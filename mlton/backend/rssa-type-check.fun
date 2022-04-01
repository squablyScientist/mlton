(* Copyright (C) 2009,2016-2017,2019-2021 Matthew Fluet.
 * Copyright (C) 1999-2008 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

functor RssaTypeCheck (S: RSSA_TYPE_CHECK_STRUCTS): RSSA_TYPE_CHECK =
struct

open S

structure Operand =
   struct
      open Operand

      val rec isLocation =
         fn Cast (z, _) => isLocation z
          | Offset _ => true
          | Runtime _ => true
          | SequenceOffset _ => true
          | _ => false
   end

local
   exception Violation
in
   fun wrapOper (oper: 'a -> unit) = fn (arg: 'a) =>
      (oper arg; true) handle Violation => false
   fun forcePoint (addHandler', isTop, lowerBoundPoint) = fn (e, p) =>
      let
         val () =
            addHandler'
            (e, fn v =>
             if isTop v then raise Violation else ())
      in
         lowerBoundPoint (e, p)
      end
end

fun checkScopes (program as Program.T {functions, main, statics, ...}): unit =
   let
      datatype status =
         Defined
       | Global
       | InScope
       | Undefined
      fun make (layout, plist) =
         let
            val {get, set, ...} =
               Property.getSet (plist, Property.initConst Undefined)
            fun bind (x, isGlobal) =
               case get x of
                  Global => ()
                | Undefined =>
                     set (x, if isGlobal then Global else InScope)
                | _ => Error.bug ("Rssa.checkScopes: duplicate definition of "
                                  ^ (Layout.toString (layout x)))
            fun reference x =
               case get x of
                  Global => ()
                | InScope => ()
                | _ => Error.bug (concat
                                  ["Rssa.checkScopes: reference to ",
                                   Layout.toString (layout x),
                                   " not in scope"])
            fun unbind x =
               case get x of
                  Global => ()
                | _ => set (x, Defined)
         in (bind, reference, unbind)
         end
      val (bindVar, getVar, unbindVar) = make (Var.layout, Var.plist)
      val bindVar =
         Trace.trace2
         ("Rssa.bindVar", Var.layout, Bool.layout, Unit.layout)
         bindVar
      val getVar =
         Trace.trace ("Rssa.getVar", Var.layout, Unit.layout) getVar
      val unbindVar =
         Trace.trace ("Rssa.unbindVar", Var.layout, Unit.layout) unbindVar
      val (bindFunc, _, _) = make (Func.layout, Func.plist)
      val bindFunc = fn f => bindFunc (f, false)
      val (bindLabel, getLabel, unbindLabel) =
         make (Label.layout, Label.plist)
      val bindLabel = fn l => bindLabel (l, false)
      fun loopStmt (s: Statement.t, isMain: bool): unit =
         (Statement.foreachUse (s, getVar)
          ; Statement.foreachDef (s, fn (x, _) =>
                                  bindVar (x, isMain)))
      fun loopFunc (f: Function.t, isMain: bool): unit =
         let
            val bindVar = fn x => bindVar (x, isMain)
            val {args, blocks, ...} = Function.dest f
            val _ = Vector.foreach (args, bindVar o #1)
            val _ = Vector.foreach (blocks, bindLabel o Block.label)
            val _ =
               Vector.foreach
               (blocks, fn Block.T {transfer, ...} =>
                Transfer.foreachLabel (transfer, getLabel))
            (* Descend the dominator tree, verifying that variable
             * definitions dominate variable uses.
             *)
            val _ =
               Tree.traverse
               (Function.dominatorTree f,
                fn Block.T {args, statements, transfer, ...} =>
                let
                   val _ = Vector.foreach (args, bindVar o #1)
                   val _ =
                      Vector.foreach
                      (statements, fn s => loopStmt (s, isMain))
                   val _ = Transfer.foreachUse (transfer, getVar)
                in
                   fn () =>
                   if isMain
                      then ()
                   else
                      let
                         val _ =
                            Vector.foreach
                            (statements, fn s =>
                             Statement.foreachDef (s, unbindVar o #1))
                         val _ = Vector.foreach (args, unbindVar o #1)
                      in
                         ()
                      end
                end)
            val _ = Vector.foreach (blocks, unbindLabel o Block.label)
            val _ = Vector.foreach (args, unbindVar o #1)
         in
            ()
         end
      val _ = Vector.foreach (statics, fn {dst, obj} =>
                              loopStmt (Statement.Object {dst = dst, obj = obj}, true))
      val _ = List.foreach (functions, bindFunc o Function.name)
      val _ = loopFunc (main, true)
      val _ = List.foreach (functions, fn f => loopFunc (f, false))
      val _ = Program.clear program
   in ()
   end

val checkScopes = Control.trace (Control.Detail, "checkScopes") checkScopes

fun typeCheck (p as Program.T {functions, main, objectTypes, profileInfo, statics, ...}) =
   let
      val _ =
         Vector.foreach
         (objectTypes, fn ty =>
          Err.check ("objectType",
                     fn () => ObjectType.isOk ty,
                     fn () => ObjectType.layout ty))
      fun tyconTy (opt: ObjptrTycon.t): ObjectType.t =
         Vector.sub (objectTypes, ObjptrTycon.index opt)
      val () = checkScopes p
      val checkFrameSourceSeqIndex =
         case profileInfo of
            NONE => (fn _ => ())
          | SOME {sourceMaps, getFrameSourceSeqIndex} =>
            let
               val _ =
                  Err.check
                  ("sourceMaps",
                   fn () => SourceMaps.check sourceMaps,
                   fn () => SourceMaps.layout sourceMaps)
            in
               fn (l, k) => let
                               fun chk b =
                                  Err.check
                                  ("getFrameSourceSeqIndex",
                                   fn () => (case (b, getFrameSourceSeqIndex l) of
                                                (true, SOME ssi) =>
                                                   SourceMaps.checkSourceSeqIndex
                                                   (sourceMaps, ssi)
                                              | (false, NONE) => true
                                              | _ => false),
                                   fn () => Label.layout l)
                            in
                               case k of
                                  Kind.Cont => chk true
                                | Kind.CReturn _ => chk true
                                | Kind.Jump => chk false
                            end
            end
      val {get = labelBlock: Label.t -> Block.t,
           set = setLabelBlock, ...} =
         Property.getSetOnce (Label.plist,
                              Property.initRaise ("block", Label.layout))
      val {get = funcInfo, set = setFuncInfo, ...} =
         Property.getSetOnce (Func.plist,
                              Property.initRaise ("info", Func.layout))
      val {get = varType: Var.t -> Type.t, set = setVarType, ...} =
         Property.getSetOnce (Var.plist,
                              Property.initRaise ("type", Var.layout))
      val setVarType =
         Trace.trace2 ("Rssa.setVarType", Var.layout, Type.layout,
                       Unit.layout)
         setVarType
      fun checkOperandAux (x: Operand.t, isLHS): unit =
          let
             datatype z = datatype Operand.t
             fun ok () =
                case x of
                   Cast (z, ty) =>
                      (checkOperandAux (z, isLHS)
                       ; Type.castIsOk {from = Operand.ty z,
                                        to = ty,
                                        tyconTy = tyconTy})
                 | Const _ => true
                 | GCState => true
                 | Offset {base, offset, ty} =>
                      (checkOperandAux (base, false)
                       ; Type.offsetIsOk {base = Operand.ty base,
                                          mustBeMutable = isLHS,
                                          offset = offset,
                                          tyconTy = tyconTy,
                                          result = ty})
                 | ObjptrTycon _ => true
                 | Runtime _ => true
                 | SequenceOffset {base, index, offset, scale, ty} =>
                      (checkOperandAux (base, false)
                       ; checkOperandAux (index, false)
                       ; Type.sequenceOffsetIsOk {base = Operand.ty base,
                                                  index = Operand.ty index,
                                                  mustBeMutable = isLHS,
                                                  offset = offset,
                                                  tyconTy = tyconTy,
                                                  result = ty,
                                                  scale = scale})
                 | Var {ty, var} => Type.isSubtype (varType var, ty)
          in
             Err.check ("operand", ok, fn () => Operand.layout x)
          end
      val checkOperandAux =
         Trace.trace2 ("Rssa.checkOperandAux",
                       Operand.layout, Bool.layout, Unit.layout)
         checkOperandAux
      fun checkLhsOperand z = checkOperandAux (z, true)
      fun checkOperand z = checkOperandAux (z, false)
      fun checkOperands v = Vector.foreach (v, checkOperand)
      fun check' (x, name, isOk, layout) =
         Err.check (name, fn () => isOk x, fn () => layout x)
      val handlersImplemented = ref false
      val labelKind = Block.kind o labelBlock
      fun statementOk (s: Statement.t): bool =
         let
            datatype z = datatype Statement.t
         in
            case s of
               Bind {src, dst = (_, dstTy), ...} =>
                  (checkOperand src
                   ; Type.isSubtype (Operand.ty src, dstTy))
             | Move {dst, src} =>
                  (checkLhsOperand dst
                   ; checkOperand src
                   ; (Type.isSubtype (Operand.ty src, Operand.ty dst)
                      andalso Operand.isLocation dst))
             | Object {dst = (_, dstTy), obj} =>
                  (Object.isOk (obj, {checkUse = checkOperand,
                                      tyconTy = tyconTy})
                   andalso Type.isSubtype (Object.ty obj, dstTy))
             | PrimApp {args, dst, prim} =>
                  (Vector.foreach (args, checkOperand)
                   ; (Type.checkPrimApp
                      {args = Vector.map (args, Operand.ty),
                       prim = prim,
                       result = Option.map (dst, #2)}))
             | Profile _ => true
             | SetExnStackLocal => (handlersImplemented := true; true)
             | SetExnStackSlot => (handlersImplemented := true; true)
             | SetHandler l => (handlersImplemented := true; false)
             | SetSlotExnStack => (handlersImplemented := true; true)
         end
      val statementOk =
         Trace.trace ("Rssa.statementOk",
                      Statement.layout,
                      Bool.layout)
                     statementOk
      fun gotoOk {args: Type.t vector,
                  dst: Label.t}: bool =
         let
            val Block.T {args = formals, kind, ...} = labelBlock dst
         in
            Vector.equals (args, formals, fn (t, (_, t')) =>
                           Type.isSubtype (t, t'))
            andalso (case kind of
                        Kind.Jump => true
                      | _ => false)
         end
      fun labelIsNullaryJump l = gotoOk {dst = l, args = Vector.new0 ()}

      (* Makes sure a tail call lines up type wise *)
      fun tailIsOk (idx: int, 
                    calleeRetsTys: Type.t vector vector,
                    callerRetsTys: Type.t vector vector): bool =
         (Vector.size callerRetsTys) < idx
         andalso
         let 
            val callerRetTys = Vector.sub (callerRetsTys, idx)
         in
            Vector.forall (calleeRetsTys,
                           fn calleeRetTys =>
                              Vector.equals 
                              (calleeRetTys, callerRetTys, Type.isSubtype))
         end

      fun nonTailIsOk (formals: (Var.t * Type.t) vector,
                       returnsTys: Type.t vector vector): bool =
          Vector.forall 
          (returnsTys,
           fn ts => 
              Vector.equals (formals, ts, fn ((_, t), t') =>
                                             Type.isSubtype (t', t)))

      (* Dispatches to either `nonTailIsOk` or `tailIsOk` *)
      (* `r`:           The return datatype that describes either which of the
       *                caller's return points to use, or what label to jump to 
       *                upon continuation.
       * calleeRetsTys: The types that are to be returned to each of the return
       *                points of the callee 
       * callerRetsTys: The types returned to each of the return points of the
       *                function making this call.
       *)
      fun retIsOk (r : Return.t, 
                   calleeRetsTys: Type.t vector vector,
                   callerRetsTys: Type.t vector vector): bool =
         case r of
            Return.Tail i => tailIsOk (i, calleeRetsTys, callerRetsTys)
          | Return.NonTail l => 
               let 
                  (* cArgs: formals expected by `l` *)
                  (* cKind: the `Kind` of block that `l` is *)
                  val Block.T {args = cArgs, kind = cKind, ...} = labelBlock l
               in
                  (* Do the types coming out of the callee match the argument
                   * types of the continuation retpt? *)
                  nonTailIsOk (cArgs, calleeRetsTys)
                  andalso
                  (* Is the block at `l` a `Cont` `Kind`? *)
                  (case cKind of
                     Kind.Cont => true
                   | _ => false)
               end
      fun callIsOk {args, func, 
                    returnPts: Return.t vector, 
                    returnsTys: Type.t vector vector} =
         let
            val {args = formals,
                 returns = calleeRetsTys, ...} =
               Function.dest (funcInfo func)
         in
            (* Make sure the passed in args are the correct types *)
            Vector.equals (args, formals, fn (z, (_, t)) =>
                           Type.isSubtype (Operand.ty z, t))
            andalso
            
            (* Make sure the return points have the correct types *)
            Vector.forall (returnPts, 
                           fn r => retIsOk (r, returnsTys, calleeRetsTys))
         end

      fun checkFunction f =
         let
            val {args, blocks, returns = returnsTys, start, ...} = Function.dest f
            val _ = Vector.foreach (args, setVarType)
            val _ =
               Vector.foreach
               (blocks, fn b as Block.T {args, kind, label, statements, ...} =>
                (setLabelBlock (label, b)
                 ; checkFrameSourceSeqIndex (label, kind)
                 ; Vector.foreach (args, setVarType)
                 ; Vector.foreach (statements, fn s =>
                                   Statement.foreachDef
                                   (s, setVarType))))
            val _ = labelIsNullaryJump start
            fun transferOk (t: Transfer.t): bool =
               let
                  datatype z = datatype Transfer.t
               in
                  case t of
                     CCall {args, func, return} =>
                        let
                           val _ = checkOperands args
                        in
                           CFunction.isOk (func, {isUnit = Type.isUnit})
                           andalso
                           Vector.equals (args, CFunction.args func,
                                          fn (z, t) =>
                                          Type.isSubtype
                                          (Operand.ty z, t))
                           andalso
                           case return of
                              NONE => true
                            | SOME l =>
                                 case labelKind l of
                                    Kind.CReturn {func = f} =>
                                       CFunction.equals (func, f)
                                  | _ => false
                        end
                   | Call {args, func, returns} =>
                        let
                           val _ = checkOperands args
                        in
                           callIsOk {args = args,
                                     func = func,
                                     returnPts = returns,
                                     returnsTys = returnsTys}
                        end
                   | Goto {args, dst} =>
                        (checkOperands args
                         ; gotoOk {args = Vector.map (args, Operand.ty),
                                   dst = dst})
                   | Return {retpt, args} =>
                        (checkOperands args; 
                         (Vector.size returnsTys) < retpt
                         andalso
                         let
                            (* The types to be returned out of the `retpt`th
                             * return point
                             *)
                            val ts = Vector.sub (returnsTys, retpt)
                         in
                            Vector.equals 
                            (args, ts, 
                             fn (arg, t) =>
                                 Type.isSubtype (Operand.ty arg, t))
                         end)

                   | Switch s =>
                        Switch.isOk (s, {checkUse = checkOperand,
                                         labelIsOk = labelIsNullaryJump})
               end
            val transferOk =
               Trace.trace ("Rssa.transferOk",
                            Transfer.layout,
                            Bool.layout)
               transferOk
            fun blockOk (Block.T {args, kind, statements, transfer, ...})
               : bool =
               let
                  fun kindOk (k: Kind.t): bool =
                     let
                        datatype z = datatype Kind.t
                     in
                        case k of
                           Cont => true
                         | CReturn {func} =>
                              let
                                 val return = CFunction.return func
                              in
                                 0 = Vector.length args
                                 orelse
                                 (1 = Vector.length args
                                  andalso
                                  let
                                     val expects =
                                        #2 (Vector.first args)
                                  in
                                     Type.isSubtype (return, expects)
                                     andalso
                                     CType.equals (Type.toCType return,
                                                   Type.toCType expects)
                                  end)
                              end
                         | Jump => true
                     end
                  val _ = check' (kind, "kind", kindOk, Kind.layout)
                  val _ =
                     Vector.foreach
                     (statements, fn s =>
                      check' (s, "statement", statementOk,
                              Statement.layout))
                  val _ = check' (transfer, "transfer", transferOk,
                                  Transfer.layout)
               in
                  true
               end
            val blockOk =
               Trace.trace ("Rssa.blockOk",
                            Block.layout,
                            Bool.layout)
                           blockOk

            val _ =
               Vector.foreach
               (blocks, fn b =>
                check' (b, "block", blockOk, Block.layout))
         in
            ()
         end
      val _ =
         Vector.foreach
         (statics, fn stmt as {dst, ...} =>
          (setVarType dst
           ; check' (Statement.Object stmt, "static", statementOk, Statement.layout)))
      val _ =
         List.foreach
         (functions, fn f => setFuncInfo (Function.name f, f))
      val _ = checkFunction main
      val _ = List.foreach (functions, checkFunction)
      val _ =
         check'
         (main, "main function",
          fn f =>
          let
             val {args, ...} = Function.dest f
          in
             Vector.isEmpty args
          end,
          Function.layout)
      val _ = Program.clear p
   in
      ()
   end handle Err.E e => (Layout.outputl (Err.layout e, Out.error)
                          ; Error.bug "Rssa.typeCheck")
end
