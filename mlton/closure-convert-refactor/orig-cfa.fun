(* Copyright (C) 2016 Matthew Fluet.
 * Copyright (C) 1999-2005, 2008 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

functor OrigCFA (S: CFA_STRUCTS): CFA =
struct

open S

structure Config = struct type t = unit end

type t = {program: Sxml.Program.t} ->
         {cfa: {arg: Sxml.Var.t,
                argTy: Sxml.Type.t,
                func: Sxml.Var.t,
                res: Sxml.Var.t,
                resTy: Sxml.Type.t} ->
               Sxml.Lambda.t list,
          destroy: unit -> unit}

local open Sxml
in
   structure Sexp = Exp
   structure SprimExp = PrimExp
   structure SvarExp = VarExp
   structure Stype = Type
   open Atoms
end

structure Value = AbstractValue (structure Sxml = Sxml)

structure VarInfo =
   struct
      type t = {value: Value.t}
   end

val traceLoopBind =
   Trace.trace
   ("ClosureConvert.loopBind",
    fn {exp, ty = _: Stype.t, var} =>
    Layout.record [("var", Var.layout var),
                   ("exp", SprimExp.layout exp)],
    Unit.layout)

fun cfa (_: {config: Config.t}): t =
   fn {program: Sxml.Program.t} =>
   let
      val Sxml.Program.T {datatypes, body, ...} = program

      val {get = conArg: Con.t -> Value.t option,
           set = setConArg, rem = remConArg} =
         Property.getSetOnce
         (Con.plist,
          Property.initRaise ("OrigCFA.conArg", Con.layout))
      val {get = varInfo: Var.t -> VarInfo.t,
           set = setVarInfo, rem = remVarInfo} =
         Property.getSetOnce
         (Var.plist,
          Property.initRaise ("OrigCFA.varInfo", Var.layout))
      val varInfo =
         Trace.trace
         ("OrigCFA.varInfo", Var.layout, Layout.ignore)
         varInfo
      val value = #value o varInfo
      val varExp = value o SvarExp.var
      val expValue = varExp o Sexp.result

      (* Do the flow analysis.
       * Initialize lambdaInfo and varInfo.
       *)
      val _ =
         Vector.foreach
         (datatypes, fn {cons, ...} =>
          Vector.foreach
          (cons, fn {con, arg} =>
           setConArg (con, (case arg of
                               NONE => NONE
                             | SOME t => SOME (Value.fromType t)))))
      val _ =
         let
            open Sxml
            fun newVar (x, v) =
               setVarInfo (x, {value = v})
            val newVar =
               Trace.trace2
               ("ClosureConvert.newVar",
                Var.layout, Layout.ignore, Unit.layout)
               newVar
            fun varExps xs = Vector.map (xs, varExp)
            fun loopExp (e: Exp.t): Value.t =
               let
                  val {decs, result} = Exp.dest e
                  val () = List.foreach (decs, loopDec)
               in
                  varExp result
               end
            and loopDec (d: Dec.t): unit =
               let
                  datatype z = datatype Dec.t
               in
                  case d of
                     Fun {decs, ...} =>
                        (Vector.foreach (decs, fn {var, ty, ...} =>
                                         newVar (var, Value.fromType ty))
                         ; (Vector.foreach
                            (decs, fn {var, lambda, ...} =>
                             Value.unify (value var,
                                          loopLambda lambda))))
                   | MonoVal b => loopBind b
                   | _ => Error.bug "OrigCFA.loopDec: strange dec"
               end
            and loopBind arg =
               traceLoopBind
               (fn {var, ty, exp} =>
               let
                  fun set v = newVar (var, v)
                  fun new () =
                     let val v = Value.fromType ty
                     in set v; v
                     end
                  val new' = ignore o new
                  datatype z = datatype PrimExp.t
               in
                  case exp of
                     App {func, arg} =>
                        let val arg = varExp arg
                           val result = new ()
                        in Value.addHandler
                           (varExp func, fn l =>
                            let
                               val lambda = Value.Lambda.dest l
                               val {arg = formal, body, ...} =
                                  Lambda.dest lambda
                            in Value.coerce {from = arg,
                                             to = value formal}
                               ; Value.coerce {from = expValue body,
                                               to = result}
                            end)
                        end
                   | Case {cases, default, ...} =>
                        let
                           val result = new ()
                           fun branch e =
                              Value.coerce {from = loopExp e, to = result}
                           fun handlePat (Pat.T {con, arg, ...}) =
                              case (arg,      conArg con) of
                                 (NONE,        NONE)       => ()
                               | (SOME (x, _), SOME v)     => newVar (x, v)
                               | _ => Error.bug "OrigCFA.loopBind: Case"
                           val _ = Cases.foreach' (cases, branch, handlePat)
                           val _ = Option.app (default, branch o #1)
                        in ()
                        end
                   | ConApp {con, arg, ...} =>
                        (case (arg,    conArg con) of
                            (NONE,   NONE)       => ()
                          | (SOME x, SOME v)     =>
                               Value.coerce {from = varExp x, to = v}
                          | _ => Error.bug "OrigCFA.loopBind: ConApp"
                         ; new' ())
                   | Const _ => new' ()
                   | Handle {try, catch = (x, t), handler} =>
                        let
                           val result = new ()
                        in Value.coerce {from = loopExp try, to = result}
                           ; newVar (x, Value.fromType t)
                           ; Value.coerce {from = loopExp handler, to = result}
                        end
                   | Lambda l => set (loopLambda l)
                   | PrimApp {prim, args, ...} =>
                        set (Value.primApply {prim = prim,
                                              args = varExps args,
                                              resultTy = ty})
                   | Profile _ => new' ()
                   | Raise _ => new' ()
                   | Select {tuple, offset} =>
                        set (Value.select (varExp tuple, offset))
                   | Tuple xs =>
                        if Value.typeIsFirstOrder ty
                           then new' ()
                      else set (Value.tuple (Vector.map (xs, varExp)))
                   | Var x => set (varExp x)
               end) arg
            and loopLambda (lambda: Lambda.t): Value.t =
               let
                  val {arg, argType, body, ...} = Lambda.dest lambda
                  val _ = newVar (arg, Value.fromType argType)
               in
                  Value.lambda (lambda,
                                Type.arrow (argType, Value.ty (loopExp body)))
               end
            val _ = loopExp body
         in ()
         end

      val cfa : {arg: Sxml.Var.t,
                 argTy: Sxml.Type.t,
                 func: Sxml.Var.t,
                 res: Sxml.Var.t,
                 resTy: Sxml.Type.t} ->
                Sxml.Lambda.t list =
         fn {func, ...} =>
         case Value.dest (value func) of
            Value.Lambdas l =>
               List.map
               (Value.Lambdas.toList l, Value.Lambda.dest)
          | _ => Error.bug "OrigCFA.cfa: non-lambda"

      val destroy = fn () =>
         (Value.destroy ();
          Vector.foreach
          (datatypes, fn {cons, ...} =>
           Vector.foreach
           (cons, fn {con, ...} =>
            remConArg con));
          Sexp.foreachBoundVar
          (body, fn (var, _, _) =>
           remVarInfo var))
   in
      {cfa = cfa, destroy = destroy}
   end
val cfa = fn config =>
   Control.trace (Control.Detail, "OrigCFA")
   (cfa config)

fun scan _ charRdr strm0 =
   let
      fun scanAlphaNums strm =
         SOME (StringCvt.splitl Char.isAlphaNum charRdr strm)
   in
      case scanAlphaNums strm0 of
         SOME ("ocfa", strm1) =>
            SOME (cfa {config = ()}, strm1)
       | _ => NONE
   end

end
