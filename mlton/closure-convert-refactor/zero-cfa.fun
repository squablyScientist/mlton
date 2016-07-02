(* Copyright (C) 2016 Matthew Fluet.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

(* A naive 0CFA control-flow analysis, using a powerset lattice of
 * abstract values.
 *)
functor ZeroCFA (S: CFA_STRUCTS): CFA =
struct

open S
open Sxml.Atoms

structure Config = struct type t = {reachabilityExt: bool} end

type t = {program: Sxml.Program.t} ->
         {cfa: {arg: Sxml.Var.t,
                argTy: Sxml.Type.t,
                func: Sxml.Var.t,
                res: Sxml.Var.t,
                resTy: Sxml.Type.t} ->
               Sxml.Lambda.t list,
          destroy: unit -> unit}

structure Proxy :>
   sig
      type t
      val all: unit -> t list
      val equals: t * t -> bool
      val hash: t -> Word.t
      val layout: t -> Layout.t
      val new: unit -> t
      val plist: t -> PropertyList.t
   end =
   struct
      type t = Sxml.Var.t
      val all = ref []
      val equals = Sxml.Var.equals
      val hash = Sxml.Var.hash
      val layout = Sxml.Var.layout
      val new = fn () => let val p = Sxml.Var.newString "p"
                         in List.push (all, p); p
                         end
      val plist = Sxml.Var.plist
      val all = fn () => !all
   end
structure AbstractValue =
   struct
      datatype t =
         Array of Proxy.t
       | Base of Sxml.Type.t
       | ConApp of {con: Sxml.Con.t, arg: Sxml.Var.t option}
       | Lambda of Sxml.Lambda.t
       | Ref of Proxy.t
       | Tuple of Sxml.Var.t vector
       | Vector of Proxy.t
       | Weak of Sxml.Var.t

      fun equals (e, e') =
         case (e, e') of
            (Array p, Array p') => Proxy.equals (p, p')
          | (Base ty, Base ty') => Sxml.Type.equals (ty, ty')
          | (ConApp {con = con, arg = arg}, ConApp {con = con', arg = arg'}) =>
               Sxml.Con.equals (con, con') andalso
               Option.equals (arg, arg', Sxml.Var.equals)
          | (Lambda lam, Lambda lam') => Sxml.Lambda.equals (lam, lam')
          | (Ref p, Ref p') => Proxy.equals (p, p')
          | (Tuple xs, Tuple xs') => Vector.equals (xs, xs', Sxml.Var.equals)
          | (Vector p, Vector p') => Proxy.equals (p, p')
          | (Weak x, Weak x') => Sxml.Var.equals (x, x')
          | _ => false

      fun layout e =
         let
            open Layout
         in
            case e of
               Array p => seq [str "Array ", Proxy.layout p]
             | Base ty => seq [str "Base ", Sxml.Type.layout ty]
             | ConApp {con, arg} => seq [Sxml.Con.layout con,
                                         case arg of
                                            NONE => empty
                                          | SOME arg => seq [str " ",
                                                             Sxml.Var.layout arg]]
             | Lambda lam => seq [str "fn ", Sxml.Var.layout (Sxml.Lambda.arg lam)]
             | Ref p => seq [str "Ref ", Proxy.layout p]
             | Tuple xs => tuple (Vector.toListMap (xs, Sxml.Var.layout))
             | Vector p => seq [str "Vector ", Proxy.layout p]
             | Weak x => seq [str "Weak ", Sxml.Var.layout x]
         end

      fun hash _ = 0wx0

      val unit = Tuple (Vector.new0 ())
      val truee = ConApp {con = Sxml.Con.truee, arg = NONE}
      val falsee = ConApp {con = Sxml.Con.falsee, arg = NONE}
   end
structure AbsVal = AbstractValue

structure AbstractValueSet = PowerSetLattice(structure Element = AbstractValue)
structure AbstractValueSet =
   struct
      open AbstractValueSet
      val unit = singleton AbstractValue.unit
      val bool = fromList [AbstractValue.truee, AbstractValue.falsee]
   end
structure AbsValSet = AbstractValueSet


fun cfa {config = {reachabilityExt}: Config.t} : t =
   fn {program: Sxml.Program.t} =>
   let
      val Sxml.Program.T {body, ...} = program

      val {get = varInfo: Sxml.Var.t -> AbsValSet.t,
           rem = remVarInfo} =
         Property.get
         (Sxml.Var.plist,
          Property.initFun (fn _ => AbsValSet.empty ()))
      val varExpInfo = varInfo o Sxml.VarExp.var

      val {get = proxyInfo: Proxy.t -> AbsValSet.t, ...} =
         Property.get
         (Proxy.plist,
          Property.initFun (fn _ => AbsValSet.empty ()))

      val {get = lambdaInfo: Sxml.Lambda.t -> bool,
           set = setLambdaInfo, destroy = destroyLambdaInfo} =
         Property.destGetSet
         (Sxml.Lambda.plist,
          Property.initFun (fn _ => false))

      val exnProxy = Proxy.new ()

      fun fromType ty =
         case (Sxml.Type.equals (ty, Sxml.Type.bool),
               Sxml.Type.equals (ty, Sxml.Type.unit),
               Sxml.Type.deVectorOpt ty) of
            (true, _, _) => AbsValSet.bool
          | (_, true, _) => AbsValSet.unit
          | (_, _, SOME ty) =>
               let
                  val pv = Proxy.new ()
                  val _ = AbsValSet.<= (fromType ty, proxyInfo pv)
               in
                  AbsValSet.singleton (AbsVal.Vector pv)
               end
          | _ => AbsValSet.singleton (AbsVal.Base ty)

      fun loopExp (exp: Sxml.Exp.t): AbsValSet.t =
         let
            val {decs, result} = Sxml.Exp.dest exp
            val () = List.foreach (decs, loopDec)
         in
            varExpInfo result
         end
      and loopExp' (exp: Sxml.Exp.t): unit = ignore (loopExp exp)
      and loopDec (dec: Sxml.Dec.t): unit =
         (case dec of
             Sxml.Dec.Fun {decs, ...} =>
                Vector.foreach
                (decs, fn {var, lambda, ...} =>
                 AbsValSet.<< (loopLambda lambda, varInfo var))
           | Sxml.Dec.MonoVal bind => loopBind bind
           | _ => Error.bug "ZeroCFA.loopDec: strange dec")
      and loopBind {var, ty, exp, ...}: unit =
         AbsValSet.<= (loopPrimExp (exp, ty), varInfo var)
      and loopPrimExp (exp: Sxml.PrimExp.t, ty: Sxml.Type.t): AbsValSet.t =
         (case exp of
             Sxml.PrimExp.App {func, arg} =>
                let
                   val res = AbsValSet.empty ()
                   val _ = AbsValSet.addHandler
                           (varExpInfo func, fn v =>
                            case v of
                               AbsVal.Lambda lam =>
                                  let
                                     val {arg = formal, body, ...} = Sxml.Lambda.dest lam
                                  in
                                     AbsValSet.<= (varExpInfo arg, varInfo formal);
                                     if reachabilityExt andalso not (lambdaInfo lam)
                                        then (setLambdaInfo (lam, true); loopExp' body)
                                        else ();
                                     AbsValSet.<= (varExpInfo (Sxml.Exp.result body), res)
                                  end
                             | _ => Error.bug "ZeroCFA.loopPrimExp: non-lambda")
                in
                   res
                end
           | Sxml.PrimExp.Case {test, cases, default} =>
                let
                   val res = AbsValSet.empty ()
                   val _ =
                      case cases of
                         Sxml.Cases.Con cases =>
                            let
                               val cases =
                                  Vector.map
                                  (cases, fn (Sxml.Pat.T {con, arg, ...}, _) =>
                                   {con = con, arg = arg})
                            in
                               AbsValSet.addHandler
                               (varExpInfo test, fn v =>
                                case v of
                                   AbsVal.ConApp {con, arg} =>
                                      (case Vector.peek (cases, fn {con = con', ...} =>
                                                         Sxml.Con.equals (con, con')) of
                                          SOME {arg = arg', ...} =>
                                             (case (arg, arg') of
                                                 (NONE, NONE) => ()
                                               | (SOME arg, SOME (arg', _)) =>
                                                    AbsValSet.<= (varInfo arg, varInfo arg')
                                               | _ => Error.bug "ZeroCFA.loopPrimExp: Case")
                                        | NONE => ())
                                 | _ => Error.bug "ZeroCFA.loopPrimExp: non-con")
                            end
                       | Sxml.Cases.Word _ => ()
                   val _ =
                      Sxml.Cases.foreach
                      (cases, fn exp =>
                       AbsValSet.<= (loopExp exp, res))
                   val _ =
                      Option.foreach
                      (default, fn (exp, _) =>
                       AbsValSet.<= (loopExp exp, res))
                in
                   res
                end
           | Sxml.PrimExp.ConApp {con, arg, ...} =>
                AbsValSet.singleton (AbsVal.ConApp {con = con, arg = Option.map (arg, Sxml.VarExp.var)})
           | Sxml.PrimExp.Const c =>
                fromType (Sxml.Type.ofConst c)
           | Sxml.PrimExp.Handle {try, catch = (var, _), handler} =>
                let
                   val res = AbsValSet.empty ()
                   val _ = AbsValSet.<= (loopExp try, res)
                   val _ = AbsValSet.<= (proxyInfo exnProxy, varInfo var)
                   val _ = AbsValSet.<= (loopExp handler, res)
                in
                   res
                end
           | Sxml.PrimExp.Lambda lam =>
                AbsValSet.singleton (loopLambda lam)
           | Sxml.PrimExp.PrimApp {prim, args, ...} =>
                let
                   val res = AbsValSet.empty ()
                   fun arg' i = Sxml.VarExp.var (Vector.sub (args, i))
                   val arg = varInfo o arg'
                   fun bug (k, v) =
                      (Error.bug o String.concat)
                      ["ZeroCFA.loopPrimExp: non-", k,
                       " (got ", Layout.toString (AbsVal.layout v),
                       " for ",Prim.Name.toString (Prim.name prim), ")"]
                   datatype z = datatype Prim.Name.t
                   val _ =
                      case Prim.name prim of
                         Array_array =>
                            let
                               val pa = Proxy.new ()
                            in
                               AbsValSet.<< (AbsVal.Array pa, res)
                            end
                       | Array_array0Const =>
                            let
                               val pa = Proxy.new ()
                            in
                               AbsValSet.<< (AbsVal.Array pa, res)
                            end
                       | Array_sub =>
                            AbsValSet.addHandler
                            (arg 0, fn v =>
                             case v of
                                AbsVal.Array pa => AbsValSet.<= (proxyInfo pa, res)
                              | _ => bug ("Array", v))
                       | Array_update =>
                            (AbsValSet.addHandler
                             (arg 0, fn v =>
                              case v of
                                 AbsVal.Array pa => AbsValSet.<= (arg 2, proxyInfo pa)
                               | _ => bug ("Array", v));
                             AbsValSet.<= (AbsValSet.unit, res))
                       | Array_toVector =>
                            let
                               val pv = Proxy.new ()
                            in
                               AbsValSet.addHandler
                               (arg 0, fn v =>
                                case v of
                                   AbsVal.Array pa => AbsValSet.<= (proxyInfo pa, proxyInfo pv)
                                 | _ => bug ("Array", v));
                               AbsValSet.<< (AbsVal.Vector pv, res)
                            end
                       | Ref_assign =>
                            (AbsValSet.addHandler
                             (arg 0, fn v =>
                              case v of
                                 AbsVal.Ref pr => AbsValSet.<= (arg 1, proxyInfo pr)
                               | _ => bug ("Ref", v));
                             AbsValSet.<= (AbsValSet.unit, res))
                       | Ref_deref =>
                            AbsValSet.addHandler
                            (arg 0, fn v =>
                             case v of
                                AbsVal.Ref pr => AbsValSet.<= (proxyInfo pr, res)
                              | _ => bug ("Ref", v))
                       | Ref_ref =>
                            let
                               val pr = Proxy.new ()
                            in
                               AbsValSet.<= (arg 0, proxyInfo pr);
                               AbsValSet.<< (AbsVal.Ref pr, res)
                            end
                       | Weak_new =>
                            AbsValSet.<< (AbsVal.Weak (arg' 0), res)
                       | Weak_get =>
                            AbsValSet.addHandler
                            (arg 0, fn v =>
                             case v of
                                AbsVal.Weak x => AbsValSet.<= (varInfo x, res)
                              | _ => bug ("Weak", v))
                       | Vector_sub =>
                            AbsValSet.addHandler
                            (arg 0, fn v =>
                             case v of
                                AbsVal.Vector pv => AbsValSet.<= (proxyInfo pv, res)
                              | _ => bug ("Vector", v))
                       | _ =>
                            AbsValSet.<= (fromType ty, res)
                in
                   res
                end
           | Sxml.PrimExp.Profile _ =>
                AbsValSet.unit
           | Sxml.PrimExp.Raise {exn, ...} =>
                let
                   val _ = AbsValSet.<= (varExpInfo exn, proxyInfo exnProxy)
                in
                   AbsValSet.empty ()
                end
           | Sxml.PrimExp.Select {tuple, offset} =>
                let
                   val res = AbsValSet.empty ()
                   val _ = AbsValSet.addHandler
                           (varExpInfo tuple, fn v =>
                            case v of
                               AbsVal.Tuple xs =>
                                  AbsValSet.<= (varInfo (Vector.sub (xs, offset)), res)
                             | _ => Error.bug "ZeroCFA.loopPrimExp: non-tuple")
                in
                   res
                end
           | Sxml.PrimExp.Tuple xs =>
                AbsValSet.singleton (AbsVal.Tuple (Vector.map (xs, Sxml.VarExp.var)))
           | Sxml.PrimExp.Var x =>
                varExpInfo x)
      and loopLambda (lambda: Sxml.Lambda.t): AbsVal.t =
         let
            val {body, ...} = Sxml.Lambda.dest lambda
            val _ =
               if reachabilityExt
                  then setLambdaInfo (lambda, false)
                  else loopExp' body
         in
            AbsVal.Lambda lambda
         end

      val _ = loopExp' body

      val _ =
         Control.diagnostics
         (fn display =>
          Sxml.Exp.foreachBoundVar
          (body, fn (x, _, _) =>
           (display o Layout.seq)
           [Sxml.Var.layout x, Layout.str ": ", AbsValSet.layout (varInfo x)]))

      val cfa : {arg: Sxml.Var.t,
                 argTy: Sxml.Type.t,
                 func: Sxml.Var.t,
                 res: Sxml.Var.t,
                 resTy: Sxml.Type.t} ->
                Sxml.Lambda.t list =
         fn {func, ...} =>
         List.keepAllMap
         (AbsValSet.getElements (varInfo func), fn v =>
          case v of
             AbsVal.Lambda lam => SOME lam
           | _ => Error.bug "ZeroCFA.cfa: non-lambda")

      val destroy = fn () =>
         (Sxml.Exp.foreachBoundVar
          (body, fn (var, _, _) =>
           remVarInfo var);
          destroyLambdaInfo ())
   in
      {cfa = cfa, destroy = destroy}
   end
val cfa = fn config =>
   Control.trace (Control.Detail, "ZeroCFA")
   (cfa config)

fun scan _ charRdr strm0 =
   let
      val (s, strm1) =
         StringCvt.splitl Char.isAlphaNum charRdr strm0
   in
      if String.equals ("0cfa", s)
         then (case charRdr strm1 of
                  SOME (#"(", strm2) =>
                     (case Pervasive.Bool.scan charRdr strm2 of
                         SOME (reachabilityExt, strm3) =>
                            (case charRdr strm3 of
                                SOME (#")", strm4) =>
                                   SOME (cfa {config = {reachabilityExt = reachabilityExt}}, strm4)
                              | _ => NONE)
                       | _ => NONE)
                | _ => NONE)
         else NONE
   end

end
