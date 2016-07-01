(* Copyright (C) 2016 Matthew Fluet.
 * Copyright (C) 1999-2005, 2008 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

(* The simple monomorphic-type-based defunctionalization
 * transformation: represent all lambdas of the same type as variants
 * of a common datatype.  The supplied control-flow analysis refines
 * the dispatch at call-sites (with a bug reporting default indicative
 * of an unsound cfa), but there is otherwise no specialization with
 * respect to the cfa.
 *)
functor TyTransform (S: TRANSFORM_STRUCTS): TRANSFORM =
struct

open S
open Sxml.Atoms

structure LambdaFree = LambdaFree(S)

fun transform {program: Sxml.Program.t, cfa} =
   let
      val Sxml.Program.T {datatypes, body, overflow} = program
      val overflow = valOf overflow

      val {freeVars, destroy = destroyLambdaFree, ...} =
         LambdaFree.lambdaFree {program = program}

      val arrowInfos = ref []
      val {get = arrowInfo: Sxml.Type.t -> {lambdas: Sxml.Lambda.t list ref,
                                            tycon: Tycon.t},
           destroy = destroyArrowInfo} =
         Property.destGet
         (Sxml.Type.plist,
          Property.initFun (fn ty =>
                            if Option.isSome (Sxml.Type.deArrowOpt ty)
                               then let val info = {lambdas = ref [],
                                                    tycon = Tycon.newString "lambdas"}
                                    in List.push (arrowInfos, info); info
                                    end
                               else Error.bug "TyTransform.arrowInfo: non-arrow"))

      val (convertType, destroyConvertType) =
         let
            val {get, set, destroy, ...} =
               Property.destGetSetOnce (Tycon.plist, Property.initConst NONE)

            fun nullary c v =
               if Vector.isEmpty v
                  then c
               else Error.bug "TyTransform.nullary: non-nullary tycon"

            fun unary make v =
               if 1 = Vector.length v
                  then make (Vector.sub (v, 0))
               else Error.bug "TyTransform.unary: non-unary tycon"

            val tycons =
               [(Tycon.array, unary Ssa.Type.array),
                (Tycon.cpointer, nullary Ssa.Type.cpointer),
                (Tycon.intInf, nullary Ssa.Type.intInf),
                (Tycon.reff, unary Ssa.Type.reff),
                (Tycon.thread, nullary Ssa.Type.thread),
                (Tycon.tuple, Ssa.Type.tuple),
                (Tycon.vector, unary Ssa.Type.vector),
                (Tycon.weak, unary Ssa.Type.weak)]
               @ Vector.toListMap (Tycon.reals, fn (t, s) => (t, nullary (Ssa.Type.real s)))
               @ Vector.toListMap (Tycon.words, fn (t, s) => (t, nullary (Ssa.Type.word s)))

            val _ = List.foreach (tycons, fn (tycon, f) => set (tycon, SOME f))

            val {hom = convertType, destroy = destroyConvertType} =
               Sxml.Type.makeMonoHom
               {con = fn (ty, tycon, ts) =>
                if Tycon.equals (tycon, Tycon.arrow)
                   then Ssa.Type.datatypee (#tycon (arrowInfo ty))
                   else case get tycon of
                           NONE => nullary (Ssa.Type.datatypee tycon) ts
                         | SOME f => f ts}
         in
            (convertType,
             fn () => (destroy (); destroyConvertType ()))
         end
      fun convertTypes tys = Vector.map (tys, convertType)

      val {get = varInfo : Var.t -> {oty: Sxml.Type.t, cvar: Var.t ref, cty: Ssa.Type.t},
           set = setVarInfo, rem = remVarInfo} =
         Property.getSetOnce
         (Var.plist,
          Property.initRaise ("TyTransform.varInfo", Var.layout))
      fun newVar x =
         let val x' = Var.new x
         in #cvar (varInfo x) := x' ; x'
         end
      fun newScope (xs: Var.t vector, f: Var.t vector -> 'a): 'a =
         let
            val old = Vector.map (xs, ! o #cvar o varInfo)
            val new = Vector.map (xs, newVar)
            val res = f new
            val () = Vector.foreach2 (xs, old, fn (x, x') =>
                                      #cvar (varInfo x) := x')
         in
            res
         end

      val {get = lambdaInfo: Sxml.Lambda.t -> {con: Con.t,
                                               cty: Ssa.Type.t,
                                               envVars: Var.t vector,
                                               envTy: Ssa.Type.t,
                                               func: Ssa.Func.t},
           set = setLambdaInfo, destroy = destroyLambdaInfo} =
         Property.destGetSetOnce
         (Sxml.Lambda.plist,
          Property.initRaise ("TyTransform.lambdaInfo", Sxml.Lambda.layout))


      val _ =
         Sxml.Exp.foreach
         {exp = body,
          handleExp = ignore,
          handlePrimExp = (fn (f, ty, exp) =>
                           case exp of
                              Sxml.PrimExp.Lambda lambda =>
                                 let
                                    val f = Var.originalName f
                                    val con = (Con.newString o String.concat)
                                              [String.toUpper (String.prefix (f, 1)),
                                               String.dropFirst f,
                                               "Env"]
                                    val envVars = freeVars lambda
                                    val envTy = Ssa.Type.tuple (Vector.map (envVars, #cty o varInfo))
                                    val func = Func.newString f
                                 in
                                    List.push (#lambdas (arrowInfo ty), lambda);
                                    setLambdaInfo (lambda, {con = con,
                                                            cty = convertType ty,
                                                            envVars = envVars,
                                                            envTy = envTy,
                                                            func = func})
                                 end
                            | _ => ()),
          handleBoundVar = (fn (x, _, ty) =>
                            setVarInfo (x, {oty = ty, cvar = ref x, cty = convertType ty})),
          handleVarExp = ignore}


      fun convertConArg (arg, f) =
         case arg of
            NONE => Vector.new0 ()
          | SOME arg => Vector.new1 (f arg)


      val datatypes =
         Vector.map
         (datatypes, fn {tycon, cons, ...} =>
          Ssa.Datatype.T
          {tycon = tycon,
           cons = (Vector.map
                   (cons, fn {con, arg} =>
                    {con = con,
                     args = convertConArg (arg, convertType)}))})

      val lambdaDatatypes =
         Vector.fromListMap
         (!arrowInfos, fn {lambdas, tycon} =>
          Ssa.Datatype.T
          {tycon = tycon,
           cons = (Vector.fromListMap
                   (!lambdas, fn lam =>
                    let
                       val {con, envTy, ...} = lambdaInfo lam
                    in
                       {con = con,
                        args = Vector.new1 envTy}
                    end))})


      val functions = ref []
      val raises: Ssa.Type.t vector option =
         Exn.withEscape
         (fn escape =>
          (Sxml.Exp.foreachPrimExp
           (body, fn (_, _, e) =>
            case e of
               Sxml.PrimExp.Handle {catch = (_, ty), ...} =>
                  escape (SOME (Vector.new1 (convertType ty)))
               | _ => ())
             ; NONE))
      val shrinkFunction =
         if !Control.closureConvertShrink
            then Ssa.shrinkFunction {globals = Vector.new0 ()}
            else fn f => f
      fun addFunction {args, body, isMain, mayInline, name, resTy} =
         let
            val (start, blocks) =
               Ssa.DirectExp.linearize
               (body, if isMain then Ssa.Handler.Dead else Ssa.Handler.Caller)
            val f =
               shrinkFunction
               (Ssa.Function.new {args = args,
                                  blocks = Vector.fromList blocks,
                                  mayInline = mayInline,
                                  name = name,
                                  raises = if isMain then NONE else raises,
                                  returns = SOME (Vector.new1 resTy),
                                  start = start})
            val f =
               if isMain
                  then Ssa.Function.profile (f, SourceInfo.main)
                  else f
         in
            List.push (functions, f)
         end


      fun convertBoundVar (x: Var.t, ty: Sxml.Type.t) =
         let
            val cx = newVar x
            val cty = #cty (varInfo x)
            val _ = Assert.assert("TyTransform.convertBoundVar",
                                  fn () => Ssa.Type.equals (cty, convertType ty))
         in
            (cx, cty)
         end

      fun convertVar (x: Var.t) =
         let val {cvar, cty, ...} = varInfo x
         in Ssa.DirectExp.var (!cvar, cty)
         end
      fun convertVars xs = Vector.map (xs, convertVar)
      val convertVarExp = convertVar o Sxml.VarExp.var
      fun convertVarExps xs = Vector.map (xs, convertVarExp)
      fun convertExp (exp: Sxml.Exp.t): Ssa.DirectExp.t =
         let
            val {decs, result} = Sxml.Exp.dest exp
         in
            Ssa.DirectExp.lett {decs = List.concatMap (decs, convertDec),
                                body = convertVarExp result}
         end
      and convertDec (dec: Sxml.Dec.t): {var: Var.t, exp: Ssa.DirectExp.t} list =
         (case dec of
             Sxml.Dec.MonoVal {var, ty, exp} =>
                let
                   val (cvar, cty) = convertBoundVar (var, ty)
                in
                   [{var = cvar,
                     exp = convertPrimExp {var = var, oty = ty, cty = cty, exp = exp}}]
                end
           | Sxml.Dec.Fun {decs, ...} =>
                Vector.toListMap
                (Vector.map (decs,
                             fn {var, ty, lambda} =>
                             {cvar = #1 (convertBoundVar (var, ty)),
                              lambda = lambda}),
                 fn {cvar, lambda} =>
                 {var = cvar,
                  exp = convertLambda {lambda = lambda, recs = decs}})
           | _ => Error.bug "TyTransform.convertDec: strange dec")
      and convertPrimExp {var: Var.t, oty: Sxml.Type.t, cty: Ssa.Type.t, exp: Sxml.PrimExp.t}: Ssa.DirectExp.t =
         (case exp of
             Sxml.PrimExp.App {func, arg} =>
                let
                   val func = Sxml.VarExp.var func
                   val arg = Sxml.VarExp.var arg
                   val argTy = #oty (varInfo arg)
                   val res = var
                   val resTy = oty
                   val funcTy = Sxml.Type.arrow (argTy, resTy)
                   val lambdas =
                      cfa {arg = arg,
                           argTy = argTy,
                           func = func,
                           res = res,
                           resTy = resTy}
                   val msg = String.concat
                             ["unsound cfa:: ",
                              (Layout.toString o Sxml.Dec.layout o Sxml.Dec.MonoVal)
                              {var = var, ty = resTy, exp = exp}]
                in
                   Ssa.DirectExp.casee
                   {test = convertVar func,
                    cases = (Ssa.DirectExp.Con
                             (Vector.fromListMap
                              (lambdas, fn lambda =>
                               let
                                  val {con, envTy, func, ...} = lambdaInfo lambda
                                  val env = (Var.newString "env", envTy)
                               in
                                  {con = con,
                                   args = Vector.new1 env,
                                   body = (Ssa.DirectExp.call
                                           {func = func,
                                            args = Vector.new2 (Ssa.DirectExp.var env,
                                                                convertVar arg),
                                            ty = cty})}
                               end))),
                    default = if List.length lambdas < List.length (! (#lambdas (arrowInfo funcTy)))
                                 then SOME (Ssa.DirectExp.bug msg)
                                 else NONE,
                    ty = cty}
                end
           | Sxml.PrimExp.Case {test, cases, default} =>
                Ssa.DirectExp.casee
                {test = convertVarExp test,
                 cases = (case cases of
                             Sxml.Cases.Con cases =>
                                Ssa.DirectExp.Con
                                (Vector.map
                                 (cases, fn (Sxml.Pat.T {con, arg, ...}, e) =>
                                  {con = con,
                                   args = convertConArg (arg, convertBoundVar),
                                   body = convertExp e}))
                           | Sxml.Cases.Word (ws, cases) =>
                                Ssa.DirectExp.Word
                                (ws,
                                 Vector.map
                                 (cases, fn (w, e) =>
                                  (w, convertExp e)))),
                 default = Option.map (default, convertExp o #1),
                 ty = cty}
           | Sxml.PrimExp.ConApp {con, arg, ...} =>
                Ssa.DirectExp.conApp
                {con = con,
                 args = convertConArg (arg, convertVarExp),
                 ty = cty}
           | Sxml.PrimExp.Const c =>
                Ssa.DirectExp.const c
           | Sxml.PrimExp.Handle {try, catch, handler} =>
                Ssa.DirectExp.handlee
                {try = convertExp try,
                 catch = convertBoundVar catch,
                 handler = convertExp handler,
                 ty = cty}
           | Sxml.PrimExp.Lambda lambda =>
                convertLambda {lambda = lambda, recs = Vector.new0 ()}
           | Sxml.PrimExp.PrimApp {prim, targs, args} =>
                let
                   val prim = Prim.map (prim, convertType)
                   val targs = convertTypes targs
                   val args = convertVarExps args
                in
                   if Prim.mayOverflow prim
                      then Ssa.DirectExp.arith
                           {prim = prim,
                            args = args,
                            overflow = Ssa.DirectExp.raisee (convertVar overflow),
                            ty = cty}
                      else Ssa.DirectExp.primApp
                           {prim = prim,
                            targs = targs,
                            args = args,
                            ty = cty}
                end
           | Sxml.PrimExp.Profile pe =>
                Ssa.DirectExp.profile pe
           | Sxml.PrimExp.Raise {exn, ...} =>
                Ssa.DirectExp.raisee (convertVarExp exn)
           | Sxml.PrimExp.Select {offset, tuple} =>
                Ssa.DirectExp.select
                {offset = offset,
                 tuple = convertVarExp tuple,
                 ty = cty}
           | Sxml.PrimExp.Tuple xs =>
                Ssa.DirectExp.tuple
                {exps = convertVarExps xs,
                 ty = cty}
           | Sxml.PrimExp.Var x =>
                convertVarExp x)
      and convertLambda {lambda, recs} =
         let
            fun mkClos {lambda, env} =
               let
                  val {con, cty, ...} = lambdaInfo lambda
               in
                  Ssa.DirectExp.conApp
                  {con = con,
                   args = Vector.new1 env,
                   ty = cty}
               end

            val {arg, argType, body, mayInline, ...} = Sxml.Lambda.dest lambda
            val {envVars, envTy, func, ...} = lambdaInfo lambda

            val () =
               newScope
               (envVars, fn envVars =>
                newScope
                (Vector.map (recs, #var), fn recs' =>
                 let
                    val env = Var.newString "env"
                    val args = Vector.new2 ((env, envTy), convertBoundVar (arg, argType))
                    val resTy = #cty (varInfo (Sxml.VarExp.var (Sxml.Exp.result body)))

                    val body =
                       Ssa.DirectExp.lett
                       {decs = ((Vector.toList o Vector.map2)
                                (recs, recs', fn ({lambda, ...}, cvar) =>
                                 {var = cvar,
                                  exp = mkClos {lambda = lambda,
                                                env = Ssa.DirectExp.var (env, envTy)}})),
                        body = convertExp body}
                    val body =
                       Ssa.DirectExp.detupleBind
                       {tuple = env,
                        tupleTy = envTy,
                        components = envVars,
                        body = body}
                 in
                    addFunction {args = args,
                                 body = body,
                                 isMain = false,
                                 mayInline = mayInline,
                                 name = func,
                                 resTy = resTy}
                 end))

            val env = Var.newString "env"
         in
            Ssa.DirectExp.lett
            {decs = [{var = env,
                      exp = Ssa.DirectExp.tuple
                            {exps = convertVars envVars,
                             ty = envTy}}],
             body = mkClos {lambda = lambda,
                            env = Ssa.DirectExp.var (env, envTy)}}
         end

      val globals = Vector.new0 ()
      val main = Ssa.Func.newString "main"
      val () =
         addFunction {args = Vector.new0 (),
                      body = convertExp body,
                      isMain = true,
                      mayInline = false,
                      name = main,
                      resTy = Ssa.Type.unit}
      val program =
         Ssa.Program.T {datatypes = Vector.concat [datatypes, lambdaDatatypes],
                        globals = globals,
                        functions = !functions,
                        main = main}
   in
      {program = program,
       destroy = fn () => (destroyLambdaFree ();
                           destroyArrowInfo ();
                           destroyConvertType ();
                           Sxml.Exp.foreachBoundVar (body, remVarInfo o #1);
                           destroyLambdaInfo ())}
   end

val transform =
   Control.trace (Control.Pass, "TyTransform")
   transform

end