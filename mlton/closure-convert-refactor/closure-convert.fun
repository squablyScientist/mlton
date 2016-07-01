(* Copyright (C) 2016 Matthew Fluet.
 * Copyright (C) 1999-2005, 2008 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

functor ClosureConvertRefactor (S: CLOSURE_CONVERT_STRUCTS): CLOSURE_CONVERT =
struct

open S

structure TyCFA = TyCFA(S)
structure TyTransform = TyTransform(S)

fun closureConvert (program: Sxml.Program.t): Ssa.Program.t =
   let
      val Sxml.Program.T {body, ...} = program

      val {cfa, destroy = destroyCFA, ...} =
         TyCFA.cfa {config = ()} {program = program}

      val _ =
         Control.diagnostics
         (fn lay =>
          let
             val {get, set, rem} =
                Property.getSetOnce
                (Sxml.Var.plist,
                 Property.initRaise ("ClosureConvert.get", Sxml.Var.layout))
             val _ =
                Sxml.Exp.foreachBoundVar
                (body, fn (var, _, ty) => set (var, ty))
             val _ =
                Sxml.Exp.foreachPrimExp
                (body, fn (res, resTy, exp) =>
                 case exp of
                    Sxml.PrimExp.App {func, arg} =>
                       let
                          val func = Sxml.VarExp.var func
                          val arg = Sxml.VarExp.var arg
                          val lambdas =
                             cfa {arg = arg,
                                  argTy = get arg,
                                  func = func,
                                  res = res,
                                  resTy = resTy}
                          val lambdasCard =
                             List.length lambdas
                       in
                          (lay o Layout.str o String.concat)
                          ["|cfa(val ",
                           Sxml.Var.toString res,
                           " = ",
                           Sxml.Var.toString func,
                           " ",
                           Sxml.Var.toString arg,
                           ")| = ",
                           Int.toString lambdasCard]
                       end
                  | _ => ())
             val _ =
                Sxml.Exp.foreachBoundVar
                (body, fn (var, _, _) => rem var)
          in
             ()
          end)

      val {program, destroy = destroyTransform, ...} =
         TyTransform.transform {program = program, cfa = cfa}
      val _ = destroyCFA ()
      val _ = destroyTransform ()
      val _ = Ssa.Program.clear program
   in
      program
   end

end
