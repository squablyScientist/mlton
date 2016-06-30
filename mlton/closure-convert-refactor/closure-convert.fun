(* Copyright (C) 2016 Matthew Fluet.
 * Copyright (C) 1999-2005, 2008 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

functor ClosureConvert (S: CLOSURE_CONVERT_STRUCTS): CLOSURE_CONVERT =
struct

open S

structure TyCFA = TyCFA(S)
structure TyTransform = TyTransform(S)

fun closureConvert (program: Sxml.Program.t): Ssa.Program.t =
   Error.bug "ClosureConvert.closureConvert: unimplemented"

end
