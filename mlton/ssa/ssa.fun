(* Copyright (C) 1999-2005 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

functor MeSsa (S: SSA_STRUCTS): ME_SSA =
   MeSimplify
   (MeRestore
   (MeShrink
   (MePrePasses
   (MeTypeCheck
   (MeAnalyze
   (MeDirectExp
   (MeSsaTree (S))))))))
