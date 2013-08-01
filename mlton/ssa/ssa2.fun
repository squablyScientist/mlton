(* Copyright (C) 1999-2005 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

functor MeSsa2 (S: ME_SSA2_STRUCTS): ME_SSA2 =
   MeSimplify2
   (MeShrink2
   (MePrePasses2
   (MeTypeCheck2
   (MeAnalyze2
   (MeSsaTree2 (S))))))
