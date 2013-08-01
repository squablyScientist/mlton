(* Copyright (C) 1999-2005 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature ME_SSA2_STRUCTS =
   sig
      include SSA_TREE2_STRUCTS
   end

signature ME_SSA2 =
   sig
      include ME_SIMPLIFY2
   end
