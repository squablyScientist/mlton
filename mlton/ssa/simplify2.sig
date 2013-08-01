(* Copyright (C) 1999-2006 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature ME_SIMPLIFY2_STRUCTS =
   sig
      include ME_SHRINK2
   end

signature ME_SIMPLIFY2 =
   sig
      include ME_SIMPLIFY2_STRUCTS

      val simplify: Program.t -> Program.t
   end
