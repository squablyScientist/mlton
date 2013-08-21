(* Copyright (C) 1999-2006 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature ME_RSSA_TRANSFORM_STRUCTS =
   sig
      structure Rssa: ME_RSSA
   end

signature ME_RSSA_TRANSFORM =
   sig
      include ME_RSSA_TRANSFORM_STRUCTS

      val transform: Rssa.Program.t -> Rssa.Program.t
   end
