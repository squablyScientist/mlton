(* Copyright (C) 1999-2006 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature ME_SIMPLIFY_STRUCTS =
   sig
      include ME_RESTORE
   end

signature ME_SIMPLIFY =
   sig
      include ME_SIMPLIFY_STRUCTS

      val simplify: Program.t -> Program.t
   end
