(* Copyright (C) 2009 Wesley W. Tersptra.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature ME_SSA2_TRANSFORM_STRUCTS =
   sig
      include ME_SHRINK2
   end

signature ME_SSA2_TRANSFORM =
   sig
      include ME_SSA2_TRANSFORM_STRUCTS

      val transform2: Program.t -> Program.t
   end
