(* Copyright (C) 2009 Wesley W. Tersptra.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)


signature ME_SSA_TRANSFORM_STRUCTS =
   sig
      include ME_RESTORE
   end

signature ME_SSA_TRANSFORM =
   sig
      include ME_SSA_TRANSFORM_STRUCTS

      val transform: Program.t -> Program.t
   end
