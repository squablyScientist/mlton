(* Copyright (C) 2013 Matthew Fluet.
 * Copyright (C) 1999-2007 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)


signature ME_PROFILE_STRUCTS =
   sig
      include ME_SHRINK
   end

signature ME_PROFILE =
   sig
      include ME_PROFILE_STRUCTS

      val addProfile: Program.t -> Program.t
      val dropProfile: Program.t -> Program.t
   end
