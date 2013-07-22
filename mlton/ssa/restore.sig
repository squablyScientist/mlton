(* Copyright (C) 1999-2005 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature ME_RESTORE_STRUCTS =
   sig
      include ME_SHRINK
   end

signature ME_RESTORE =
   sig
      include ME_RESTORE_STRUCTS

      val restoreFunction: 
         {globals: Statement.t vector} -> Function.t -> Function.t
      val restore: Program.t -> Program.t
   end
