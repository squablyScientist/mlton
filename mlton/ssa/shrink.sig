(* Copyright (C) 1999-2005 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature ME_SHRINK_STRUCTS =
   sig
      include ME_PREPASSES
   end

signature ME_SHRINK =
   sig
      include ME_SHRINK_STRUCTS

      val shrinkFunction: 
         {globals: Statement.t vector} -> Function.t -> Function.t
      val shrink: Program.t -> Program.t
   end
