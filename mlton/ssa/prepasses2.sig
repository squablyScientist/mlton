(* Copyright (C) 2005-2007 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature ME_PREPASSES2_STRUCTS =
   sig
      include ME_TYPE_CHECK2
   end

signature ME_PREPASSES2 =
   sig
      include ME_PREPASSES2_STRUCTS

      val eliminateDeadBlocksFunction: Function.t -> Function.t
      val eliminateDeadBlocks: Program.t -> Program.t
      val orderFunctions: Program.t -> Program.t
      val reverseFunctions: Program.t -> Program.t
   end
