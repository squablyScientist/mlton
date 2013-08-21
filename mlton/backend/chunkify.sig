(* Copyright (C) 2009 Matthew Fluet.
 * Copyright (C) 1999-2005 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature ME_CHUNKIFY_STRUCTS =
   sig
      include ME_RSSA
   end

signature ME_CHUNKIFY =
   sig
      include ME_CHUNKIFY_STRUCTS

      (* Partitions all the labels declared into disjoint sets, referred
       * to as chunks.  Returns the list of chunks.
       * All funcs, conts, and handlers are assumed to be entry points.
       * All conts and handlers are assumed to be return points.
       *)
      val chunkify: Program.t -> {
                                  funcs: Func.t vector,
                                  labels: Label.t vector
                                  } vector
   end
