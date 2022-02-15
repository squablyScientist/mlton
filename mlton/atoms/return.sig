(* Copyright (C) 2009,2017,2019 Matthew Fluet.
 * Copyright (C) 1999-2008 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

signature RETURN_STRUCTS =
   sig
      structure Label: LABEL
   end

signature RETURN =
   sig
      include RETURN_STRUCTS

      datatype t =
         NonTail of Label.t
       | Tail of int

      (* TODO figure out if compose is needed *)
      (*val compose: t * t -> t*)
      val equals: t * t -> bool
      val foldLabel: t * 'a * (Label.t * 'a -> 'a) -> 'a
      val foldInt: t * 'a * (int * 'a -> 'a) -> 'a
      val foreachLabel: t * (Label.t -> unit) -> unit
      val foreachInt: t * (int -> unit) -> unit
      val hash: t -> word
      val layout: t -> Layout.t

      (* TODO figyre out if there should be two of these functions *)
      (*val map: t * (Label.t -> Label.t) -> t *)
      val mapLabel: t * (Label.t -> Label.t) -> t
      val mapInt: t * (int -> int) -> t
   end
