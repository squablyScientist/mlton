(* Copyright (C) 2016 Matthew Fluet.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature SCAN =
   sig
      val string: string -> (char,'a) StringCvt.reader -> (unit,'a) StringCvt.reader
   end
