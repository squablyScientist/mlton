(* Copyright (C) 2016 Matthew Fluet.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

structure Scan: SCAN =
struct

fun chars cs charRdr strm =
   case cs of
      [] => SOME ((), strm)
    | c::cs => (case charRdr strm of
                   SOME (c', strm') =>
                      if c = c' then SOME ((),strm') else NONE
                 | _ => NONE)

fun string s = chars (String.explode s)

end
