(* Copyright (C) 2016 Matthew Fluet.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

signature CFA_STRUCTS =
   sig
      structure Sxml: SXML
   end

signature CFA =
   sig
      include CFA_STRUCTS

      val cfa: {program: Sxml.Program.t} ->
               {cfa: {arg: Sxml.Var.t,
                      argTy: Sxml.Type.t,
                      func: Sxml.Var.t,
                      res: Sxml.Var.t,
                      resTy: Sxml.Type.t} ->
                     Sxml.Lambda.t list,
                destroy: unit -> unit}
   end
