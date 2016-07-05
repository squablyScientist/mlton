(* Copyright (C) 2016 Matthew Fluet.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

functor PowerSetLattice (S: POWERSET_LATTICE_STRUCTS): POWERSET_LATTICE =
struct

open S

structure Elt = Element

structure EltSet :>
   sig
      type t
      val add: t * Elt.t -> t
      val contains: t * Elt.t -> bool
      val empty: t
      val foreach: t * (Elt.t -> unit) -> unit
      val fromList: Elt.t list -> t
      val layout: t -> Layout.t
      val singleton: Elt.t -> t
      val toList: t -> Elt.t list
   end =
   struct
      type t = Elt.t list
      val {add, contains, empty, singleton, ...} =
         List.set {equals = Elt.equals, layout = Elt.layout}
      val foreach = List.foreach
      fun fromList es = List.removeDuplicates (es, Elt.equals)
      fun layout es =
         Layout.seq [Layout.str "{",
                     (Layout.fill o Layout.separateRight)
                     (List.map (es, Elt.layout), ","),
                     Layout.str "}"]
      val toList = fn es => es
   end

datatype t = T of {elements: EltSet.t ref,
                   frozen: bool ref,
                   handlers: (Elt.t -> unit) list ref}

fun layout (T {elements, ...}) =
   EltSet.layout (!elements)

fun new es = T {elements = ref es,
                frozen = ref false,
                handlers = ref []}

fun empty () = new EltSet.empty
fun singleton e = new (EltSet.singleton e)
fun fromList es = new (EltSet.fromList es)

fun getElements (T {elements, frozen, handlers, ...}) =
   (frozen := true;
    handlers := [];
    EltSet.toList (!elements))

fun addHandler (T {elements, handlers, ...}, h) =
   (List.push (handlers, h);
    EltSet.foreach (!elements, fn e => h e))

fun op<< (e, T {elements, frozen, handlers, ...}) =
   if EltSet.contains (!elements, e)
      then ()
      else if !frozen
              then Error.bug "PowerSetLattice.contains: frozen"
              else (elements := EltSet.add (!elements, e);
                    List.foreach (!handlers, fn h => h e))

fun op<= (es, es') =
   addHandler(es, fn e => << (e, es'))

end
