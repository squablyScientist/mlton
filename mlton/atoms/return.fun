(* Copyright (C) 2009,2017,2019 Matthew Fluet.
 * Copyright (C) 1999-2008 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

functor Return (S: RETURN_STRUCTS): RETURN =
   struct
      open S

      datatype t =
         NonTail of Label.t
       | Tail of int

      fun layout r =
         let
            open Layout
         in
            case r of
               NonTail l => seq [str "NonTail ", Label.layout l]
             | Tail i => seq [str "Tail #", Int.layout i]
         end

      fun equals (r, r'): bool =
         case (r, r') of
            (NonTail l, NonTail l') => Label.equals (l, l')
          | (Tail i, Tail i') => i = i'
          | _ => false
       
      (* TODO check with Fluet to determine if this is correct *)
      fun foldLabel (r, a, f) =
         case r of
            NonTail l => f (l, a)
          | Tail i => a

      fun foreachLabel (r, f) = foldLabel (r, (), f o #1)

      fun foldInt (r, a, f) = 
         case r of 
            NonTail l => a
          | Tail i => f (i, a)

      fun foreachInt (r, f) = foldInt (r, (), f o #1)

      (* TODO figure out if we still need map or should be done in case analysis
      * somewhere else, or split into two functions maybe (one for int one for
      * label)?*)
      (*
      fun map (r, f) =
         case r of
            Dead => Dead
          | NonTail {cont, handler} =>
               NonTail {cont = f cont,
                        handler = Handler.map (handler, f)}
          | Tail => Tail
      *)

      fun mapLabel (r, f) = 
         case r of 
            NonTail l => NonTail (f l)
          | Tail i => Tail i

      fun mapInt (r, f) = 
         case r of 
            NonTail l => NonTail l
          | Tail i => Tail (f i)

      (* TODO figure out if we still need compose or should be doing it otf *)
      (*
      fun compose (r, r') =
         case r' of
            Dead => Dead
          | NonTail {cont, handler} =>
               NonTail
               {cont = cont,
                handler = (case handler of
                              Handler.Caller =>
                                 (case r of
                                     Dead => Handler.Caller
                                   | NonTail {handler, ...} => handler
                                   | Tail => Handler.Caller)
                            | Handler.Dead => handler
                            | Handler.Handle _ => handler)}
          | Tail => r
      *)

      local
         val newHash = Random.word
         val localHash = newHash ()
         val tailHash = newHash ()
      in
         fun hash r =
            case r of
               NonTail l => Hash.combine (localHash, Label.hash l)
             | Tail i  => Hash.combine (tailHash, Word.fromInt i)
      end
   end
