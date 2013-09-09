(* Copyright (C) 2013 David Larsen.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)


(*
 * This (diagnostic) pass duplicates all of the existing entries of a function,
 * to exercise the mutli-entry pipeline.
 *)
functor MeDuplicateEntries (S: ME_SSA_TRANSFORM_STRUCTS): ME_SSA_TRANSFORM =
struct

open S

fun transform (Program.T {datatypes, globals, functions, main}) =
   let
      (* Maps old entry points to new entry points. *)
      val {get = newEntries: FuncEntry.t -> FuncEntry.t list,
           set = setNewEntries: (FuncEntry.t * FuncEntry.t list) -> unit,
           destroy = destroyFuncEntryMap: unit -> unit} =
         Property.destGetSetOnce (FuncEntry.plist,
                          Property.initConst [])

      (*
       * Makes a copy of every entry point.
       *
       * New blocks are added so that the new entry point can pass its
       * arguments into the rest of the function.
       *
       * Say we start with a function that looks like this:
       *
       *  fun foo {...}
       *  fun_entry foo_0 (x_1) = L_1()
       *  L_1:
       *    ...
       *
       * When we duplicate the foo_0 entry, the function will look like this:
       *
       *  fun foo {...}
       *  fun_entry foo_0   (x_2) = L_2()
       *  fun_entry foo_0_0 (x_3) = L_3()
       *  L_2():
       *    goto L_4 (x_2)
       *  L_3():
       *    goto L_4 (x_3)
       *  L_1(x_1): (* L_1 gets the arguments that foo_0 used to have. *)
       *    ...
       *)
      fun duplicate (f: Function.t) : Function.t =
         let
            val {blocks, entries, mayInline, name, raises, returns} =
               Function.dest f
            fun dropType args = Vector.map (args, fn (a, _) => a)
            val blocks = ref blocks
            val (entries, newBlocks) = Vector.fold
               (entries, ([],[]),
                fn (FunctionEntry.T {args, function, name, start},
                    (entries, newBlocks)) =>
                  let
                     val oldName = FuncEntry.toString name

                     (* For now, leave the existing entry name the same.  This
                        pass will be updated later to have the callees randomly
                        pick either the new entry or the old entry. *)
                     val oldFuncEntry = name
                     val newFuncEntry = FuncEntry.newString oldName
                     val () = setNewEntries (name, [oldFuncEntry, newFuncEntry])

                     val oldArgs = args

                     (* Alpha-rename the arguments. *)
                     val newOldArgs = Vector.map
                        (args,
                        fn (v, t) => ((Var.newString (Var.originalName v)), t))
                     val newNewArgs = Vector.map
                        (args,
                        fn (v, t) => ((Var.newString (Var.originalName v)), t))

                     (* Filter through the existing functions to make the
                        union point for the two function entries (the old and
                        the new) and put it in the function.  The replacement
                        block should have the arguments of the entry that is
                        being replaced. *)
                     val oldStartLabel = start
                     val () = blocks := Vector.map (!blocks,
                        fn block as Block.T {args= _, label, statements, transfer} =>
                           if Label.equals (label, start)
                              then Block.T {args = oldArgs,
                                            label = oldStartLabel,
                                            statements = statements,
                                            transfer = transfer}
                              else block
                        )

                     (* A new block for the old function entry.  This passes
                        the arguments into the oldStartBlock. *)
                     val newOldStartBlock as Block.T{label = newOldStartLabel, ...} =
                        Block.T {args = Vector.new0 (),
                                 label = Label.newNoname (),
                                 statements = Vector.new0 (),
                                 transfer = Transfer.Goto{args = dropType newOldArgs,
                                                          dst = oldStartLabel}}
                     val newNewStartBlock as Block.T{label = newNewStartLabel, ...} =
                        Block.T {args = Vector.new0 (),
                                 label = Label.newNoname (),
                                 statements = Vector.new0 (),
                                 transfer = Transfer.Goto{args = dropType newNewArgs,
                                                          dst = oldStartLabel}}
                     val old = FunctionEntry.T {args = newOldArgs,
                                                function = function,
                                                name = oldFuncEntry,
                                                start = newOldStartLabel}
                     val new = FunctionEntry.T {args = newNewArgs,
                                                function = function,
                                                name = newFuncEntry,
                                                start = newNewStartLabel}
                  in
                     (old :: new :: entries,
                     newOldStartBlock :: newNewStartBlock :: newBlocks)
                  end
               )
            val blocks = Vector.concat [(Vector.fromList newBlocks), !blocks]
         in
            Function.new {blocks = blocks,
                          entries = Vector.fromList entries,
                          mayInline = mayInline,
                          name = name,
                          raises = raises,
                          returns = returns}
         end

      (* Updates function calls to use the newly duplicated function entries *)
      fun updateCalls (f: Function.t) =
         let
            val {blocks, entries, mayInline, name, raises, returns} =
               Function.dest f
            val blocks = Vector.map
               (blocks,
                fn block =>
                  let
                     val Block.T {args, label, statements, transfer} = block
                  in
                     case transfer of
                        Transfer.Call {args = cargs, entry, func, return} =>
                           Block.T {args = args,
                                    label = label,
                                    statements = statements,
                                    transfer =
                              Transfer.Call {args = cargs,
                                 (* TODO Make this randomly pick from the list,
                                    so that all of the function entries are
                                    exercised. *)
                                 entry = hd (tl (newEntries entry)),
                                 func = func,
                                 return = return}}
                     |  _  => block
                  end
               )
         in
            Function.new {blocks = blocks,
                          entries = entries,
                          mayInline = mayInline,
                          name = name,
                          raises = raises,
                          returns = returns}
         end
      val functions = List.map (functions, duplicate)
      (* Only run updateCalls after all of the function entries have been
         duplicated. *)
      val functions = List.map (functions, updateCalls)
      val () = destroyFuncEntryMap ()
   in
         (Program.T {datatypes = datatypes,
                    globals = globals,
                    functions = functions,
                    main = main})
   end

end
