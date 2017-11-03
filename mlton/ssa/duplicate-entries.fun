(* Copyright (C) 2017 Matthew Fluet.
 * Copyright (C) 2013 Matthew Fluet, David Larsen.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)


(*
 * This (diagnostic) pass duplicates all of the existing entries of a function,
 * to exercise the mutli-entry pipeline.
 *)
functor DuplicateEntries (S: SSA_TRANSFORM_STRUCTS): SSA_TRANSFORM =
struct

open S

fun transform (Program.T {datatypes, globals, functions, main}) =
   let
      val shrink = shrinkFunction {globals = globals}
      val degree = !Control.duplicateEntriesDegree

      val {get = entryCount: FuncEntry.t -> Counter.t,
           destroy = destroyEntryCount} =
         Property.destGet
         (FuncEntry.plist,
          Property.initFun (fn _ => Counter.new 0))
      val () =
         List.foreach
         (functions, fn f =>
          Vector.foreach
          (Function.blocks f, fn b =>
           case Block.transfer b of
              Transfer.Call {entry, ...} =>
                 Counter.tick (entryCount entry)
            | _ => ()))
      val () = Counter.tick (entryCount (#entry main))

      val {get = entryInfo: FuncEntry.t -> {newNames: FuncEntry.t vector,
                                            counter: Counter.t},
           destroy = destroyEntryInfo} =
         Property.destGet
         (FuncEntry.plist,
          Property.initFun
          (fn e => let
                      val count = Counter.value (entryCount e)
                      val count = Int.max (1, count)
                      val degree =
                         if degree < 0
                            then count
                            else Int.min (degree, count)
                      val newNames =
                         Vector.tabulate (degree, fn _ => FuncEntry.new e)
                   in
                      {newNames = newNames,
                       counter = Counter.new 0}
                   end))
      fun renameEntry e =
         let
            val {newNames, counter} = entryInfo e
         in
            Vector.sub (newNames, (Counter.next counter mod Vector.length newNames))
         end

      (*
       * Makes copies of every entry point.
       *
       * New blocks are added so that the new entry point can pass its
       * arguments into the rest of the function.
       *
       * Say we start with a function that looks like this:
       *
       *  fun foo: {...} =
       *  entry foo_1 (x_1) = L_1()
       *  L_1 ():
       *    ...
       *
       * When we duplicate the foo_1 entry, the function will look like this:
       *
       *  fun foo: {...} =
       *  entry foo_2 (x_2) = L_2 ()
       *  entry foo_3 (x_3) = L_3 ()
       *  L_2 ():
       *    goto L_4 (x_2)
       *  L_3 ():
       *    goto L_4 (x_3)
       *  L_4 (x_1):
       *    goto L_1 ()
       *  L_1 ():
       *    ...
       *
       * Note that the "shrink" cleanup pass will merge the L_1 and L_4 blocks.
       *)
      fun duplicate (f: Function.t) : Function.t =
         let
            val {blocks, entries, mayInline, name, raises, returns} =
               Function.dest f
            val (newEntries, newBlocks) =
               Vector.fold
               (entries, ([],[]), fn (FunctionEntry.T {args, name, start}, (newEntries, newBlocks)) =>
                let
                   val {newNames, ...} = entryInfo name
                   val newJoin = Label.new start
                   val newBlocks =
                      (Block.T
                       {label = newJoin,
                        args = args,
                        statements = Vector.new0 (),
                        transfer = (Transfer.Goto
                                    {dst = start,
                                     args = Vector.new0 ()})}) ::
                      newBlocks
                in
                   Vector.fold
                   (newNames, (newEntries, newBlocks), fn (newName, (newEntries, newBlocks)) =>
                    let
                       val newArgs =
                          Vector.map (args, fn (x, ty) => (Var.new x, ty))
                       val newStart =
                          Label.new start
                    in
                       ((FunctionEntry.T
                         {name = newName,
                          args = newArgs,
                          start = newStart}) ::
                        newEntries,
                        (Block.T
                         {label = newStart,
                          args = Vector.new0 (),
                          statements = Vector.new0 (),
                          transfer = (Transfer.Goto
                                      {dst = newJoin,
                                       args = Vector.map (newArgs, #1)})}) ::
                        newBlocks)
                    end)
                end)
            val blocks =
               Vector.map
               (blocks, fn Block.T {label, args, statements, transfer} =>
                let
                   val newTransfer =
                      case transfer of
                         Transfer.Call {func, entry, args, return} =>
                            Transfer.Call {func = func,
                                           entry = renameEntry entry,
                                           args = args,
                                           return = return}
                       | _ => transfer
                in
                   Block.T
                   {label = label,
                    args = args,
                    statements = statements,
                    transfer = newTransfer}
                end)
         in
            shrink (Function.new {blocks = Vector.concat [Vector.fromList newBlocks, blocks],
                                  entries = Vector.fromList newEntries,
                                  mayInline = mayInline,
                                  name = name,
                                  raises = raises,
                                  returns = returns})
         end
      val newFunctions = List.map (functions, duplicate)
      val newMain = {func = #func main,
                     entry = renameEntry (#entry main)}
      val () = destroyEntryInfo ()
      val () = destroyEntryCount ()
   in
      Program.T {datatypes = datatypes,
                 globals = globals,
                 functions = newFunctions,
                 main = newMain}
   end
end
