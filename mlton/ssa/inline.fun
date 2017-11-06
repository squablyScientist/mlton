(* Copyright (C) 2017 Matthew Fluet.
 * Copyright (C) 2013 Matthew Fluet, David Larsen.
 * Copyright (C) 2009 Matthew Fluet.
 * Copyright (C) 1999-2007 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

functor Inline (S: INLINE_STRUCTS): INLINE = 
struct

open S
open Exp Transfer

structure Function =
   struct
      open Function

      fun containsCall (f: Function.t, entry: FuncEntry.t): bool =
         Exn.withEscape
         (fn escape =>
          (Function.dfsReachable
           (f, fn name => FuncEntry.equals (name, entry),
            fn Block.T {transfer, ...} =>
            ((case transfer of
                 Call _ => escape true
               | _ => ())
              ; fn () => ()))
           ; false))
      fun containsLoop (f: Function.t, entry: FuncEntry.t): bool =
         let
            val {get, set, destroy} =
               Property.destGetSet (Label.plist, Property.initConst false)
         in
            Exn.withEscape
            (fn escape =>
             (Function.dfsReachable
              (f, fn name => FuncEntry.equals (name, entry),
               fn (Block.T {label, transfer, ...}) =>
               (set (label, true)
                ; (case transfer of
                      Goto {dst, ...} => if get dst then escape true else ()
                    | _ => ())
                ; fn () => set (label, false)))
              ; false))
            before (destroy ())
         end
   end

local
   fun 'a make (dontInlineEntry: Function.t * FuncEntry.t * 'a -> bool)
      (Program.T {functions, ...}, a: 'a):
      {func: Func.t, entry: FuncEntry.t} -> bool =
      let
         val {get = shouldInline: FuncEntry.t -> bool,
              set = setShouldInline, ...} =
            Property.getSetOnce (FuncEntry.plist, Property.initConst false)
      in
         List.foreach
         (functions, fn f =>
          Vector.foreach
          (Function.entries f, fn FunctionEntry.T {name, ...} =>
           if not (Function.mayInline f) orelse dontInlineEntry (f, name, a)
              then ()
              else setShouldInline (name, true)))
         ; Control.diagnostics
           (fn display =>
            let open Layout
            in List.foreach
               (functions, fn f =>
                Vector.foreach
                (Function.entries f, fn e =>
                 let
                    val name = FunctionEntry.name e
                    val shouldInline = shouldInline name
                 in
                    display
                    (seq [Func.layout (Function.name f), str "@",
                          FuncEntry.layout name, str ": ",
                          record [("shouldInline", Bool.layout shouldInline)]])
                 end))
            end)
         ; shouldInline o #entry
      end
in
   val leafOnce = make (fn (f, entry, {size}) =>
                        Option.isNone (Function.sizeReachableMax
                                       (f, fn name => FuncEntry.equals (name, entry),
                                        {max = size,
                                         sizeExp = Exp.size,
                                         sizeTransfer = Transfer.size}))
                        orelse Function.containsCall (f, entry))
   val leafOnceNoLoop = make (fn (f, entry, {size}) =>
                              Option.isNone (Function.sizeReachableMax
                                             (f, fn name => FuncEntry.equals (name, entry),
                                              {max = size,
                                               sizeExp = Exp.size,
                                               sizeTransfer = Transfer.size}))
                              orelse Function.containsCall (f, entry)
                              orelse Function.containsLoop (f, entry))
end

structure Graph = DirectedGraph
structure Node = Graph.Node

local
   fun make (dontInline: Function.t * FuncEntry.t -> bool)
      (Program.T {functions, ...}, {size: int option}):
      {func: Func.t, entry: FuncEntry.t} -> bool =
      let
         val max = size
         type info = {function: Function.t,
                      node: unit Node.t,
                      shouldInline: bool ref,
                      size: int ref}
         val {get = entryInfo: FuncEntry.t -> info,
              set = setEntryInfo, ...} =
            Property.getSetOnce
            (FuncEntry.plist, Property.initRaise ("entryInfo", FuncEntry.layout))
         val {get = nodeEntry: unit Node.t -> FuncEntry.t,
              set = setNodeEntry, ...} =
            Property.getSetOnce 
            (Node.plist, Property.initRaise ("nodeEntry", Node.layout))
         val graph = Graph.new ()
         (* initialize the info for each entry *)
         val _ = 
            List.foreach
            (functions, fn f =>
             Vector.foreach
             (Function.entries f, fn e =>
              let
                 val name = FunctionEntry.name e
                 val n = Graph.newNode graph
              in
                 setNodeEntry (n, name)
                 ; setEntryInfo (name, {function = f,
                                        node = n,
                                        shouldInline = ref false,
                                        size = ref 0})
              end))
         (* Build the call graph. *)
         val _ =
            List.foreach
            (functions, fn f =>
             Vector.foreach
             (Function.entries f, fn FunctionEntry.T {name, ...} =>
              let
                 val blocks =
                    Function.blocksReachable
                    (f, fn entry => FuncEntry.equals (entry, name))
                 val {node, ...} = entryInfo name
              in
                 Vector.foreach
                 (blocks, fn Block.T {transfer, ...} =>
                  case transfer of
                     Call {entry, ...} =>
                        (ignore o Graph.addEdge)
                        (graph, {from = node, to = #node (entryInfo entry)})
                   | _ => ())
              end))
         (* Compute strongly-connected components.
          * Then start at the leaves of the call graph and work up.
          *)
         val _ = 
            List.foreach
            (rev (Graph.stronglyConnectedComponents graph),
             fn scc =>
             case scc of 
                [n] =>
                   let
                      val entry = nodeEntry n
                      val {function, shouldInline, size, ...} = 
                         entryInfo entry
                   in 
                      if Function.mayInline function
                         andalso not (dontInline (function, entry))
                         then Exn.withEscape
                              (fn escape =>
                               let
                                  val res =
                                     Function.sizeReachableMax
                                     (function,
                                      fn name => FuncEntry.equals (name, entry),
                                      {max = max,
                                       sizeExp = Exp.size,
                                       sizeTransfer =
                                       fn t =>
                                       case t of
                                          Call {entry, ...} =>
                                             let
                                                val {shouldInline, size, ...} =
                                                   entryInfo entry
                                             in
                                                if !shouldInline
                                                   then !size
                                                   else escape ()
                                             end
                                        | _ => Transfer.size t})
                               in
                                  case res of
                                     NONE => ()
                                   | SOME n => (shouldInline := true
                                                ; size := n)
                               end)
                      else ()
                   end
              | _ => ())
         val _ =
            Control.diagnostics
            (fn display =>
             let open Layout
             in List.foreach
                (functions, fn f =>
                 Vector.foreach
                 (Function.entries f, fn e =>
                  let
                     val name = FunctionEntry.name e
                     val {shouldInline, size, ...} = entryInfo name
                     val shouldInline = !shouldInline
                     val size = !size
                  in
                     display
                     (seq [Func.layout (Function.name f), str "@",
                           FuncEntry.layout name, str ": ",
                           record [("shouldInline", Bool.layout shouldInline),
                                   ("size", Int.layout size)]])
                  end))
             end)
      in
         ! o #shouldInline o entryInfo o #entry
      end
in
   val leafRepeat = make (fn _ => false)
   val leafRepeatNoLoop = make (fn (f, e) => Function.containsLoop (f, e))
end

fun nonRecursive
   (Program.T {functions, ...}, {small: int, product: int}):
   {func: Func.t, entry: FuncEntry.t} -> bool =
   let
      type info = {doesCallSelf: bool ref,
                   entry: FuncEntry.t,
                   function: Function.t,
                   node: unit Node.t,
                   numCalls: int ref,
                   shouldInline: bool ref,
                   size: int ref}
      val {get = entryInfo: FuncEntry.t -> info,
           set = setEntryInfo, ...} =
         Property.getSetOnce
         (FuncEntry.plist, Property.initRaise ("entryInfo", FuncEntry.layout))
      val {get = nodeEntry: unit Node.t -> FuncEntry.t,
           set = setNodeEntry, ...} =
         Property.getSetOnce 
         (Node.plist, Property.initRaise ("nodeEntry", Node.layout))
      val graph = Graph.new ()
      (* initialize the info for each entry *)
      val _ = 
         List.foreach
         (functions, fn f =>
          Vector.foreach
          (Function.entries f, fn e =>
           let
              val name = FunctionEntry.name e
              val n = Graph.newNode graph
           in
              setNodeEntry (n, name)
              ; setEntryInfo (name, {doesCallSelf = ref false,
                                     entry = name,
                                     function = f,
                                     node = n,
                                     numCalls = ref 0,
                                     shouldInline = ref false,
                                     size = ref 0})
           end))
      (* Update call counts. *)
      val _ = 
         List.foreach
         (functions, fn f =>
          Vector.foreach
          (Function.entries f, fn e =>
           let
              val name = FunctionEntry.name e
              val blocks =
                 Function.blocksReachable
                 (f, fn entry => FuncEntry.equals (entry, name))
             val {doesCallSelf, ...} = entryInfo name
          in
             Vector.foreach
             (blocks, fn Block.T {transfer, ...} =>
              case transfer of
                 Call {entry, ...} =>
                    let
                       val {numCalls, ...} = entryInfo entry
                    in
                       if FuncEntry.equals (name, entry)
                          then doesCallSelf := true
                       else Int.inc numCalls
                    end
               | _ => ())
          end))
      (* Merge call counts of "major" entries. *)
      val _ =
         List.foreach
         (functions, fn f =>
          let
             val entries = Function.entries f
             fun doit () =
                let
                   val funcSize =
                      Function.size
                      (f, {sizeExp = Exp.size,
                           sizeTransfer = Transfer.size})
                   val majorEntries =
                      Vector.keepAll
                      (entries, fn e =>
                       let
                          val name = FunctionEntry.name e
                          val {doesCallSelf, ...} =
                             entryInfo (FunctionEntry.name e)
                          val entrySize =
                             Function.sizeReachable
                             (f, fn entry => FuncEntry.equals (entry, name),
                              {sizeExp = Exp.size,
                               sizeTransfer = Transfer.size})
                       in
                          not (!doesCallSelf)
                          andalso
                          entrySize >= funcSize div 2
                       end)
                   val majorNumCalls =
                      Vector.fold
                      (majorEntries, 0, fn (e, majorNumCalls) =>
                       let
                          val {numCalls, ...} =
                             entryInfo (FunctionEntry.name e)
                       in
                          majorNumCalls + !numCalls
                       end)
                   val _ =
                      Vector.foreach
                      (majorEntries, fn e =>
                       let
                          val {numCalls, ...} =
                             entryInfo (FunctionEntry.name e)
                       in
                          numCalls := majorNumCalls
                       end)
                in
                   ()
                end
          in
             if Vector.length entries > 1
                then doit ()
                else ()
          end)
      fun mayInline (setSize: bool,
                     {entry, function, doesCallSelf, numCalls, size, ...}: info): bool =
         Function.mayInline function
         andalso not (!doesCallSelf)
         andalso let
                    val n =
                       Function.sizeReachable
                       (function,
                        fn name => FuncEntry.equals (name, entry),
                        {sizeExp = Exp.size,
                         sizeTransfer =
                         fn t as Call {entry, ...} =>
                               let
                                  val {shouldInline, size, ...} = entryInfo entry
                               in
                                  if !shouldInline
                                     then !size
                                     else Transfer.size t
                               end
                          | t => Transfer.size t})
                 in
                    if setSize
                       then size := n
                    else ()
                    ; (!numCalls - 1) * (n - small) <= product
                 end
      (* Build the call graph.  Do not include functions that we already know
       * will not be inlined.
       *)
      val _ =
         List.foreach
         (functions, fn f =>
          Vector.foreach
          (Function.entries f, fn e =>
           let
              val name = FunctionEntry.name e
              val blocks =
                 Function.blocksReachable
                 (f, fn entry => FuncEntry.equals (entry, name))
              val info as {node, ...} = entryInfo name
           in
              if mayInline (false, info)
                 then Vector.foreach
                      (blocks, fn Block.T {transfer, ...} =>
                       case transfer of
                          Call {entry, ...} =>
                             if FuncEntry.equals (name, entry)
                                then ()
                                else (ignore o Graph.addEdge)
                                     (graph, {from = node, to = #node (entryInfo entry)})
                        | _ => ())
                 else ()
           end))
      (* Compute strongly-connected components.
       * Then start at the leaves of the call graph and work up.
       *)
      val _ = 
         List.foreach
         (rev (Graph.stronglyConnectedComponents graph),
          fn [n] => let
                       val entry = nodeEntry n
                       val info as {shouldInline, ...} = entryInfo entry
                    in
                       shouldInline := mayInline (true, info)
                    end
           | _ => ())
      val _ =
         Control.diagnostics
         (fn display =>
          let open Layout
          in List.foreach
             (functions, fn f =>
              Vector.foreach
              (Function.entries f, fn e =>
               let
                  val name = FunctionEntry.name e
                  val {numCalls, shouldInline, size, ...} = entryInfo name
                  val numCalls = !numCalls
                  val shouldInline = !shouldInline
                  val size = !size
               in
                  display
                  (seq [Func.layout (Function.name f), str "@",
                        FuncEntry.layout name, str ": ",
                        record [("numCalls", Int.layout numCalls),
                                ("shouldInline", Bool.layout shouldInline),
                                ("size", Int.layout size)]])
               end))
          end)
   in
      ! o #shouldInline o entryInfo o #entry
   end

fun transform {program as Program.T {datatypes, globals, functions, main},
               shouldInline: {func: Func.t, entry: FuncEntry.t} -> bool,
               inlineIntoMain: bool} =
   let
      val shouldInline = fn {func, entry} =>
         if Func.equals (func, #func main) andalso FuncEntry.equals (entry, #entry main)
            then false
            else shouldInline {func = func, entry = entry}
      val {get = entryInfo: FuncEntry.t -> {function: Function.t,
                                            isCalledByMain: bool ref},
           set = setEntryInfo, ...} =
         Property.getSetOnce
         (FuncEntry.plist, Property.initRaise ("Inline.entryInfo", FuncEntry.layout))
      val isCalledByMain: FuncEntry.t -> bool =
         ! o #isCalledByMain o entryInfo
      val () =
         List.foreach
         (functions, fn f =>
          Vector.foreach
          (Function.entries f, fn e =>
           setEntryInfo (FunctionEntry.name e,
                         {function = f,
                          isCalledByMain = ref false})))
      val () =
         Vector.foreach 
         (#blocks (Function.dest (Program.mainFunction program)),
          fn Block.T {transfer, ...} =>
          case transfer of
             Transfer.Call {entry, ...} =>
                #isCalledByMain (entryInfo entry) := true
           | _ => ())
      fun doit (blocks: Block.t vector,
                return: Return.t) : Block.t vector =
         let
            val newBlocks = ref []
            val blocks =
               Vector.map
               (blocks,
                fn block as Block.T {label, args, statements, transfer} =>
                let
                   fun new transfer =
                      Block.T {label = label,
                               args = args,
                               statements = statements,
                               transfer = transfer}
                in
                  case transfer of
                     Call {args, entry, func, return = return'} =>
                        let
                           val return = Return.compose (return, return')
                        in
                           if shouldInline {func = func, entry = entry}
                              then 
                              let
                                 local
                                    val {entries, blocks, ...} =
                                       (Function.dest o Function.alphaRename) 
                                       (#function (entryInfo entry),
                                        fn name => FuncEntry.equals (name, entry))
                                    val blocks = doit (blocks, return)
                                    val _ = List.push (newBlocks, blocks)
                                    val FunctionEntry.T {args, name, start, ...} =
                                       Vector.first (entries)
                                    val name =
                                       Label.newString (Func.originalName func ^ "$" ^ FuncEntry.originalName name)
                                    val _ = 
                                       List.push 
                                       (newBlocks,
                                        Vector.new1
                                        (Block.T
                                         {label = name,
                                          args = args,
                                          statements = Vector.new0 (),
                                          transfer = Goto {dst = start,
                                                           args = Vector.new0 ()}}))
                                 in
                                    val name = name
                                 end
                              in
                                 new (Goto {dst = name, 
                                            args = args})
                              end
                           else new (Call {func = func,
                                           entry = entry,
                                           args = args,
                                           return = return})
                        end
                   | Raise xs =>
                        (case return of
                            Return.NonTail
                            {handler = Handler.Handle handler, ...} =>
                               new (Goto {dst = handler,
                                          args = xs})
                          | _ => block)
                   | Return xs =>
                        (case return of
                            Return.NonTail {cont, ...} =>
                               new (Goto {dst = cont, args = xs})
                          | _ => block)
                   | _ => block
                end)
         in
            Vector.concat (blocks::(!newBlocks))
         end
      val shrink = shrinkFunction {globals = globals}
      val functions =
         List.fold
         (functions, [], fn (f, ac) =>
          let
             val {blocks, entries, mayInline, name as func, raises, returns} =
                Function.dest f
             val keptEntries =
                Vector.keepAllMap
                (entries, fn e as FunctionEntry.T {name = entry, ...} =>
                 if shouldInline {func = func, entry = entry}
                    then if inlineIntoMain
                            then NONE
                            else if isCalledByMain entry
                                    then SOME e
                                    else NONE
                    else SOME e)
             fun keep () =
                let
                   val blocks = doit (blocks, Return.Tail)
                in
                   shrink (Function.new {blocks = blocks,
                                         entries = keptEntries,
                                         mayInline = mayInline,
                                         name = name,
                                         raises = raises,
                                         returns = returns})
                   :: ac
                end
          in
             if Func.equals (func, #func main)
                then if inlineIntoMain
                        then keep ()
                     else f :: ac
             else if Vector.isEmpty keptEntries
                     then ac
                  else keep ()
          end)
      val program =
         Program.T {datatypes = datatypes,
                    globals = globals,
                    functions = functions,
                    main = main}
      val _ = Program.clearTop program
   in
      program
   end

fun inlineLeaf (p, {loops, repeat, size}) =
   if size = SOME 0
      then p
   else transform {program = p,
                   shouldInline =
                   case (loops, repeat) of
                      (false, false) => leafOnce (p, {size = size})
                    | (false, true) => leafRepeat (p, {size = size})
                    | (true, false) => leafOnceNoLoop (p, {size = size})
                    | (true, true) => leafRepeatNoLoop (p, {size = size}),
                   inlineIntoMain = true}
fun inlineNonRecursive (p, arg) =
   transform {program = p,
              shouldInline = nonRecursive (p, arg),
              inlineIntoMain = !Control.inlineIntoMain}

end
