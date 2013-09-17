(* Copyright (C) 2013 Matthew Fluet, David Larsen.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)


functor MeMergeTailCalls (S: ME_SSA_TRANSFORM_STRUCTS): ME_SSA_TRANSFORM =
struct

open S
structure Graph = DirectedGraph
structure Node = Graph.Node

fun transform (Program.T {datatypes, globals, functions, main}) =
   let
      val {get = funcInfo : Func.t -> {function: Function.t,
                                       node: unit Node.t,
                                       rename: Func.t option ref},
           set = setFuncInfo, rem = remFuncInfo, ...} =
         Property.getSetOnce
         (Func.plist,
          Property.initRaise ("funcInfo", Func.layout))
      local
         fun mk sel f = sel (funcInfo f)
      in
         val funcToFunction = mk #function
         val funcToNode = mk #node
         val funcToRename' = mk #rename
         val funcToRename = ! o funcToRename'
      end
      fun renameFunc f =
         case funcToRename f of
            NONE => f
          | SOME f => f
      val {get = nodeInfo : unit Node.t -> {func: Func.t},
           set = setNodeInfo, ...} =
         Property.getSetOnce
         (Node.plist,
          Property.initRaise ("nodeInfo", Node.layout))
      local
         fun mk sel n = sel (nodeInfo n)
      in
         val nodeToFunc = mk #func
      end

      val G = Graph.new ()
      val () =
         List.foreach
         (functions, fn f =>
          let
             val {name, ...} = Function.dest f
             val node = Graph.newNode G
             val () = setFuncInfo (name, {function = f,
                                          node = node,
                                          rename = ref NONE})
             val () = setNodeInfo (node, {func = name})
          in
             ()
          end)
      val () =
         List.foreach
         (functions, fn f =>
          let
             val {name, blocks, raises = raisesCaller, returns = returnsCaller, ...} =
                Function.dest f
             val caller = funcToNode name
          in
             Vector.foreach
             (#blocks (Function.dest f), fn block =>
              case Block.transfer block of
                 Transfer.Call {func, return = Return.Tail, ...} =>
                    let
                       val {raises = raisesCallee, returns = returnsCallee, ...} =
                          Function.dest (funcToFunction func)
                       val callee = funcToNode func
                       val () = ignore (Graph.addEdge (G, {from = caller, to = callee}))
                    in
                       ()
                    end
               | _ => ())
          end)
      val sccs = Graph.stronglyConnectedComponents G
      val () =
         List.foreach
         (sccs, fn scc =>
          if List.length scc > 1
             then let
                     val funcs =
                        List.map (scc, nodeToFunc)
                     val names =
                        List.removeDuplicates
                        (List.map (funcs, Func.originalName),
                         String.equals)
                     val name = Func.newString (String.concatWith (names, "_"))
                     val _ =
                        Control.diagnostics
                        (fn display =>
                         let open Layout
                         in
                            display (seq [List.layout Func.layout funcs,
                                          str " => ",
                                          Func.layout name])
                         end)
                     val () =
                        List.foreach
                        (funcs, fn f =>
                         funcToRename' f := SOME name)
                  in
                     ()
                  end
          else ())

      fun rewriteBlock (block as Block.T {label, args, statements, transfer}) =
         Exn.withEscape
         (fn escape =>
          let
             val transfer =
                case transfer of
                   Transfer.Call {func, entry, args, return} =>
                      Transfer.Call {func = renameFunc func,
                                     entry = entry,
                                     args = args,
                                     return = return}
                 | _ => escape block
          in
             Block.T {label = label,
                      args = args,
                      statements = statements,
                      transfer = transfer}
          end)
      val functions =
         List.map
         (sccs, fn scc =>
          let
             val functions =
                List.map
                (scc, fn n =>
                 Function.dest (funcToFunction (nodeToFunc n)))
             val blocks =
                (Vector.concat o List.map)
                (functions, fn {blocks, ...} =>
                 Vector.map (blocks, rewriteBlock))
             val entries = Vector.concat (List.map (functions, #entries))
             val mayInline = List.forall (functions, #mayInline)
             val name = renameFunc (#name (hd functions))
             val raises = List.peekMap (functions, #raises)
             val returns = List.peekMap (functions, #returns)
          in
             Function.new {blocks = blocks,
                           entries = entries,
                           mayInline = mayInline,
                           name = name,
                           raises = raises,
                           returns = returns}
          end)
      val main =
         {func = renameFunc (#func main),
          entry = #entry main}
      val () = List.foreach (functions, remFuncInfo o #name o Function.dest)
   in
      Program.T {datatypes = datatypes,
                 globals = globals,
                 functions = functions,
                 main = main}
   end
end
