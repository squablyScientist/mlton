(* Copyright (C) 2013 Matthew Fluet.
 *
 * MLton is released under a BSD-style license.
 * See the file MLton-LICENSE for details.
 *)

functor SplitEntries (S: SSA_TRANSFORM_STRUCTS): SSA_TRANSFORM =
struct

open S
open Exp Transfer

fun transform (Program.T {datatypes, globals, functions, main}) =
   let
      (* restore and shrink *)
      val restore = restoreFunction {globals = globals}
      val shrink = shrinkFunction {globals = globals}

      (* tyconInfo *)
      val {get = tyconInfo: Tycon.t -> {cons: Con.t vector},
           set = setTyconInfo, ...} =
         Property.getSetOnce
         (Tycon.plist, Property.initRaise ("knownCase.conInfo", Tycon.layout))
      (* conInfo *)
      val {get = conInfo: Con.t -> {args: Type.t vector, index: int, tycon: Tycon.t},
           set = setConInfo, ...} =
         Property.getSetOnce
         (Con.plist, Property.initRaise ("splitEntries.conInfo", Con.layout))
      val _ =
         Vector.foreach
         (datatypes, fn Datatype.T {tycon, cons} =>
          (setTyconInfo (tycon, {cons = Vector.map (cons, #con)});
           Vector.foreachi
           (cons, fn (i, {con, args}) =>
            setConInfo (con, {args = args, index = i, tycon = tycon}))))

      (* entryInfo *)
      val {get = entryInfo: FuncEntry.t -> {testIndex: int, newEntryNames: FuncEntry.t vector} option,
           set = setEntryInfo, ...} =
         Property.getSetOnce
         (FuncEntry.plist, Property.initRaise ("splitEntries.entryInfo", FuncEntry.layout))

      (* labelInfo *)
      val {get = labelInfo: Label.t -> {block: Block.t},
           set = setLabelInfo, ...} =
         Property.getSetOnce
         (Label.plist, Property.initRaise ("splitEntries.labelInfo", Label.layout))

      (* varInfo *)
      val {get = varInfo: Var.t -> {conApp: {con: Con.t, args: Var.t vector} option},
           set = setVarInfo, ...} =
         Property.getSetOnce
         (Var.plist, Property.initRaise ("splitEntries.varInfo", Var.layout))

      val functions =
         List.map
         (functions, fn f =>
          let
             val {blocks, entries, mayInline, name, raises, returns} =
                Function.dest f
             val () =
                Vector.foreach
                (blocks, fn block as Block.T {label, ...} =>
                 setLabelInfo (label, {block = block}))
             val (newEntriess, newBlockss) =
                Vector.fold
                (entries, ([], []), fn (entry, (newEntriess, newBlockss)) =>
                 Exn.withEscape
                 (fn escape =>
                  let
                     val FunctionEntry.T {name, args, start} = entry
                     val escape = fn () =>
                        (setEntryInfo (name, NONE)
                         ; ignore (escape (newEntriess, newBlockss))
                         ; Error.bug "splitEntries.escape")
                     val Block.T {statements, transfer, ...} = #block (labelInfo start)
                     val () =
                        if Vector.length statements > 0
                           then escape ()
                        else ()
                     val (testVar, cases, default) =
                        case transfer of
                           Case {test, cases = Cases.Con cases, default} =>
                              (test, cases, default)
                         | _ => escape ()
                     val (testIndex, testTy) =
                        case Vector.peeki (args, fn (_, (x, _)) => Var.equals (testVar, x)) of
                           SOME (i, (_, ty)) => (i, ty)
                         | NONE => Error.bug "splitEntries.testIndex_testTy"
                     val testTycon =
                        case Type.dest testTy of
                           Type.Datatype tycon => tycon
                         | _ => Error.bug "splitEntries.testTycon"
                     val nonTestArgs =
                        Vector.tabulate
                        (Vector.length args - 1, fn i =>
                         Vector.sub (args, if i < testIndex then i else i + 1))
                     val cons = #cons (tyconInfo testTycon)
                     val (newEntries, newBlocks) =
                        (Vector.unzip o Vector.map)
                        (cons, fn con =>
                         let
                            val newName =
                               FuncEntry.newString
                               (Con.originalName con)
                            val newConArgs =
                               Vector.map
                               (#args (conInfo con), fn ty =>
                                (Var.newNoname (), ty))
                            val (newConArgVars, _) =
                               Vector.unzip newConArgs
                            val newNonTestArgs =
                               Vector.map
                               (nonTestArgs, fn (x, ty) =>
                                (Var.new x, ty))
                            val newStart = Label.newNoname ()
                            val newEntry =
                               FunctionEntry.T
                               {name = newName,
                                args = Vector.concat [newConArgs, newNonTestArgs],
                                start = newStart}
                            val newStatements =
                               Vector.concat
                               [(Vector.new1 o Statement.T)
                                {var = SOME testVar,
                                 ty = testTy,
                                 exp = ConApp {con = con,
                                               args = newConArgVars}},
                                Vector.map2
                                (nonTestArgs, newNonTestArgs, fn ((x, ty), (x', _)) =>
                                 Statement.T
                                 {var = SOME x,
                                  ty = ty,
                                  exp = Var x'})]
                            val conDst =
                               Vector.peekMap
                               (cases, fn (con', dst') =>
                                if Con.equals (con, con')
                                   then SOME dst'
                                else NONE)
                            val newTransfer =
                               case (conDst, default) of
                                  (SOME dst, _) =>
                                     Goto {dst = dst,
                                           args = newConArgVars}
                                | (NONE, SOME dst) =>
                                     Goto {dst = dst,
                                           args = Vector.new0 ()}
                                | _ => Error.bug "SplitEntries.newTransfer"
                            val newBlock =
                               Block.T {label = newStart,
                                        args = Vector.new0 (),
                                        statements = newStatements,
                                        transfer = newTransfer}
                         in
                            (newEntry, newBlock)
                         end)
                     val newEntryNames = Vector.map (newEntries, FunctionEntry.name)
                     val () =
                        setEntryInfo
                        (name, SOME {testIndex = testIndex,
                                     newEntryNames = newEntryNames})
                     (* Diagnostics *)
                     val _ =
                        Control.diagnostics
                        (fn display =>
                         let open Layout
                         in
                            display (seq [FuncEntry.layout name, str " ",
                                          record [("testVar", Var.layout testVar),
                                                  ("testTy", Type.layout testTy),
                                                  ("testIndex", Int.layout testIndex)],
                                          str " ==> ",
                                          Vector.layout
                                          (fn (con, name) =>
                                           seq [Con.layout con,
                                                str " => ",
                                                FuncEntry.layout name])
                                          (Vector.zip (cons, newEntryNames))])
                         end)
                  in
                     (newEntries::newEntriess, newBlocks::newBlockss)
                  end))
          in
             (restore o Function.new)
             {blocks = Vector.concat (blocks::newBlockss),
              entries = Vector.concat (entries::newEntriess),
              mayInline = mayInline,
              name = name,
              raises = raises,
              returns = returns}
          end)
      val () =
         Control.diagnostics
         (fn display => display Layout.empty)
      val () =
         Vector.foreach
         (globals, fn Statement.T {var, exp, ...} =>
          case (var, exp) of
             (SOME x, ConApp {con, args}) =>
                setVarInfo (x, {conApp = SOME {con = con, args = args}})
           | (SOME x, _) =>
                setVarInfo (x, {conApp = NONE})
           | _ => ())
      val functions =
         List.map
         (functions, fn f =>
          let
             val {blocks, entries, mayInline, name, raises, returns} =
                Function.dest f
             val () =
                Vector.foreach
                (entries, fn FunctionEntry.T {args, ...} =>
                 let
                    val () =
                       Vector.foreach
                       (args, fn (x, _) =>
                        setVarInfo (x, {conApp = NONE}))
                 in
                    ()
                 end)
             val () =
                Vector.foreach
                (blocks, fn Block.T {args, statements, ...} =>
                 let
                    val () =
                       Vector.foreach
                       (args, fn (x, _) =>
                        setVarInfo (x, {conApp = NONE}))
                    val () =
                       Vector.foreach
                       (statements, fn Statement.T {var, exp, ...} =>
                        case (var, exp) of
                           (SOME x, ConApp {con, args}) =>
                              setVarInfo (x, {conApp = SOME {con = con, args = args}})
                         | (SOME x, _) =>
                              setVarInfo (x, {conApp = NONE})
                         | _ => ())
                 in
                    ()
                 end)
             val blocks =
                Vector.map
                (blocks, fn block as Block.T {label, args, statements, transfer} =>
                 Exn.withEscape
                 (fn escape =>
                  let
                     val escape = fn () =>
                        (ignore (escape block)
                         ; Error.bug "splitEntries.escape")
                     val newTransfer =
                        case transfer of
                           Call {func, entry, args, return} =>
                              let
                                 val (testIndex, newEntryNames) =
                                    case entryInfo entry of
                                       SOME {testIndex, newEntryNames} =>
                                          (testIndex, newEntryNames)
                                     | _ => escape ()
                                 val testVar = Vector.sub (args, testIndex)
                                 val (con, newConAppVars) =
                                    case #conApp (varInfo testVar) of
                                       SOME {con, args} => (con, args)
                                     | _ => escape ()
                                 val conIndex = #index (conInfo con)
                                 val nonTestVars =
                                    Vector.tabulate
                                    (Vector.length args - 1, fn i =>
                                     Vector.sub (args, if i < testIndex then i else i + 1))
                                 val newEntryName = Vector.sub (newEntryNames, conIndex)
                              in
                                 Call {func = func,
                                       entry = newEntryName,
                                       args = Vector.concat [newConAppVars, nonTestVars],
                                       return = return}
                              end
                         | _ => escape ()
                     val _ =
                        Control.diagnostics
                        (fn display =>
                         let open Layout
                         in
                            display (seq [Transfer.layout transfer,
                                          str " ==> ",
                                          Transfer.layout newTransfer])
                         end)
                  in
                     Block.T {label = label,
                              args = args,
                              statements = statements,
                              transfer = newTransfer}
                  end))
          in
             (shrink o Function.new)
             {blocks = blocks,
              entries = entries,
              mayInline = mayInline,
              name = name,
              raises = raises,
              returns = returns}
          end)
      val program = Program.T {datatypes = datatypes,
                               globals = globals,
                               functions = functions,
                               main = main}
      val _ = Program.clearTop program
   in
      program
   end
end
