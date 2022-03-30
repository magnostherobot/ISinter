module Sinter

import Text.Parser

import System.File

import Sinter.Sexpr
import Sinter.Parse
import Sinter.GV

public export
parse : String -> Maybe SinterTL
parse x = do let (toks, _) = lex x
             let Right (s, _) = tokensToSexpr toks
               | Left _ => empty
             sin <- sexprToSinter s
             pure sin

public export
gv : Sinter -> Graph
gv = asGV . gen

public export
gvtl : SinterTL -> Graph
gvtl = asGV . genTL

main : IO ()
main = do Right contents <- fRead stdin
            | Left err => printLn err
          let Just sinter = parse contents
            | x => printLn x
          printLn sinter
          printLn $ gvtl sinter
