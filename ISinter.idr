module ISinter

import Text.Parser

import Lex
import Sexpr
import Sinter

public export
parse : String -> Maybe SinterTL
parse x = do let (toks, _) = lex x
             let Right (s, _) = tokensToSexpr toks
               | Left _ => empty
             sin <- sexprToSinter s
             pure sin

main : IO ()
main = do line <- getLine
          printLn $ parse line
          main
