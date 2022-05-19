module Sinter

import Text.Parser

import System.File
import System

import Sinter.Sexpr
import Sinter.Parse
import Sinter.GV

mmap : Monad m => (a -> m b) -> List a -> m (List b)
mmap f [] = pure []
mmap f (x :: xs) = pure $ !(f x) :: !(mmap f xs)

public export
parse : String -> Maybe (List SinterTL)
parse x = do let (toks, _) = lex x
             let Right (s, _) = tokensToSexprs toks
               | Left _ => empty
             mmap sexprToSinter s

public export
gv : Sinter -> Graph
gv = asGV . gen

public export
gvtl : SinterTL -> Graph
gvtl = asGV . genTL

data Output = Sinter | Sexpr | LLVM | GV

arg : String -> Maybe Output
arg "sinter" = Just Sinter
arg "sexpr" = Just Sexpr
arg "llvm" = Just LLVM
arg "gv" = Just GV
arg _ = Nothing

usage : IO a
usage = die "usage text here"

unknown : String -> IO a
unknown x = do putStrLn ("unknown argument " ++ x)
               usage

readArgs : IO Output
readArgs = do [exec, out] <- getArgs
                | _ => usage
              maybe (unknown out) pure (arg out)

as : Output -> SinterTL -> String
as Sinter = show
as Sexpr = show . genTL
as LLVM = ?as_rhs_2
as GV = show . gvtl

forEach : Monad m => Foldable t => (a -> m ()) -> t a -> m ()
forEach f xs = foldlM (\() => f) () xs

main : IO ()
main = do out <- readArgs
          Right contents <- fRead stdin
            | Left err => printLn err
          let Just sinters = parse contents
            | x => putStrLn "parse error"
          forEach (putStrLn . as out) sinters
