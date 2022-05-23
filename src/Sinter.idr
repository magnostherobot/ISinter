module Sinter

import Text.Parser

import System.File
import System

import Control.Linear.LIO

import Sinter.Sexpr
import Sinter.Parse
import Sinter.GV
import Sinter.LLVM

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

usage : HasIO io => io a
usage = die "usage text here"

unknown : HasIO io => String -> io a
unknown x = do putStrLn ("unknown argument " ++ x)
               usage

readArgs : HasIO io => io Output
readArgs = do [exec, out] <- getArgs
                | _ => usage
              maybe (unknown out) pure (arg out)

as : LinearIO io => Output -> SinterTL -> L io String
as Sinter = pure . show
as Sexpr = pure . show . genTL
as LLVM = \x => compile [x] >>= showModule
as GV = pure . show . gvtl

forEach : Monad m => Foldable t => (a -> m ()) -> t a -> m ()
forEach f xs = foldlM (\() => f) () xs

mainL : L IO ()
mainL = do out <- readArgs
           Right contents <- fRead stdin
           | Left err => printLn err
           let Just sinters = parse contents
           | x => putStrLn "parse error"
           forEach (\x => as out x >>= putStrLn) sinters

main : IO ()
main = run mainL
