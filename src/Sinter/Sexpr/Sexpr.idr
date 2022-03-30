module Sinter.Sexpr.Sexpr

public export
data Sexpr = SexprID String | SexprInt Integer
           | SexprString String | Branch Sexpr Sexpr
           | SNil

public export
Show Sexpr where
  show (SexprID x) = x
  show (SexprInt x) = show x
  show (SexprString x) = show x
  show (Branch x y) = "(" ++ show x ++ " " ++ show y ++ ")"
  show SNil = "()"
