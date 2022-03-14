module Sexpr

import Lex

import Text.Parser

public export
data Sexpr = SexprID String | SexprInt Integer
           | SexprString String | Branch Sexpr Sexpr
           | SNil

Show Sexpr where
  show (SexprID x) = x
  show (SexprInt x) = show x
  show (SexprString x) = show x
  show (Branch x y) = "(" ++ show x ++ " " ++ show y ++ ")"
  show SNil = "()"

lParen : Grammar _ SinToken True ()
lParen = terminal "Expected '('" (\case LParen => Just ()
                                        _ => Nothing)

rParen : Grammar _ SinToken True ()
rParen = terminal "Expected ')'" (\case RParen => Just ()
                                        _ => Nothing)

lBracket : Grammar _ SinToken ? ()
lBracket = terminal "Expected '['" (\case LBracket => Just ()
                                          _ => Nothing)

rBracket : Grammar _ SinToken ? ()
rBracket = terminal "Expected ']'" (\case RBracket => Just ()
                                          _ => Nothing)

sid : Grammar _ SinToken ? Sexpr
sid = terminal "Not an ID"
        (\case (SID str) => Just (SexprID str)
               _ => Nothing)

sint : Grammar _ SinToken ? Sexpr
sint = terminal "Not an integer"
         (\case (SInt i) => Just (SexprInt i)
                _ => Nothing)

snil : Grammar _ SinToken True Sexpr
snil = terminal "Not a nil"
         (\case Nil => Just SNil
                _ => Nothing)

sstring : Grammar _ SinToken ? Sexpr
sstring = terminal "Not a string"
            (\case (SString str) => Just (SexprString str)
                   _ => Nothing)

branches : List Sexpr -> Sexpr
branches [] = SNil
branches (x :: xs) = Branch x (branches xs)

mutual

  parenExpr : Grammar _ SinToken True Sexpr
  parenExpr = do lParen
                 lhs <- sexpr
                 rhs <- sexpr
                 rParen
                 pure (Branch lhs rhs)

  listExpr : Grammar _ SinToken True Sexpr
  listExpr = do lBracket
                exprs <- many sexpr
                rBracket
                pure (branches exprs)

  sexpr : Grammar _ SinToken True Sexpr
  sexpr =  sint
       <|> sid
       <|> sstring
       <|> snil
       <|> parenExpr
       <|> listExpr

public export
tokensToSexpr : List (WithBounds SinToken) -> Either ? ?
tokensToSexpr = parse sexpr

public export
stringToSexpr : String -> Maybe Sexpr
stringToSexpr x = do let (toks, _) = lex x
                     let Right (e, _) = tokensToSexpr toks
                       | Left _ => empty
                     pure e

FromString (Maybe Sexpr) where
  fromString = stringToSexpr
