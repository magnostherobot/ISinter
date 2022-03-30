module Sinter.Sexpr.Lex

import Data.List

import Text.Lexer

public export
data SinToken = LParen | RParen
              | LBracket | RBracket
              | Semicolon
              | SString String
              | SID String
              | SInt Integer
              | Whitespace
              | Nil

export
Show SinToken where
  show LParen = "("
  show RParen = ")"
  show LBracket = "["
  show RBracket = "]"
  show Semicolon = ";"
  show (SString val) = show val
  show (SID n) = n
  show (SInt i) = show i
  show Whitespace = " "
  show Nil = "()"

sid : Lexer
sid =
  let
    sidFront = alpha <|> oneOf "-_+*^!:/%.=<>"
    sidRest  = digit <|> sidFront
  in sidFront <+> many sidRest

sint : Lexer
sint = opt (oneOf "-+") <+> digits

tokenMap : TokenMap SinToken
tokenMap = [ (sid, SID)
           , (sint, SInt . cast)
           , (spaces, const Whitespace)
           , (exact "()", const Nil)
           , (is '(', const LParen)
           , (is ')', const RParen)
           , (is '[', const LBracket)
           , (is ']', const RBracket)
           , (is ';', const Semicolon)
           ]

relevant : WithBounds SinToken -> Bool
relevant (MkBounded Whitespace _ _) = False
relevant (MkBounded Semicolon  _ _) = False
relevant _ = True

LexT : Type
LexT = (List (WithBounds SinToken), (Int, Int, String))

clean : LexT -> LexT
clean (tokens, inputRemainder) = (filter relevant tokens, inputRemainder)

export
lex : String -> (List (WithBounds SinToken), (Int, Int, String))
lex = clean . lex tokenMap
