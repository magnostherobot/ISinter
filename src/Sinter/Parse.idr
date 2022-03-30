module Sinter.Parse

import Data.List

import Sinter.Sexpr

public export
data Sinter = SInt Integer Nat
            | SStr String
            | SIf Sinter Sinter Sinter Nat
            | SLet String Sinter Sinter
            | SCase Sinter (List (Integer, Sinter)) Sinter Nat
            | SCall String (List Sinter)

public export
covering
Show Sinter where
  show (SInt v w) =
    concat [show v, "u", show w]
  show (SStr x) =
    concat [show x, "s"]
  show (SIf x y z w) =
    concat ["if ", show w, " {", show x, "} then {", show y,
             "} else {", show z, "}"]
  show (SLet x y z) =
    concat ["let {", show x, "} be {", show y, "} in {", show z, "}"]
  show (SCase x xs y k) =
    concat ["case ", show k, " {", show x, "} of {",
             show xs, "} default {", show y, "}"]
  show (SCall x xs) =
    concat ["call {", x, "} args {", show xs, "}"]

genList : List Sexpr -> Sexpr
genList = foldr Branch SNil

SexprNat : Nat -> Sexpr
SexprNat = SexprInt . natToInteger

mutual

  genCase : (Integer, Sinter) -> Sexpr
  genCase (i, e) = Branch (SexprInt i) (gen e)

  public export
  gen : Sinter -> Sexpr
  gen (SInt v w) =
    (Branch (SexprNat w) (SexprInt v))
  gen (SStr x) =
    SexprString x
  gen (SIf x y z w) =
    genList [SexprID "if", gen x, gen y, gen z, SexprNat w]
  gen (SLet x y z) =
    genList [SexprID "let", Branch (SexprID x) (gen y), gen z]
  gen (SCase x xs y w) =
    genList [SexprID "case", gen x, genList $ map genCase xs, gen y, SexprNat w]
  gen (SCall x xs) =
    genList (SexprID x :: map gen xs)

sid : Sexpr -> Maybe String
sid (SexprID x) = Just x
sid _ = Nothing

sstr : Sexpr -> Maybe String
sstr (SexprString x) = Just x
sstr _ = Nothing

sint : Sexpr -> Maybe Integer
sint (SexprInt i) = Just i
sint _ = Nothing

snat : Sexpr -> Maybe Nat
snat s = do x <- sint s
            case compare x 0 of
                 LT => Nothing
                 _  => pure $ cast x

b : (Sexpr -> Maybe a) -> (Sexpr -> Maybe b) -> (Sexpr -> Maybe (a, b))
b f g (Branch l r) = do l' <- f l
                        r' <- g r
                        pure (l', r')
b _ _ _ = Nothing

add : a -> (List a, b) -> (List a, b)
add x (xs, y) = (x :: xs, y)

bs : (Sexpr -> Maybe a) -> Sexpr -> (List a, Sexpr)
bs f x = case b f Just x of
              Just (v, y) => add v $ bs f y
              Nothing => ([], x)

list : (Sexpr -> Maybe a) -> Sexpr -> Maybe (List a)
list f x = case bs f x of
                (y, SNil) => Just y
                _ => Nothing

mutual

  cond : Sexpr -> Maybe Sinter
  cond s = do [SexprID "if", c, t, e, w] <- list Just s
                | _ => empty
              c' <- parseBody c
              t' <- parseBody t
              e' <- parseBody e
              w' <- snat w
              pure $ SIf c' t' e' w'
  
  bind : Sexpr -> Maybe Sinter
  bind s = do [SexprID "let", x, y] <- list Just s
                | _ => empty
              (n, e) <- b sid parseBody x
              y' <- parseBody y
              pure $ SLet n e y'
  
  case' : Sexpr -> Maybe Sinter
  case' s = do [SexprID "case", x, cs, d, w] <- list Just s
                 | _ => empty
               x'  <- parseBody x
               cs' <- list (b sint parseBody) cs
               d'  <- parseBody d
               w'  <- snat w
               pure $ SCase x' cs' d' w'
  
  call : Sexpr -> Maybe Sinter
  call s = do (n, ns) <- b sid (list parseBody) s
              pure $ SCall n ns
  
  intlit : Sexpr -> Maybe Sinter
  intlit s = do (w, v) <- b snat sint s
                pure $ SInt v w
  
  strlit : Sexpr -> Maybe Sinter
  strlit s = sstr s >>= pure . SStr
  
  parseBody : Sexpr -> Maybe Sinter
  parseBody x =  cond x
             <|> case' x
             <|> bind x
             <|> call x
             <|> intlit x
             <|> strlit x

public export
data SinterTL = SDef String (List String) Sinter
              | SDec String (List String)
              | STyp String (List String)

public export
covering
Show SinterTL where
  show (SDef x xs y) =
    concat ["def {", x, "} args {", show xs, "} as {", show y, "}"]
  show (SDec x xs) =
    concat ["dec {", x, "} args {", show xs, "}"]
  show (STyp x xs) =
    concat ["type {", x, "} members {", show xs, "}"]

public export
genTL : SinterTL -> Sexpr
genTL (SDef x xs y) =
  genList [SexprID "def", SexprID x, genList $ map SexprID xs, gen y]
genTL (SDec x xs) =
  genList [SexprID "dec", SexprID x, genList $ map SexprID xs]
genTL (STyp x xs) =
  genList [SexprID "type", SexprID x, genList $ map SexprID xs]

def : Sexpr -> Maybe SinterTL
def s = do [SexprID "def", n, ns, x] <- list Just s
             | _ => empty
           n'  <- sid n
           ns' <- list sid ns
           x'  <- parseBody x
           pure $ SDef n' ns' x'

dec : Sexpr -> Maybe SinterTL
dec s = do [SexprID "dec", n, ns] <- list Just s
             | _ => empty
           n'  <- sid n
           ns' <- list sid ns
           pure $ SDec n' ns'

typ : Sexpr -> Maybe SinterTL
typ s = do [SexprID "type", n, ns] <- list Just s
             | _ => empty
           n'  <- sid n
           ns' <- list sid ns
           pure $ STyp n' ns'

public export
sexprToSinter : Sexpr -> Maybe SinterTL
sexprToSinter s = def s <|> dec s <|> typ s
