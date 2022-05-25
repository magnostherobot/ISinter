module Sinter.Sinter

public export
data Sinter = SInt Integer Nat
            | SStr String
            | SID String
            | SIf Sinter Sinter Sinter Nat
            | SLet String Sinter Sinter
            | SCase Sinter (List (Integer, Sinter)) Sinter Nat
            | SCall Sinter (List Sinter)

public export
covering
Show Sinter where
  show (SID n) = n
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
    concat ["call {", show x, "} args {", show xs, "}"]

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
