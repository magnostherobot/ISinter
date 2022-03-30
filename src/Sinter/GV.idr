module Sinter.GV

import Sinter.Sexpr

GraphID = String

data NodeID : Type where
  First : NodeID
  Next : NodeID -> NodeID

toNat : NodeID -> Nat
toNat First = Z
toNat (Next n) = S (toNat n)

Show NodeID where
  show n = show $ show $ toNat n

data Attr : Type where
  MkAttr : (k : String) ->
           (v : String) ->
           Attr

data Statement : Type where
  MkEdge : (l : NodeID) ->
           (r : NodeID) ->
           (lArrow : Bool) ->
           (rArrow : Bool) ->
           Statement
  MkNode : (id' : NodeID) ->
           (attrs : List Attr) ->
           Statement

public export
data Graph : Type where
  MkGraph : (strict : Bool) ->
            (directed : Bool) ->
            (id' : Maybe GraphID) ->
            (stmts : List Statement) ->
            Graph

arrow : Bool -> Bool -> String
arrow False False = "-"
arrow False True  = "->"
arrow True  False = "<-"
arrow True  True  = "<->"

join : Show s => String -> List s -> String
join sep [] = ""
join sep (x :: []) = show x
join sep (x :: xs) = show x ++ sep ++ join sep xs

public export
Show Attr where
  show (MkAttr k v) = show k ++ "=" ++ show v

public export
Show Statement where
  show (MkEdge l r la lr) =
    concat [ show l, arrow la lr, show r, ";" ]
  show (MkNode n attrs) =
    concat [ show n, "[", join ", " attrs, "];" ]

public export
Show Graph where
  show (MkGraph strict directed id' stmts) =
    let
      strict' = if strict then "strict " else ""
      di = if directed then "digraph" else "graph"
      stmts' = join "\n" stmts
    in
      concat [ strict', di, " {", stmts', "\n}" ]

firstID : NodeID
firstID = First

newID : {auto id' : NodeID} -> NodeID
newID {id' = n} = Next n

node : {auto lid : NodeID} -> String -> (List Statement, NodeID)
node label =
  let id' = newID
  in  ([ MkNode id' [ MkAttr "label" label ] ], id')

gvStatements : Sexpr -> NodeID -> (List Statement, NodeID)
gvStatements (SexprID n) id' = node n
gvStatements (SexprInt i) id' = node (show i)
gvStatements (SexprString s) id' = node (show s)
gvStatements SNil id' = node "()"
gvStatements (Branch x y) id' =
  let
    (xs, xid) = gvStatements x id'
    (ys, yid) = gvStatements y xid
    (bs, bid) = node "" {lid = yid}
    es = [ MkEdge bid xid False True
         , MkEdge bid yid False True
         ]
  in
    (xs ++ ys ++ bs ++ es, bid)

public export
asGV : Sexpr -> Graph
asGV x =
  let (stmts, _) = gvStatements x firstID
  in  MkGraph False True Nothing stmts
