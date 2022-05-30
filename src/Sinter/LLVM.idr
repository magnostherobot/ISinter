module Sinter.LLVM

import Data.Vect
import Data.List
import Libraries.Data.StringMap
import Control.Linear.LIO

import public LLVM
import Sinter.Sinter

Scope : Type
Scope = List (String, Value)

addToScope : Scope -> String -> Value -> Scope
addToScope xs n f = (n, f) :: xs

addArgsToScope : Scope -> List String -> Function -> Scope
addArgsToScope scope args f =
  let
    vs = zip args (map (getParam f) [0..(length args)])
  in
    foldl (uncurry . addToScope) scope vs

getFromScope : String -> Scope -> Maybe Value
getFromScope k [] = Nothing
getFromScope k ((n, f) :: xs) = if k == n
                                   then Just f
                                   else getFromScope k xs

record W where
 constructor MkW
 1 ctxt : Context
 1 mod : Module
 scope : Scope

record BodyContext where
  constructor MkBodyContext
  1 w : W
  func : Function

-- TODO could check boxing/unboxing at type level

boxT : Type'
boxT = pointerType (intType 8)

sizeT : Type'
sizeT = typeOf (sizeOf boxT)

gcType : LinearIO io => L io Type'
gcType = functionType boxT [sizeT] False

buildGCCall : LinearIO io => (1 b : BuilderAt bl) -> Scope ->
              Value -> String -> L1 io (BuildResultAt bl Value)
buildGCCall b scope arg name = do
  let Just gcFunc = getFromScope "gc_alloc" scope
    | Nothing => ?error3
  buildCall b !gcType (cast gcFunc) [arg] name

buildBox : LinearIO io => (1 b : BuilderAt bl) -> Scope -> Value -> Type' ->
           L1 io (BuildResultAt bl Value)
buildBox b scope unboxed unboxedT = do
  let size = sizeOf boxT
  Result b rawBox <- buildGCCall b scope size "boxed"
  Result b box <- buildPointerCast b rawBox (pointerType unboxedT) "box_uncast"
  Result b _ <- buildStore b unboxed box
  pure1 $ Result b rawBox

buildUnbox : LinearIO io => (1 b : BuilderAt bl) -> Value -> (width : Nat) ->
             L1 io (BuildResultAt bl Value)
buildUnbox b box w = do
  let newType = intType w
  let uncastBoxType = pointerType newType
  Result b uncast <- buildPointerCast b box uncastBoxType "uncast"
  buildLoad b newType uncast "unboxed"

func : LinearIO io => Nat -> L io Type'
func n =
  let args = replicate n boxT
  in  functionType boxT args False

data WWith : Type -> Type where
  WW : (1 w : W) -> a -> WWith a

getOrAdd : LinearIO io => String -> List String -> (1 w : W) ->
           L1 io (WWith Value)
getOrAdd k args (MkW ctxt mod scope) = case getFromScope k scope of
  Just x  => pure1 $ WW (MkW ctxt mod scope) x
  Nothing => do type <- func (length args)
                M mod f <- addFunction mod k type
                let v = cast f
                let scope = addToScope scope k v
                pure1 $ WW (MkW ctxt mod scope) v

record LDPair a where
  constructor P
  block : Block
  1 builder : BuilderAt block
  value : a

record LDCPair a where
  constructor C
  block : Block
  1 builder : BuilderAt block
  1 bc : BodyContext
  value : a

compileSinterBody' : LinearIO io =>
                     {bl : Block} ->
                     (1 builder : BuilderAt bl) ->
                     (1 ctxt : BodyContext) ->
                     Sinter ->
                     L1 io (LDCPair Value)

compileInt : (value : Integer) -> (width : Nat) -> Value
compileInt v w = constInt (intType w) v False

compileIntBoxed : LinearIO io =>
                  (1 b : BuilderAt bl) ->
                  Scope ->
                  (value : Integer) ->
                  (width : Nat) ->
                  L1 io (BuildResultAt bl Value)
compileIntBoxed b scope v w = do
  let int = compileInt v w
  buildBox b scope int (intType w)

compileString : LinearIO io =>
                (1 builder : BuilderAt bl) ->
                String ->
                L1 io (BuildResultAt bl Value)
compileString builder str = buildGlobalString builder str ""

compileIf : LinearIO io =>
            {start : Block} ->
            (1 builder : BuilderAt start) ->
            (1 ctxt : BodyContext) ->
            (cond, then', else' : Sinter) ->
            (width : Nat) ->
            L1 io (LDCPair Value)
compileIf b ctxt cond then' else' width = do
  let MkBodyContext w f = ctxt

  thenBlock <- appendBlock f "then"
  elseBlock <- appendBlock f "else"
  mergeBlock <- appendBlock f "merge"

  let ctxt = MkBodyContext w f

  C _ b ctxt condResult <- compileSinterBody' b ctxt cond
  Result b unboxed <- buildUnbox b condResult width
  Result b _ <- buildCondBr b unboxed thenBlock elseBlock

  b <- positionBuilderAtEnd b thenBlock
  C _ b ctxt thenResult <- compileSinterBody' b ctxt then'
  Result b _ <- buildBr b mergeBlock

  b <- positionBuilderAtEnd b elseBlock
  C _ b ctxt elseResult <- compileSinterBody' b ctxt else'
  Result b _ <- buildBr b mergeBlock

  b <- positionBuilderAtEnd b mergeBlock
  Result b phi <- buildPhi b boxT "merge_phi"
  addIncoming phi [(thenResult, thenBlock), (elseResult, elseBlock)]

  pure1 $ C mergeBlock b ctxt phi

compileLet : LinearIO io =>
             {bl : Block} ->
             (1 builder : BuilderAt bl) ->
             (1 ctxt : BodyContext) ->
             (new : String) ->
             (old : Sinter) ->
             (body : Sinter) ->
             L1 io (LDCPair Value)
compileLet b ctxt new old body = do
  C _ b ctxt oldResult <- compileSinterBody' b ctxt old
  let MkBodyContext (MkW c m scope) f = ctxt
  let scope = addToScope scope new oldResult
  let ctxt = MkBodyContext (MkW c m scope) f
  compileSinterBody' b ctxt body

compileCaseBranch : LinearIO io =>
                    {bl : Block} ->
                    (1 builder : BuilderAt bl) ->
                    (1 ctxt : BodyContext) ->
                    (switch : Value) ->
                    (footer : Block) ->
                    (match : Integer) ->
                    (branch : Sinter) ->
                    (width : Nat) ->
                    L1 io (LDCPair Value)
compileCaseBranch b ctxt switch footer match branch width = do
  let MkBodyContext w f = ctxt
  branchBlock <- appendBlock f "branch"
  let match' = compileInt match width
  addCase switch match' branchBlock
  b <- positionBuilderAtEnd b branchBlock
  let ctxt = MkBodyContext w f

  C block b ctxt branchResult <- compileSinterBody' b ctxt branch
  Result b _ <- buildBr b footer

  pure1 $ C block b ctxt branchResult

ccb : LinearIO io =>
      {bl : Block} ->
      (1 builder : BuilderAt bl) ->
      (1 ctxt : BodyContext) ->
      (switch : Value) ->
      (footer : Block) ->
      List (Integer, Sinter) ->
      List (Value, Block) ->
      (width : Nat) ->
      L1 io (LDCPair (List (Value, Block)))
ccb b ctxt switch footer [] acc w = pure1 $ C bl b ctxt acc
ccb b ctxt switch footer ((i, x) :: xs) acc w = do
  C block b ctxt v <- compileCaseBranch b ctxt switch footer i x w
  b <- positionBuilderAtEnd b bl
  ccb b ctxt switch footer xs ((v, block) :: acc) w

compileCaseBranches : LinearIO io =>
                      {bl : Block} ->
                      (1 builder : BuilderAt bl) ->
                      (1 ctxt : BodyContext) ->
                      (switch : Value) ->
                      (footer : Block) ->
                      (cases : List (Integer, Sinter)) ->
                      (width : Nat) ->
                      L1 io (LDCPair (List (Value, Block)))
compileCaseBranches b ctxt switch footer xs w =
  ccb b ctxt switch footer xs [] w

compileCase : LinearIO io =>
              {bl : Block} ->
              (1 builder : BuilderAt bl) ->
              (1 ctxt : BodyContext) ->
              (val : Sinter) ->
              (cases : List (Integer, Sinter)) ->
              (else' : Sinter) ->
              (width : Nat) ->
              L1 io (LDCPair Value)
compileCase b ctxt val cases else' width = do
  C bl' b ctxt valResult <- compileSinterBody' b ctxt val
  Result b unboxed <- buildUnbox b valResult width

  let MkBodyContext w f = ctxt
  elseBlock <- appendBlock f "else"
  mergeBlock <- appendBlock f "merge"
  let ctxt = MkBodyContext w f
  b <- positionBuilderAtEnd b elseBlock
  C elseEnd b ctxt elseResult <- compileSinterBody' b ctxt else'
  Result b _ <- buildBr b mergeBlock

  b <- positionBuilderAtEnd b bl'
  Result b switch <- buildSwitch b unboxed elseBlock (length cases)

  C _ b ctxt vsbs <- compileCaseBranches b ctxt switch mergeBlock cases width
  let vsbs = (elseResult, elseEnd) :: vsbs

  b <- positionBuilderAtEnd b mergeBlock
  Result b phi <- buildPhiWithIncoming b boxT (fromList vsbs) ""
  pure1 $ C mergeBlock b ctxt phi

ca : LinearIO io =>
     {bl : Block} ->
     (1 builder : BuilderAt bl) ->
     (1 ctxt : BodyContext) ->
     List Sinter ->
     List Value ->
     L1 io (LDCPair (List Value))
ca b ctxt [] acc = pure1 $ C bl b ctxt acc
ca b ctxt (x :: xs) acc = do
  C block b ctxt v <- compileSinterBody' b ctxt x
  ca b ctxt xs (v :: acc)

compileArgs : LinearIO io =>
              {bl : Block} ->
              (1 builder : BuilderAt bl) ->
              (1 ctxt : BodyContext) ->
              List Sinter ->
              L1 io (LDCPair (List Value))
compileArgs b ctxt xs = ca b ctxt xs []

compileCall : LinearIO io =>
              {bl : Block} ->
              (1 builder : BuilderAt bl) ->
              (1 ctxt : BodyContext) ->
              (fsin : Sinter) ->
              (args : List Sinter) ->
              L1 io (LDCPair Value)
compileCall b ctxt fsin args = do
  C block b ctxt f <- compileSinterBody' b ctxt fsin
  C block b ctxt args' <- compileArgs b ctxt args
  t <- func (length args)
  Result b v <- buildCall b t (cast f) (fromList args') ""
  pure1 $ C block b ctxt v

compileSinterBody' b ctxt (SID n) = do
  let MkBodyContext (MkW c m scope) f = ctxt
  let Just v = getFromScope n scope
    | Nothing => ?error2
  let ctxt = MkBodyContext (MkW c m scope) f
  pure1 $ C bl b ctxt v

compileSinterBody' b ctxt (SInt v w) = do
  let MkBodyContext (MkW c m scope) f = ctxt
  Result b res <- compileIntBoxed b scope v w
  let ctxt = MkBodyContext (MkW c m scope) f
  pure1 $ C bl b ctxt res

compileSinterBody' b ctxt (SStr str) = do
  Result b x <- compileString b str
  pure1 $ C bl b ctxt x

compileSinterBody' b ctxt (SIf cond then' else' w) =
  compileIf b ctxt cond then' else' w

compileSinterBody' b ctxt (SLet new old body) =
  compileLet b ctxt new old body

compileSinterBody' b ctxt (SCase val cases else' w) =
  compileCase b ctxt val cases else' w

compileSinterBody' b ctxt (SCall f args) =
  compileCall b ctxt f args

record BlockBuilderAndW where
  constructor BlBuW
  mblock : Maybe Block
  1 builder : Builder mblock
  1 w : W

compileDef : {mb : Maybe Block} ->
             LinearIO io =>
             (1 b : Builder mb) ->
             (1 w : W) ->
             String ->
             List String ->
             Sinter ->
             L1 io BlockBuilderAndW
compileDef b w name args body = do
  WW (MkW c m scope) f <- getOrAdd name args w
  let f = cast f
  let innerScope = addArgsToScope scope args f
  let ctxt = MkBodyContext (MkW c m innerScope) f
  bl' <- appendBlock f "entry"
  b <- positionBuilderAtEnd b bl'
  C bl'' b (MkBodyContext (MkW c m _) f) res <- compileSinterBody' b ctxt body
  Result b () <- buildRet b res
  pure1 (BlBuW (Just bl'') b (MkW c m scope))

compileDec : LinearIO io =>
             (1 w : W) ->
             String ->
             List String ->
             L1 io W
compileDec w name args = do
  WW w _ <- getOrAdd name args w
  pure1 w

foldlM : LinearIO io =>
         ((1 _ : acc) -> e -> L1 io acc) ->
         (1 _ : acc) ->
         List e ->
         L1 io acc
foldlM f a [] = pure1 a
foldlM f a (x :: xs) = do a <- f a x
                          foldlM f a xs

addStruct : LinearIO io =>
            (1 w : W) ->
            String ->
            List String ->
            L1 io (WWith Type')
addStruct (MkW ctxt mod scope) name members = do
  let n = length members
  ctxt <# type <- structCreateNamed ctxt name
  structSetBody type (replicate n boxT) False
  pure1 $ WW (MkW ctxt mod scope) type

constructorFill : LinearIO io =>
                  (space : Value) ->
                  (type : Type') ->
                  (f : Function) ->
                  (1 b : BuilderAt bl) ->
                  (i : Nat) ->
                  L1 io (BuilderAt bl)
constructorFill space type f b i = do
  Result b pos <- buildStructGEP b type space i "pos"
  let param = getParam f i
  Result b _ <- buildStore b param pos
  pure1 b

constructorFills : LinearIO io =>
                   (1 b : BuilderAt bl) ->
                   (space : Value) ->
                   (type : Type') ->
                   (f : Function) ->
                   (n : Nat) ->
                   L1 io (BuilderAt bl)
constructorFills b space type f Z = pure1 b
constructorFills b space type f (S k) =
  foldlM (constructorFill space type f) b [0..k]

addConstructor : LinearIO io =>
                 {mb : Maybe Block} ->
                 (1 b : Builder mb) ->
                 (1 w : W) ->
                 String ->
                 List String ->
                 Type' ->
                 L1 io BlockBuilderAndW
addConstructor b (MkW ctxt mod scope) name members struct = do
  let n = length members
  type <- func n
  M mod f <- addFunction mod name type
  let scope = addToScope scope name (cast f)
  bl <- appendBlock f "main"
  b <- positionBuilderAtEnd b bl
  Result b space <- buildGCCall b scope (sizeOf struct) "space"
  let structPtr = pointerType struct
  Result b spaceCast <- buildPointerCast b space structPtr "space_cast"
  b <- constructorFills b spaceCast struct f n
  Result b () <- buildRet b space
  pure1 (BlBuW (Just bl) b (MkW ctxt mod scope))

addArgAccess : LinearIO io =>
               {mb : Maybe Block} ->
               (1 b : Builder mb) ->
               (1 w : W) ->
               (structName : String) ->
               (struct : Type') ->
               (member : String) ->
               (n : Nat) ->
               L1 io BlockBuilderAndW
addArgAccess b (MkW ctxt mod scope) structName struct member n = do
  let name = structName ++ "." ++ member
  type <- func 1
  M mod f <- addFunction mod name type
  let scope = addToScope scope name (cast f)
  bl <- appendBlock f "main"
  b <- positionBuilderAtEnd b bl

  let param = getParam f 0
  Result b space <- buildPointerCast b param (pointerType struct) "uncast"
  Result b ptr <- buildStructGEP b struct space n "member"
  Result b v <- buildLoad b boxT ptr "deref"
  Result b () <- buildRet b v

  pure1 (BlBuW (Just bl) b (MkW ctxt mod scope))

addArgAccesses : LinearIO io =>
                 {mb : Maybe Block} ->
                 (1 b : Builder mb) ->
                 (1 w : W) ->
                 (name : String) ->
                 (members : List String) ->
                 (struct : Type') ->
                 L1 io BlockBuilderAndW
addArgAccesses b w name members struct =
  case length members of
       Z => pure1 (BlBuW mb b w)
       S k => foldlM (\(BlBuW _ b w), (n, i) =>
             addArgAccess b w name struct n i)
         (BlBuW mb b w) (zip members [0..k])

compileType : LinearIO io =>
              {mb : Maybe Block} ->
              (1 b : Builder mb) ->
              (1 w : W) ->
              String ->
              List String ->
              L1 io BlockBuilderAndW
compileType b w name args = do
  WW w struct <- addStruct w name args
  BlBuW _ b w <- addConstructor b w name args struct
  addArgAccesses b w name args struct

compileSin : LinearIO io =>
             {mb : Maybe Block} ->
             (1 b : Builder mb) ->
             (1 w : W) ->
             SinterTL ->
             L1 io BlockBuilderAndW
compileSin b w (SDef name args body) = compileDef b w name args body
compileSin b w (SDec name args) = pure1 $ BlBuW mb b !(compileDec w name args)
compileSin b w (STyp name mems) = compileType b w name mems

compileSins : LinearIO io =>
              {mb : Maybe Block} ->
              (1 b : Builder mb) ->
              (1 w : W) ->
              List SinterTL ->
              L1 io BlockBuilderAndW
compileSins b w [] = pure1 $ BlBuW mb b w
compileSins b w (x :: xs) = do BlBuW mb b w <- compileSin b w x
                               compileSins b w xs

public export
mkW : LinearIO io => L1 io W
mkW = do ctxt <- contextCreate
         (ctxt # mod) <- createModuleWithName "" ctxt
         type <- gcType
         M mod f <- addFunction mod "gc_alloc" type
         let scope = [("gc_alloc", cast f)]
         let w = MkW ctxt mod scope
         pure1 w

public export
compile : LinearIO io => List SinterTL -> L1 io Module
compile sins = do b <- createBuilder
                  w <- mkW
                  BlBuW _ b (MkW ctxt mod _) <- compileSins b w sins
                  disposeBuilder b
                  let (MkCtxt c) = ctxt
                  -- contextDispose ctxt
                  pure1 mod

public export
showModule : LinearIO io => (1 mod : Module) -> L io String
showModule = printModuleToString'
