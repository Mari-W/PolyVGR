module Kinding where

import Ast (Dom (DEmpty, DProj, DTree, DVar), ExprType (ETAccess, ETArr, ETChan, ETForAll, ETPair, ETUnit, ETVar), Kind (KDom, KLam, KSession, KShape, KState, KType), Label (LLeft, LRight), Session (SBranch, SChoice, SDual, SEnd, SRecv, SSend, SVar), Shape (SDisjoint, SEmpty, SSingle), State (SSEmpty, SSMap, SSTree), Type (TApp, TDom, TExpr, TLam, TSess, TState, TVar))
import Constraints (constrWellFormed, constrWellFormed')
import Context (Ctx, Has (HasKind, HasType, HasConstr), typeAbsSafe)
import Equality (kindEq)
import Result (Result, ok, raise, todo)


typeWellFormed :: Ctx -> Type -> Result Kind
{- K-Var -}
typeWellFormed ctx (TVar i) = case ctx !! i of
  HasKind k -> ok k
  _ -> raise "[K-Var] expected variable i to have a kind"
{- K-App -}
typeWellFormed ctx (TApp t t') = do
  k <- typeWellFormed ctx t
  k' <- typeWellFormed ctx t'
  case k of
    KLam f t -> do
      kindEq f k'
      ok t
    _ -> raise "[K-App] expected abstraction to apply to"
{- K-Lam -}
typeWellFormed ctx (TLam s t) = do
  k <- typeWellFormed (HasKind (KDom s) : typeAbsSafe ctx) t
  case kindEq k KType of
    Left str -> raise str
    Right _ -> kindEq k KState
  ok (KLam (KDom s) k)
typeWellFormed ctx (TExpr e) = do
  typeExprWellFormed ctx e
  ok KType
typeWellFormed ctx (TSess s) = do
  typeSessWellFormed ctx s
  ok KSession
typeWellFormed ctx (TDom d) = do
  s <- typeDomWellFormed ctx d
  ok (KDom s)
typeWellFormed ctx (TState s) = do
  s <- typeStateWellFormed ctx s
  ok KState

typeVarWellFormed :: Ctx -> Int -> Result Kind
typeVarWellFormed ctx i = typeWellFormed ctx (TVar i)

typeExprWellFormed :: Ctx -> ExprType -> Result ()
{- K-Var -}
typeExprWellFormed ctx (ETVar i) = do
  k <- typeVarWellFormed ctx i
  kindEq k KType 
{- K-All -}
typeExprWellFormed ctx (ETForAll k c t) = do
  let ctx' = HasKind k : (map HasConstr c ++ ctx)
  typeExprWellFormed ctx' t
{- K-Arr -}
typeExprWellFormed ctx (ETArr (s, e) (s', e')) = todo {- disjointness -}
{- K-Chan -}
typeExprWellFormed ctx (ETChan d) = do
  sh <- typeDomWellFormed ctx d
  case sh of
    SSingle -> ok ()
    _ -> raise "[K-Chan] expected shape of single channel for domain"
{- K-AccessPoint -}
typeExprWellFormed ctx (ETAccess a) = typeSessWellFormed ctx a
{- K-Unit -}
typeExprWellFormed ctx ETUnit = ok ()
{- K-Pair -}
typeExprWellFormed ctx (ETPair e e') = do
  typeExprWellFormed ctx e
  typeExprWellFormed ctx e'

typeSessWellFormed :: Ctx -> Session -> Result ()
{- K-Var -}
typeSessWellFormed ctx (SVar i) = do
  k <- typeVarWellFormed ctx i
  kindEq k KSession
{- K-Send -}
typeSessWellFormed ctx (SSend sh st e s) = do
  typeSessWellFormed ctx s
  let ctx = HasKind (KDom sh) : typeAbsSafe ctx
  typeStateWellFormed ctx st
  typeExprWellFormed ctx e
{- K-Recv -}
typeSessWellFormed ctx (SRecv sh st e s) = do
  typeSessWellFormed ctx s
  let ctx' = HasKind (KDom sh) : typeAbsSafe ctx
  typeStateWellFormed ctx' st
  typeExprWellFormed ctx' e
{- K-Branch -}
typeSessWellFormed ctx (SBranch s s') = do
  typeSessWellFormed ctx s
  typeSessWellFormed ctx s'
{- K-Choice -}
typeSessWellFormed ctx (SChoice s s') = do
  typeSessWellFormed ctx s
  typeSessWellFormed ctx s'
{- K-End -}
typeSessWellFormed ctx SEnd = ok ()
{- K-Dual -}
typeSessWellFormed ctx (SDual s) = typeSessWellFormed ctx s

typeDomWellFormed :: Ctx -> Dom -> Result Shape
{- K-Var -}
typeDomWellFormed ctx (DVar i) = do
  k <- typeVarWellFormed ctx i
  kindEq k (KDom SSingle)
  ok SSingle
{- K-DomEmpty -}
typeDomWellFormed ctx DEmpty = ok SEmpty
{- K-DomProj -}
typeDomWellFormed ctx (DProj l d) = do
  s <- typeDomWellFormed ctx d
  case s of
    SDisjoint sh sh' -> case l of
      LLeft -> ok sh
      LRight -> ok sh'
    _ -> raise "[K-DomProj] expected tree like shape when projecting out domain"
{- K-DomMerge -}
typeDomWellFormed ctx (DTree d d') = do
  sh <- typeDomWellFormed ctx d
  sh' <- typeDomWellFormed ctx d'
  constrWellFormed ctx (d, d')
  ok (SDisjoint sh sh')

typeStateWellFormed :: Ctx -> State -> Result ()
{- K-StEmpty -}
typeStateWellFormed ctx SSEmpty = ok ()
{- K-StChan -}
typeStateWellFormed ctx (SSMap d s) = do
  typeSessWellFormed ctx s
  sh <- typeDomWellFormed ctx d
  case sh of
    SSingle -> ok ()
    _ -> raise "[K-StChan] expected domain of single channel when mapping channel to session type"
{- K-StMerge -}
typeStateWellFormed ctx (SSTree st st') = do
  typeStateWellFormed ctx st
  typeStateWellFormed ctx st
  constrWellFormed' ctx (st, st')
  ok ()
