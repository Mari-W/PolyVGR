module Equality where

import Ast
import Context
import Data.Bifunctor (Bifunctor (bimap))
import Data.Either (fromRight)
import Result

kEq :: Ctx -> Kind -> Kind -> Result ()
kEq ctx KType KType = ok ()
kEq ctx KSession KSession = ok ()
kEq ctx KState KState = ok ()
kEq ctx KShape KShape = ok ()
kEq ctx (KDom t) (KDom t') = tEq ctx t t'
kEq ctx (KLam k1 k1') (KLam k2 k2') = do
  kEq ctx k1 k2
  kEq ctx k1' k2'
kEq _ k k' = raise ("[K-Eq] kind mismatch between " ++ show k ++ " and " ++ show k')

kEqs :: Ctx -> Kind -> [Kind] -> Result ()
kEqs ctx k = mapM_ (kEq ctx k)

tNf :: Ctx -> Type -> Result Type
{- TC-TApp -}
tNf ctx (TApp (TLam s d t) t') = do
  ctx' <- (s, d) +. ctx
  tNf ctx' t'
{- TC-Proj -}
tNf ctx (DProj l (DMerge d d')) = case l of
  LLeft -> tNf ctx d
  LRight -> tNf ctx d'
{- TC-DualVar -}
tNf ctx (SDual (SDual (TVar i))) = ok (TVar i)
{- TC-DualEnd -}
tNf ctx (SDual SEnd) = ok SEnd
{- TC-DualSend -}
tNf ctx (SDual (SSend n sh st t s)) = do
  dual <- tNf ctx (SDual s)
  ok (SRecv n sh st t dual)
{- TC-DualRecv -}
tNf ctx (SDual (SRecv n sh st t s)) = do
  dual <- tNf ctx (SDual s)
  ok (SSend n sh st t dual)
{- TC-DualChoice -}
tNf ctx (SDual (SChoice st st')) = do
  dual <- tNf ctx (SDual st)
  dual' <- tNf ctx (SDual st')
  ok (SBranch dual dual')
{- TC-DualBranch -}
tNf ctx (SDual (SBranch st st')) = do
  dual <- tNf ctx (SDual st)
  dual' <- tNf ctx (SDual st')
  ok (SChoice dual dual')
{- recurse -}
tNf ctx (TLam s d t) = do
  d <- tNf ctx d
  t <- tNf ctx t
  ok (TLam s d t)
tNf ctx (EAll s k constrs t) = do
  {-TODO constrs <- sequence (map (sequence (bimap (tNf ctx) (tNf ctx))) constrs)-}
  t <- tNf ctx t
  ok (EAll s k constrs t)
tNf ctx (EArr s t s' t') = do
  s <- tNf ctx s
  t <- tNf ctx t
  s' <- tNf ctx s'
  t' <- tNf ctx t'
  ok (EArr s t s' t')
tNf ctx (EChan t) = do
  t <- tNf ctx t
  ok (EChan t)
tNf ctx (EAcc t) = do
  t <- tNf ctx t
  ok (EAcc t)
tNf ctx (EPair t t') = do
  t <- tNf ctx t
  t' <- tNf ctx t'
  ok (EPair t t')
tNf ctx (SSend n d s t t') = do
  d <- tNf ctx d
  s <- tNf ctx s
  t <- tNf ctx t
  t' <- tNf ctx t'
  ok (SSend n d s t t')
tNf ctx (SRecv n d s t t') = do
  d <- tNf ctx d
  s <- tNf ctx s
  t <- tNf ctx t
  t' <- tNf ctx t'
  ok (SRecv n d s t t')
tNf ctx (SChoice t t') = do
  t <- tNf ctx t
  t' <- tNf ctx t'
  ok (SChoice t t')
tNf ctx (SBranch t t') = do
  t <- tNf ctx t
  t' <- tNf ctx t'
  ok (SBranch t t')
tNf ctx (SDual t) = do
  t <- tNf ctx t
  ok (SDual t)
tNf ctx (DMerge d d') = do
  d <- tNf ctx d
  d' <- tNf ctx d'
  ok (DMerge d d')
tNf ctx (SSBind t t') = do
  t <- tNf ctx t
  t' <- tNf ctx t'
  ok (SSBind t t')
tNf ctx t = ok t

tEq :: Ctx -> Type -> Type -> Result ()
tEq ctx t t' = do 
  t <- tNf ctx t
  t' <- tNf ctx t'
  tEq' ctx t t'

tEq' :: Ctx -> Type -> Type -> Result ()
tEq' ctx (TVar a) (TVar b) = do 
  t <- a .? ctx
  t' <- b .? ctx 
  tEq' ctx t t'
tEq' ctx (TApp d c) (TApp d' c') = do 
  tEq' ctx d d'
  tEq' ctx c c'
tEq' ctx ..