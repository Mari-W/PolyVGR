module Equality where

import Ast
import Context
import Data.Bifunctor (Bifunctor (bimap))
import Result
import Data.Foldable
import Substitution

type Equiv = (String, String)

kEq :: Ctx -> Kind -> Kind -> Result ()
kEq ctx KType KType = ok ()
kEq ctx KSession KSession = ok ()
kEq ctx KState KState = ok ()
kEq ctx KShape KShape = ok ()
kEq ctx (KDom t1) (KDom t2) = tEq ctx t1 t2
kEq ctx (KLam d1 c1) (KLam d2 c2) = do
  kEq ctx d1 d2
  kEq ctx c1 c2
kEq ctx k1 k2 = raise ("[K-Eq] kind mismatch between " ++ show k1 ++ " and " ++ show k2)

kEqs :: Ctx -> Kind -> [Kind] -> Result ()
kEqs ctx ks = mapM_ (kEq ctx ks)

kNEq :: Ctx -> Kind -> Kind -> Result ()
kNEq ctx k1 k2 = do
  case kEq ctx k1 k2 of 
    Left _ -> ok ()
    Right _ -> raise ("[K-Eq] kind " ++ show k1 ++ " cannot be " ++ show k2)

tNf :: Type -> Type
{- TC-TApp -}
tNf (TApp (TLam s d t) t') = subT s t' t
{- TC-Proj -}
tNf (DProj l (DMerge d d')) = case l of
  LLeft -> tNf d
  LRight -> tNf d'
{- TC-DualVar -}
tNf (SDual (SDual (TVar i))) = TVar i
{- TC-DualEnd -}
tNf (SDual SEnd) = SEnd
{- TC-DualSend -}
tNf (SDual (SSend n sh st t s)) = SRecv n sh st t (tNf (SDual s))
{- TC-DualRecv -}
tNf (SDual (SRecv n sh st t s)) = SSend n sh st t (tNf  (SDual s))
{- TC-DualChoice -}
tNf (SDual (SChoice st st')) = SBranch (tNf (SDual st)) (tNf (SDual st'))
{- TC-DualBranch -}
tNf (SDual (SBranch st st')) = SChoice (tNf (SDual st)) (tNf (SDual st'))
{- recurse -}
tNf (TLam s d t) = TLam s (tNf d) (tNf t)
tNf (EAll s k cs t) = EAll s k (map (bimap tNf tNf) cs) (tNf  t)
tNf (EArr s t ctx' s' t') = EArr (tNf s) (tNf t) ctx' (tNf s') (tNf t')
tNf (EChan t) = EChan (tNf t)
tNf (EAcc t) = EAcc (tNf t)
tNf (EPair t t') = EPair (tNf t) (tNf t')
tNf (SSend n k s t t') = SSend n k (tNf s) (tNf t) (tNf t')
tNf (SRecv n k s t t') = SRecv n k (tNf s) (tNf t) (tNf t')
tNf (SChoice t t') = SChoice (tNf t) (tNf t')
tNf (SBranch t t') = SBranch (tNf t) (tNf t')
tNf (SDual t) = SDual (tNf t)
tNf (DMerge d d') = DMerge (tNf d) (tNf d')
tNf (SSBind t t') = SSBind (tNf t) (tNf t')
tNf t = t

tEq :: Ctx -> Type -> Type -> Result ()
tEq ctx t t' = tEq' ctx [] (tNf t) (tNf t')

tEq' :: Ctx -> [Equiv] -> Type -> Type -> Result ()
tEq' ctx eqs (TVar a) (TVar b) = do 
  case (find (\ (x, y) -> x == a && y == b) eqs,
       find (\ (x, y) -> x == b && y == a) eqs) of 
    (Nothing, Nothing) -> if a /= b then raise ("[T-Eq] variable name mismatch between " ++ a ++ " and " ++ "b") else ok ()
    _ -> ok ()
  ok ()
tEq' ctx eqs (TApp d c) (TApp d' c') = do 
  tEq' ctx eqs d d'
  tEq' ctx eqs c c'
tEq' ctx eqs (TLam s d t)  (TLam s' d' t') = do
  tEq' ctx eqs d d'
  tEq' ctx ((s, s') : eqs) t t'
tEq' ctx eqs (EArr st1 t1 ctx' st1' t1') (EArr st2 t2 ctx'' st2' t2') = do
  tEq' ctx eqs st1 st2
  tEq' ctx eqs t1 t2
  {- ctxEq ctx' ctx'' -}
  let eqs' = zip (map fst ctx') (map fst ctx'') ++ eqs
  tEq' ctx eqs'  st1' st2'
  tEq' ctx eqs'  t1' t2'
tEq' ctx eqs (EAll s k cs t) (EAll s' k' cs' t') = do
  kEq ctx k k'
  let cs' = renCstrsM eqs cs'
  {- Gamma, C1 |- C2 und Gamma, C2 |- C1 fordern -}
  ctx' <- cs +-* ctx
  tEq' ctx' ((s, s') : eqs) t t'
tEq' ctx eqs (EChan t) (EChan t') = tEq' ctx eqs t t'
tEq' ctx eqs (EAcc t) (EAcc t') = tEq' ctx eqs t t'
tEq' ctx eqs EUnit EUnit = ok ()
tEq' ctx eqs (SSend n k s t c) (SSend n' k' s' t' c') = do
  kEq ctx k k' 
  tEq' ctx ((n, n') : eqs) s s' 
  tEq' ctx ((n, n') : eqs) t t'
  tEq' ctx eqs c c'
tEq' ctx eqs (SRecv n k s t c) (SRecv n' k' s' t' c') = do
  kEq ctx k k' 
  tEq' ctx ((n, n') : eqs) s s' 
  tEq' ctx ((n, n') : eqs) t t'
  tEq' ctx eqs c c'  
tEq' ctx eqs (SChoice l r) (SChoice l' r') = do
  tEq' ctx eqs l l'
  tEq' ctx eqs r r'
tEq' ctx eqs (SBranch l r) (SBranch l' r') = do
  tEq' ctx eqs l l'
  tEq' ctx eqs r r'
tEq' ctx eqs SEnd SEnd = ok ()
tEq' ctx eqs (SDual t) (SDual t') = unreachable
tEq' ctx eqs SHEmpty SHEmpty = ok ()
tEq' ctx eqs (SHDisjoint l r) (SHDisjoint l' r') = do
  tEq' ctx eqs l l'
  tEq' ctx eqs r r'
tEq' ctx eqs DEmpty DEmpty = ok ()
tEq' ctx eqs (DMerge l r) (DMerge l' r') = do
  tEq' ctx eqs l l'
  tEq' ctx eqs r r'
tEq' ctx eqs (DProj l t) (DProj l' t') = unreachable
tEq' ctx eqs SSEmpty SSEmpty  = ok ()
tEq' ctx eqs (SSBind d t) (SSBind d' t') = do
  tEq' ctx eqs d d'
  tEq' ctx eqs t t'
tEq' ctx eqs (SSMerge l r) (SSMerge l' r') = do
  tEq' ctx eqs l l'
  tEq' ctx eqs r r'
tEq' ctx eqs a b = raise ("[T-Eq] type mismatch between " ++ show a ++ " and " ++ show b)   