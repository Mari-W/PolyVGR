module Conversion where

import Ast
import Substitution
import Data.Bifunctor

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
tNf (TApp t t') = TApp (tNf t) (tNf t')
tNf (TLam s k t) = TLam s k (tNf t)
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
tNf (SHMerge t t') = SHMerge (tNf t) (tNf t')
tNf (DMerge d d') = DMerge (tNf d) (tNf d')
tNf (DProj l d) = DProj l (tNf d)
tNf (SSBind t t') = SSBind (tNf t) (tNf t')
tNf (SSMerge t t') = SSMerge (tNf t) (tNf t')
tNf t = t