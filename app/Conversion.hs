{-# LANGUAGE  FlexibleContexts #-}
module Conversion where

import Ast
    ( Label(LRight, LLeft),
      Type(SSMerge, TVar, SEnd, TApp, TLam, EAll, EArr, EChan, EAcc,
           EPair, SSend, SRecv, SChoice, SBranch, SDual, SHMerge, DMerge,
           DProj, SSBind, SSEmpty) )
import Substitution ( subT )
import Data.Bifunctor ( Bifunctor(bimap) )
import Data.List (sort)
import Control.Monad.State (MonadState)
import Data.Bitraversable (bimapM)

tNf :: MonadState Int m => Type -> m Type
{- TC-TApp -}
tNf (TApp (TLam s d t) t') = subT s t' t
{- TC-Proj -}
tNf (DProj l (DMerge d d')) = case l of
  LLeft -> tNf d
  LRight -> tNf d'
{- TC-DualVar -}
tNf (SDual (SDual (TVar i))) = return $ TVar i
{- TC-DualEnd -}
tNf (SDual SEnd) = return SEnd
{- TC-DualSend -}
tNf (SDual (SSend n sh st t s)) = SRecv n sh st t <$> tNf (SDual s)
{- TC-DualRecv -}
tNf (SDual (SRecv n sh st t s)) = SSend n sh st t <$> tNf (SDual s)
{- TC-DualChoice -}
tNf (SDual (SChoice st st')) = SBranch <$> tNf (SDual st) <*> tNf (SDual st')
{- TC-DualBranch -}
tNf (SDual (SBranch st st')) = SChoice <$> tNf (SDual st) <*> tNf (SDual st')
tNf (TApp t t') = TApp <$> tNf t <*> tNf t'
tNf (TLam s k t) = TLam s k <$> tNf t
tNf (EAll s k cs t) = EAll s k <$> mapM (bimapM tNf tNf) cs <*> tNf  t
tNf (EArr s t ctx' s' t') = EArr <$> tNf s <*> tNf t <*> pure ctx' <*> tNf s' <*> tNf t'
tNf (EChan t) = EChan <$> tNf t
tNf (EAcc t) = EAcc <$> tNf t
tNf (EPair t t') = EPair <$> tNf t <*> tNf t'
tNf (SSend n k s t t') = SSend n k <$> tNf s <*> tNf t <*> tNf t'
tNf (SRecv n k s t t') = SRecv n k <$> tNf s <*> tNf t <*> tNf t'
tNf (SChoice t t') = SChoice <$> tNf t <*> tNf t'
tNf (SBranch t t') = SBranch <$> tNf t <*> tNf t'
tNf (SDual t) = SDual <$> tNf t
tNf (SHMerge t t') = SHMerge <$> tNf t <*> tNf t'
tNf (DMerge d d') = DMerge <$> tNf d <*> tNf d'
tNf (DProj l d) = DProj l <$> tNf d
tNf (SSBind t t') = SSBind <$> tNf t <*> tNf t'
tNf ss @ (SSMerge t t') = return $ normalizeSt ss
tNf t = return t

flattenSt :: Type -> [Type]
flattenSt SSEmpty = []
flattenSt (SSMerge l r) = flattenSt l ++ flattenSt r
flattenSt t = [t]

rebuildSt :: [Type] -> Type
rebuildSt = foldr SSMerge SSEmpty

normalizeSt :: Type -> Type
normalizeSt = rebuildSt . sort . flattenSt