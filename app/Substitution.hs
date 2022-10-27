{-# LANGUAGE FlexibleContexts #-}
module Substitution where

import Ast
    ( Cstr,
      Ctx,
      Expr(..),
      Has(HasCstr, HasType, HasKind),
      Kind(KArr, KDom),
      Type(..),
      Val(..) )
import Data.Foldable ( find )
import Data.Bifunctor ( Bifunctor(bimap, second) )
import Context ( freshVar )
import Control.Monad.State (MonadState)
import Data.Bitraversable (bimapM)

type Bind = String
type Free = String

flatten :: [[a]] -> [a]
flatten arr = [y | x<- arr, y <- x]

freeCstrs :: [Bind] -> [Cstr] -> [Free]
freeCstrs bs cs = flatten (map (\(x, y) -> freeT bs x ++ freeT bs y) cs)

freeCtx :: [Bind] -> Ctx -> [Free]
freeCtx bs [] = []
freeCtx bs ((s, HasKind k) : xs) = freeK bs k ++ freeCtx (s : bs) xs 
freeCtx bs ((s, HasType t) : xs) = freeT bs t ++ freeCtx (s : bs) xs
freeCtx bs ((s, HasCstr c) : xs) = freeCstrs bs [c] ++ freeCtx bs xs

freeK :: [Bind] -> Kind -> [Free]
freeK bs (KDom t) = freeT bs t
freeK bs (KArr l r) = freeK bs l ++ freeK bs r
freeK bs _ = []

freeT :: [Bind] -> Type -> [Free]
freeT bs (TVar x) = case find (== x) bs of
  Nothing -> [x]
  Just _ -> [] 
freeT bs (TApp f a) = freeT bs f ++ freeT bs a
freeT bs (TLam s d t) = freeT (s : bs) t
freeT bs (EAll x k cs t) = let bs' = x : bs in
  freeCstrs bs' cs ++ freeK bs k ++ freeT bs' t 
freeT bs (EArr st1 t1 ctx st2 t2) = let bs' = map fst ctx ++ bs in
  freeT bs st1 ++  freeT bs t1 ++ freeCtx bs ctx ++ freeT bs' st2 ++ freeT bs' t2
freeT bs (EChan d) = freeT bs d
freeT bs (EAcc t) = freeT bs t
freeT bs EUnit = []
freeT bs EInt = []
freeT bs (EPair l r) = freeT bs l ++ freeT bs r
freeT bs (SSend x k st t c) = let bs' = x : bs in
  freeT bs c ++ freeT bs' t ++ freeT bs' st ++ freeK bs k
freeT bs (SRecv x k st t c) = let bs' = x : bs in
  freeT bs c ++ freeT bs' t ++ freeT bs' st ++ freeK bs k
freeT bs (SChoice l r) = freeT bs l ++ freeT bs r
freeT bs (SBranch l r) = freeT bs l ++ freeT bs r
freeT bs SEnd = []
freeT bs (SDual t) = freeT bs t
freeT bs SHEmpty = [] 
freeT bs SHSingle = []
freeT bs (SHMerge l r) = freeT bs l ++ freeT bs r
freeT bs DEmpty = [] 
freeT bs (DProj l t) = freeT bs t
freeT bs (DMerge l r) = freeT bs l ++ freeT bs r
freeT bs SSEmpty = [] 
freeT bs (SSBind l r) = freeT bs l ++ freeT bs r
freeT bs (SSMerge l r) = freeT bs l ++ freeT bs r

freeE :: [Bind] -> Expr -> [Free]
freeE bs (Let x e1 e2) = freeE bs e1 ++ freeE (x : bs) e2
freeE bs (Val v) = freeV bs v
freeE bs (Proj l v) = freeV bs v
freeE bs (App v1 v2) = freeV bs v1 ++ freeV bs v2
freeE bs (AApp v t) = freeV bs v
freeE bs (Fork v) = freeV bs v
freeE bs (Acc v) = freeV bs v
freeE bs (Req v) = freeV bs v
freeE bs (Send v1 v2) = freeV bs v1 ++ freeV bs v2
freeE bs (Recv v) = freeV bs v
freeE bs (Sel l v) = freeV bs v
freeE bs (Case v e1 e2) = freeV bs v ++ freeE bs e1 ++ freeE bs e2
freeE bs (Close v) = freeV bs v
freeE bs (New t) = []

freeV :: [Bind] -> Val -> [Free]
freeV bs (VVar x) = case find (== x) bs of
  Nothing -> [x]
  Just _ -> [] 
freeV bs VUnit = []
freeV bs (VInt i) = []
freeV bs (VPair v1 v2) = freeV bs v1 ++ freeV bs v2
freeV bs (VTAbs x k cs v) = freeV (x : bs) v
freeV bs (VChan t) = []
freeV bs (VAbs st x t e) = freeE (x : bs) e 
 

renCstrs :: MonadState Int m => String -> String -> [Cstr] -> m [Cstr]
renCstrs x1 x2 = subCstrs x1 (TVar x2)

renCstrsM :: MonadState Int m => [(String, String)] -> [Cstr] -> m [Cstr]
renCstrsM [] cs = return cs
renCstrsM ((x, y) : xs) cs = renCstrsM xs =<< renCstrs y x cs

renCtx :: MonadState Int m => String -> String -> Ctx -> m Ctx 
renCtx x1 x2 = subCtx x1 (TVar x2)

renK :: MonadState Int m =>  String -> String -> Kind -> m Kind
renK x1 x2 = subK x1 (TVar x2)
 
renTM :: MonadState Int m => [(String, String)] -> Type -> m Type
renTM xs = subTM (map (second TVar) xs)

renT :: MonadState Int m => String -> String -> Type -> m Type
renT x1 x2 = subT x1 (TVar x2)

renE :: MonadState Int m => String -> String -> Expr -> m Expr
renE x1 x2 = subE x1 (VVar x2)

renV :: MonadState Int m => String -> String -> Val -> m Val
renV x1 x2 = subV x1 (VVar x2)

subCstrs :: MonadState Int m => String -> Type -> [Cstr] -> m [Cstr]
subCstrs x s = mapM (bimapM (subT x s) (subT x s))

subCtx :: MonadState Int m => String -> Type -> Ctx -> m Ctx
subCtx x s [] = return []
subCtx x s ((x2, i) : xs) = do
  r <- case i of
            HasType t -> HasType <$> subT x s t
            HasKind k -> HasKind <$>  subK x s k
            HasCstr c -> HasCstr . head <$> subCstrs x s [c]
  if x /= x2 then case find (== x2) (freeT [] s) of
    Nothing -> ((x2, r) :) <$> subCtx x s xs
    Just str -> do
      v <- freshVar x2
      ren <- renCtx x2 v xs
      ((v, r) :) <$> subCtx x s ren
  else return $ (x2, r) : xs

subK :: MonadState Int m => String -> Type -> Kind -> m Kind
subK x s (KDom t) = KDom <$> subT x s t
subK x s (KArr l r) = KArr <$> subK x s l <*> subK x s r
subK x s k = return k

subTM :: MonadState Int m => [(String, Type)] -> Type -> m Type
subTM [] t = return t
subTM ((x, s) : xs) t = subTM xs =<< subT x s t

subT :: MonadState Int m => String -> Type -> Type -> m Type
subT x s (TVar x2) = return $ if x == x2 then s else TVar x2
subT x s (TApp f a) = TApp <$> subT x s f <*> subT x s a
subT x s (TLam x2 k b) = if x == x2 then TLam x2 <$> subK x s k <*> pure b else 
    case find (== x2) (freeT [] s) of
      Nothing -> TLam x2 <$> subK x s k <*> subT x s b
      Just _ -> do
        v <- freshVar x2
        TLam v <$> subK x s k <*> (subT x s =<< renT x2 v b)
subT x s (EAll x2 k cs t) = if x == x2 then (\k -> EAll x2 k cs t) <$> subK x s k  else
    case find (== x2) (freeT [] s) of
      Nothing -> EAll x2 <$> subK x s k <*> subCstrs x s cs <*> subT x s t
      Just _ -> do
        v <- freshVar x2 
        EAll v <$> subK x s k <*> (subCstrs x s =<< renCstrs x2 v cs) <*> (subT x s =<< renT x2 v t)
subT x s (EArr st1 t1 ctx st2 t2) = EArr <$> subT x s st1 <*> subT x s t1 
                                    <*> subCtx x s ctx <*> subT x s st2 <*> subT x s t2
subT x s (EChan d) = EChan <$> subT x s d
subT x s (EAcc t) = EAcc <$> subT x s t
subT x s EUnit = return EUnit 
subT x s EInt = return EInt 
subT x s (EPair l r) = EPair <$> subT x s l <*> subT x s r
subT x s (SSend x2 k st t c) =  if x == x2 then SSend x2 <$> subK x s k <*> pure st <*> pure t  <*> subT x s c else 
    case find (== x2) (freeT [] s) of
      Nothing -> SSend x2 <$> subK x s k <*> subT x s st <*> subT x s t <*> subT x s c
      Just str -> do
        v <- freshVar x2 
        SSend v <$> subK x s k <*> (subT x s =<< renT x2 v st) <*> (subT x s =<< renT x2 v t) <*> subT x s c
subT x s (SRecv x2 k st t c) = if x == x2 then SRecv x2 <$> subK x s k <*> pure st <*> pure t <*> subT x s c else 
    case find (== x2) (freeT [] s) of
      Nothing -> SRecv x2 <$> subK x s k <*> subT x s st <*> subT x s t <*> subT x s c
      Just str -> do
        v <- freshVar x2 
        SRecv v  <$> subK x s k <*> (subT x s =<< renT x2 v st) <*> (subT x s  =<< renT x2 v t) <*> subT x s c
subT x s (SChoice l r) = SChoice <$> subT x s l <*> subT x s r
subT x s (SBranch l r) = SBranch <$> subT x s l <*> subT x s r
subT x s SEnd = return SEnd
subT x s (SDual t) = SDual <$> subT x s t
subT x s SHEmpty = return SHEmpty 
subT x s SHSingle = return SHSingle
subT x s (SHMerge l r) = SHMerge <$> subT x s l <*> subT x s r
subT x s DEmpty = return DEmpty 
subT x s (DProj l t) = DProj l <$> subT x s t
subT x s (DMerge l r) = DMerge <$> subT x s l <*> subT x s r
subT x s SSEmpty = return SSEmpty 
subT x s (SSBind l r) = SSBind <$> subT x s l <*> subT x s r
subT x s (SSMerge l r) = SSMerge <$> subT x s l <*> subT x s r

subE :: MonadState Int m => String -> Val -> Expr -> m Expr
subE x s (Let x2 e1 e2) = if x == x2 then Let x2 <$> subE x s e1 <*> pure e2 else 
    case find (== x2) (freeV [] s) of
      Nothing -> Let x2 <$> subE x s e1 <*> subE x s e2
      Just str -> do
        v <- freshVar x2
        Let v <$> subE x s e1 <*> (subE x s =<< renE x2 v e2)
subE x s (Val v) = Val <$> subV x s v 
subE x s (Proj l v) = Proj l <$> subV x s v
subE x s (App v1 v2) = App <$> subV x s v1 <*> subV x s v2
subE x s (AApp v t) = AApp <$> subV x s v <*> pure t
subE x s (Fork v) = Fork <$> subV x s v
subE x s (Acc v) = Acc <$> subV x s v
subE x s (Req v) = Req <$> subV x s v
subE x s (Send v1 v2) = Send <$> subV x s v1 <*> subV x s v2
subE x s (Recv v) = Recv <$> subV x s v
subE x s (Sel l v) = Sel l <$> subV x s v
subE x s (Case v e1 e2) =  Case <$> subV x s v <*> subE x s e1 <*> subE x s e2
subE x s (Close v) = Close <$> subV x s v
subE x s (New t) = return $ New t 

subV :: MonadState Int m => String -> Val -> Val -> m Val
subV x s (VVar x2) = return $ if x == x2 then s else VVar x2
subV x s VUnit = return VUnit
subV x s (VInt i) = return $ VInt i
subV x s (VPair v1 v2) = VPair <$> subV x s v1 <*> subV x s v2
subV x s (VTAbs x2 k cs v) = VTAbs x2 k cs <$> subV x s v
subV x s (VChan t) = return $ VChan t
subV x s (VAbs st x2 t e) = if x == x2 then return $ VAbs st x2 t e else 
    case find (== x2) (freeV [] s) of
      Nothing -> VAbs st x2 t <$> subE x s e
      Just str -> do
        v <- freshVar x2 
        VAbs st v t <$> (subE x s =<< renE x2 v e)

subTE :: MonadState Int m => String -> Type -> Expr -> m Expr
subTE x s (Let x2 e1 e2) = Let x2 <$> subTE x s e1 <*> subTE x s e2
subTE x s (Val v) = Val <$> subTV x s v 
subTE x s (Proj l v) = Proj l <$> subTV x s v
subTE x s (App v1 v2) = App <$> subTV x s v1 <*> subTV x s v2
subTE x s (AApp v t) = AApp <$> subTV x s v <*> subT x s t
subTE x s (Fork v) = Fork <$> subTV x s v
subTE x s (Acc v) = Acc <$> subTV x s v
subTE x s (Req v) = Req <$> subTV x s v
subTE x s (Send v1 v2) = Send <$> subTV x s v1 <*> subTV x s v2
subTE x s (Recv v) = Recv <$> subTV x s v
subTE x s (Sel l v) = Sel l <$> subTV x s v
subTE x s (Case v e1 e2) =  Case <$> subTV x s v <*> subTE x s e1 <*> subTE x s e2
subTE x s (Close v) = Close <$> subTV x s v
subTE x s (New t) = New <$> subT x s t

subTV :: MonadState Int m => String -> Type -> Val -> m Val
subTV x s (VVar x2) = return $ VVar x2
subTV x s VUnit = return VUnit
subTV x s (VInt i) = return $ VInt i
subTV x s (VPair v1 v2) = VPair <$> subTV x s v1 <*> subTV x s v2
subTV x s (VTAbs x2 k cs v) = if x == x2 then VTAbs x2 <$> subK x s k <*> pure cs <*> pure v else 
    case find (== x2) (freeT [] s) of
      Nothing -> VTAbs x2 <$> subK x s k <*> subCstrs x s cs <*> subTV x s v
      Just str -> do
        f <- freshVar x2 
        VTAbs f <$> subK x s k <*> (subCstrs x s =<< renCstrs x2 f cs) <*> (subTV x s =<< renV x2 f v)
subTV x s (VChan t) = return $ VChan t
subTV x s (VAbs st x2 t e) = VAbs <$> subT x s st <*> pure x2 <*> subT x s t <*> subTE x s e 