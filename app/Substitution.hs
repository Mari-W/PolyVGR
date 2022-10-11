module Substitution where

import Ast
import Data.Foldable
import Data.Bifunctor
import Context
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
freeK bs (KLam l r) = freeK bs l ++ freeK bs r
freeK bs _ = []

freeT :: [Bind] -> Type -> [Free]
freeT bs (TVar x) = case find (== x) bs of
  Nothing -> [x]
  Just _ -> [] 
freeT bs (TApp f a) = freeT bs f ++ freeT bs a
freeT bs (TLam s d t) = freeT (s : bs) t
freeT bs (EAll x k cs t) = do
  let bs' = x : bs
  freeCstrs bs' cs ++ freeK bs k ++ freeT bs' t 
freeT bs (EArr st1 t1 ctx st2 t2) = do
  let bs' = map fst ctx ++ bs
  freeT bs st1 ++  freeT bs t1 ++ freeCtx bs ctx ++ freeT bs' st2 ++ freeT bs' t2
freeT bs (EChan d) = freeT bs d
freeT bs (EAcc t) = freeT bs t
freeT bs EUnit = []
freeT bs (EPair l r) = freeT bs l ++ freeT bs r
freeT bs (SSend x k st t c) = do
  let bs' = x : bs
  freeT bs c ++ freeT bs' t ++ freeT bs' st ++ freeK bs k
freeT bs (SRecv x k st t c) = do
  let bs' = x : bs
  freeT bs c ++ freeT bs' t ++ freeT bs' st ++ freeK bs k
freeT bs (SChoice l r) = freeT bs l ++ freeT bs r
freeT bs (SBranch l r) = freeT bs l ++ freeT bs r
freeT bs SEnd = []
freeT bs (SDual t) = freeT bs t
freeT bs SHEmpty = [] 
freeT bs SHSingle = []
freeT bs (SHDisjoint l r) = freeT bs l ++ freeT bs r
freeT bs DEmpty = [] 
freeT bs (DProj l t) = freeT bs t
freeT bs (DMerge l r) = freeT bs l ++ freeT bs r
freeT bs SSEmpty = [] 
freeT bs (SSBind l r) = freeT bs l ++ freeT bs r
freeT bs (SSMerge l r) = freeT bs l ++ freeT bs r

renCstrs :: String -> String -> [Cstr] -> [Cstr]
renCstrs x1 x2 = subCstrs x1 (TVar x2)

renCtx :: String -> String -> Ctx -> Ctx 
renCtx x1 x2 = subCtx x1 (TVar x2)

renK :: String -> String -> Kind -> Kind
renK x1 x2 = subK x1 (TVar x2)
 
renT :: String -> String -> Type -> Type
renT x1 x2 = subT x1 (TVar x2)

subCstrs :: String -> Type -> [Cstr] -> [Cstr]
subCstrs x s = map (bimap (subT x s) (subT x s))

subCtx :: String -> Type -> Ctx -> Ctx
subCtx x s [] = []
subCtx x s ((x2, i) : xs) = do
  let r = case i of
            HasType t -> HasType (subT x s t)
            HasKind k -> HasKind (subK x s k)
            HasCstr c -> HasCstr(head (subCstrs x s [c]))
  if x /= x2 then case find (== x2) (freeT [] s) of
    Nothing -> (x2, r) : subCtx x s xs
    Just str -> do
      let v = freshVar 
      (v, r) : subCtx x s (renCtx x2 v xs)
  else (x2, r) : xs

subK :: String -> Type -> Kind -> Kind
subK x s (KDom t) = KDom (subT x s t)
subK x s (KLam l r) = KLam (subK x s l) (subK x s r)
subK x s k = k

subT :: String -> Type -> Type -> Type
subT x s (TVar x2) = if x == x2 then s else TVar x2
subT x s (TApp f a) = TApp (subT x s f) (subT x s a)
subT x s (TLam x2 d b) = do
  if x == x2 then TLam x2 (subT x s d) b else 
    case find (== x2) (freeT [] s) of
      Nothing -> TLam x2 (subT x s d) (subT x s b)
      Just _ -> do
        let v = freshVar
        TLam v (subT x s d) (subT x s (renT x2 v b))
subT x s (EAll x2 k cs t) = do
  if x == x2 then EAll x2 (subK x s k) cs t else
    case find (== x2) (freeT [] s) of
      Nothing -> EAll x2 (subK x s k) (subCstrs x s cs) (subT x s t)
      Just _ -> do
        let v = freshVar
        EAll v (subK x s k) (subCstrs x s (renCstrs x2 v cs)) (subT x s (renT x2 v t))
subT x s (EArr st1 t1 ctx st2 t2) = EArr (subT x s st1) (subT x s t1) (subCtx x s ctx) (subT x s st2) (subT x s t2) 
subT x s (EChan d) = EChan (subT x s d)
subT x s (EAcc t) = EAcc (subT x s t)
subT x s EUnit = EUnit 
subT x s (EPair l r) = EPair (subT x s l) (subT x s r)
subT x s (SSend x2 k st t c) = do 
  if x == x2 then SSend x2 (subK x s k) st t (subT x s c) else 
    case find (== x2) (freeT [] s) of
      Nothing -> SSend x2 (subK x s k) (subT x s st) (subT x s t) (subT x s c)
      Just str -> do
        let v = freshVar
        SSend x2 (subK x s k) (subT x s (renT x2 v st)) (subT x s  (renT x2 v t)) (subT x s c)
subT x s (SRecv x2 k st t c) = do 
  if x == x2 then SRecv x2 (subK x s k) st t (subT x s c) else 
    case find (== x2) (freeT [] s) of
      Nothing -> SRecv x2 (subK x s k) (subT x s st) (subT x s t) (subT x s c)
      Just str -> do
        let v = freshVar
        SRecv x2 (subK x s k) (subT x s (renT x2 v st)) (subT x s  (renT x2 v t)) (subT x s c)
subT x s (SChoice l r) = SChoice (subT x s l) (subT x s r)
subT x s (SBranch l r) = SBranch (subT x s l) (subT x s r)
subT x s SEnd = SEnd
subT x s (SDual t) = SDual (subT x s t)
subT x s SHEmpty = SHEmpty 
subT x s SHSingle = SHSingle
subT x s (SHDisjoint l r) = SHDisjoint (subT x s l) (subT x s r)
subT x s DEmpty = DEmpty 
subT x s (DProj l t) = DProj l (subT x s t)
subT x s (DMerge l r) = DMerge (subT x s l) (subT x s r)
subT x s SSEmpty = SSEmpty 
subT x s (SSBind l r) = SSBind (subT x s l) (subT x s r)
subT x s (SSMerge l r) = SSMerge (subT x s l) (subT x s r)