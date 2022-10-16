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
freeT bs (EAll x k cs t) = let bs' = x : bs in
  freeCstrs bs' cs ++ freeK bs k ++ freeT bs' t 
freeT bs (EArr st1 t1 ctx st2 t2) = let bs' = map fst ctx ++ bs in
  freeT bs st1 ++  freeT bs t1 ++ freeCtx bs ctx ++ freeT bs' st2 ++ freeT bs' t2
freeT bs (EChan d) = freeT bs d
freeT bs (EAcc t) = freeT bs t
freeT bs EUnit = []
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
freeV bs (VPair v1 v2) = freeV bs v1 ++ freeV bs v2
freeV bs (VTAbs x k cs v) = freeV (x : bs) v
freeV bs (VChan t) = []
freeV bs (VAbs st x t e) = freeE (x : bs) e 
 

renCstrs :: String -> String -> [Cstr] -> [Cstr]
renCstrs x1 x2 = subCstrs x1 (TVar x2)

renCstrsM :: [(String, String)] -> [Cstr] -> [Cstr]
renCstrsM [] cs = cs
renCstrsM ((x, y) : xs) cs = renCstrsM xs (renCstrs y x cs)

renCtx :: String -> String -> Ctx -> Ctx 
renCtx x1 x2 = subCtx x1 (TVar x2)

renK :: String -> String -> Kind -> Kind
renK x1 x2 = subK x1 (TVar x2)
 
renTM :: [(String, String)] -> Type -> Type
renTM xs = subTM (map (second TVar) xs)

renT :: String -> String -> Type -> Type
renT x1 x2 = subT x1 (TVar x2)

renE :: String -> String -> Expr -> Expr
renE x1 x2 = subE x1 (VVar x2)

renV :: String -> String -> Val -> Val
renV x1 x2 = subV x1 (VVar x2)

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
    Just str -> let v = freshVar in
      (v, r) : subCtx x s (renCtx x2 v xs)
  else (x2, r) : xs

subK :: String -> Type -> Kind -> Kind
subK x s (KDom t) = KDom (subT x s t)
subK x s (KLam l r) = KLam (subK x s l) (subK x s r)
subK x s k = k

subTM :: [(String, Type)] -> Type -> Type
subTM [] t = t
subTM ((x, s) : xs) t = subTM xs (subT x s t)

subT :: String -> Type -> Type -> Type
subT x s (TVar x2) = if x == x2 then s else TVar x2
subT x s (TApp f a) = TApp (subT x s f) (subT x s a)
subT x s (TLam x2 k b) = if x == x2 then TLam x2 (subK x s k) b else 
    case find (== x2) (freeT [] s) of
      Nothing -> TLam x2 (subK x s k) (subT x s b)
      Just _ -> let v = freshVar in
        TLam v (subK x s k) (subT x s (renT x2 v b))
subT x s (EAll x2 k cs t) = if x == x2 then EAll x2 (subK x s k) cs t else
    case find (== x2) (freeT [] s) of
      Nothing -> EAll x2 (subK x s k) (subCstrs x s cs) (subT x s t)
      Just _ -> let v = freshVar in
        EAll v (subK x s k) (subCstrs x s (renCstrs x2 v cs)) (subT x s (renT x2 v t))
subT x s (EArr st1 t1 ctx st2 t2) = EArr (subT x s st1) (subT x s t1) (subCtx x s ctx) (subT x s st2) (subT x s t2) 
subT x s (EChan d) = EChan (subT x s d)
subT x s (EAcc t) = EAcc (subT x s t)
subT x s EUnit = EUnit 
subT x s (EPair l r) = EPair (subT x s l) (subT x s r)
subT x s (SSend x2 k st t c) =  if x == x2 then SSend x2 (subK x s k) st t (subT x s c) else 
    case find (== x2) (freeT [] s) of
      Nothing -> SSend x2 (subK x s k) (subT x s st) (subT x s t) (subT x s c)
      Just str ->  let v = freshVar in
        SSend v (subK x s k) (subT x s (renT x2 v st)) (subT x s  (renT x2 v t)) (subT x s c)
subT x s (SRecv x2 k st t c) = if x == x2 then SRecv x2 (subK x s k) st t (subT x s c) else 
    case find (== x2) (freeT [] s) of
      Nothing -> SRecv x2 (subK x s k) (subT x s st) (subT x s t) (subT x s c)
      Just str -> let v = freshVar in
        SRecv v (subK x s k) (subT x s (renT x2 v st)) (subT x s  (renT x2 v t)) (subT x s c)
subT x s (SChoice l r) = SChoice (subT x s l) (subT x s r)
subT x s (SBranch l r) = SBranch (subT x s l) (subT x s r)
subT x s SEnd = SEnd
subT x s (SDual t) = SDual (subT x s t)
subT x s SHEmpty = SHEmpty 
subT x s SHSingle = SHSingle
subT x s (SHMerge l r) = SHMerge (subT x s l) (subT x s r)
subT x s DEmpty = DEmpty 
subT x s (DProj l t) = DProj l (subT x s t)
subT x s (DMerge l r) = DMerge (subT x s l) (subT x s r)
subT x s SSEmpty = SSEmpty 
subT x s (SSBind l r) = SSBind (subT x s l) (subT x s r)
subT x s (SSMerge l r) = SSMerge (subT x s l) (subT x s r)

subE :: String -> Val -> Expr -> Expr
subE x s (Let x2 e1 e2) = if x == x2 then Let x2 (subE x s e1) e2 else 
    case find (== x2) (freeV [] s) of
      Nothing -> Let x2 (subE x s e1) (subE x s e2)
      Just str -> let v = freshVar in
        Let v (subE x s e1) (subE x s (renE x2 v e2))
subE x s (Val v) = Val (subV x s v) 
subE x s (Proj l v) = Proj l (subV x s v)
subE x s (App v1 v2) = App (subV x s v1) (subV x s v2)
subE x s (AApp v t) = AApp (subV x s v) t
subE x s (Fork v) = Fork (subV x s v)
subE x s (Acc v) = Acc (subV x s v)
subE x s (Req v) = Req (subV x s v)
subE x s (Send v1 v2) = Send (subV x s v1) (subV x s v2)
subE x s (Recv v) = Recv (subV x s v)
subE x s (Sel l v) = Sel l (subV x s v)
subE x s (Case v e1 e2) =  Case (subV x s v) (subE x s e1) (subE x s e2)
subE x s (Close v) = Close (subV x s v)
subE x s (New t) = New t 

subV :: String -> Val -> Val -> Val
subV x s (VVar x2) = if x == x2 then s else VVar x2
subV x s VUnit = VUnit
subV x s (VPair v1 v2) = VPair (subV x s v1) (subV x s v2)
subV x s (VTAbs x2 k cs v) = VTAbs x2 k cs (subV x s v)
subV x s (VChan t) = VChan t
subV x s (VAbs st x2 t e) = if x == x2 then VAbs st x2 t e else 
    case find (== x2) (freeV [] s) of
      Nothing -> VAbs st x2 t (subE x s e)
      Just str -> let v = freshVar in
        VAbs st v t (subE x s (renE x2 v e))

subTE :: String -> Type -> Expr -> Expr
subTE x s (Let x2 e1 e2) = Let x2 (subTE x s e1) (subTE x s e2)
subTE x s (Val v) = Val (subTV x s v) 
subTE x s (Proj l v) = Proj l (subTV x s v)
subTE x s (App v1 v2) = App (subTV x s v1) (subTV x s v2)
subTE x s (AApp v t) = AApp (subTV x s v) (subT x s t)
subTE x s (Fork v) = Fork (subTV x s v)
subTE x s (Acc v) = Acc (subTV x s v)
subTE x s (Req v) = Req (subTV x s v)
subTE x s (Send v1 v2) = Send (subTV x s v1) (subTV x s v2)
subTE x s (Recv v) = Recv (subTV x s v)
subTE x s (Sel l v) = Sel l (subTV x s v)
subTE x s (Case v e1 e2) =  Case (subTV x s v) (subTE x s e1) (subTE x s e2)
subTE x s (Close v) = Close (subTV x s v)
subTE x s (New t) = New (subT x s t)

subTV :: String -> Type -> Val -> Val
subTV x s (VVar x2) = VVar x2
subTV x s VUnit = VUnit
subTV x s (VPair v1 v2) = VPair (subTV x s v1) (subTV x s v2)
subTV x s (VTAbs x2 k cs v) = if x == x2 then VTAbs x2 (subK x s k) cs v else 
    case find (== x2) (freeT [] s) of
      Nothing -> VTAbs x2 (subK x s k) (subCstrs x s cs) (subTV x s v)
      Just str -> let f = freshVar in
        VTAbs f (subK x s k) (subCstrs x s (renCstrs x2 f cs)) (subTV x s (renV x2 f v))
subTV x s (VChan t) = VChan t
subTV x s (VAbs st x2 t e) = VAbs (subT x s st) x2 (subT x s t) (subTE x s e) 