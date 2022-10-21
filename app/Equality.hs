{-# LANGUAGE FlexibleContexts #-}
module Equality where

import Ast
    ( Ctx,
      Has(HasType),
      Kind(..),
      Type(SSMerge, TVar, TApp, TLam, EArr, EAll, EChan, EAcc, EUnit,
           SSend, SRecv, SChoice, SBranch, SEnd, SDual, SHEmpty, SHSingle,
           SHMerge, DEmpty, DMerge, DProj, SSEmpty, SSBind) )
import Context ( (+-*), (.?) )
import Data.Bifunctor (Bifunctor (bimap))
import Result ( ok, raise, unreachable, Result )
import Data.Foldable ( find )
import Substitution ( renCstrsM )
import Constraints ( ce ) 
import Conversion ( tNf )
import Control.Monad ( join )
import Data.Either ( isLeft )
import Data.Tuple ( swap )
import Pretty ( Pretty(pretty) )

type Equiv = (String, String)

kEq ctx k1 k2 = case kEq' ctx k1 k2 of
  Right x -> Right x
  Left err -> Left $ err ++ "\n    equality of " ++ pretty k1 ++ " and " ++ pretty k2 ++ "\n         in [" ++ pretty ctx ++ "]"


kEq' :: Ctx -> Kind -> Kind -> Result ()
kEq' ctx KType KType = ok ()
kEq' ctx KSession KSession = ok ()
kEq' ctx KState KState = ok ()
kEq' ctx KShape KShape = ok ()
kEq' ctx (KDom t1) (KDom t2) = tEq ctx t1 t2
kEq' ctx (KArr d1 c1) (KArr d2 c2) = do
  kEq ctx d1 d2
  kEq ctx c1 c2
kEq' ctx k1 k2 = raise ("[K-Eq] kind mismatch between " ++ pretty k1 ++ " and " ++ pretty k2)

kEqs :: Ctx -> Kind -> [Kind] -> Result ()
kEqs ctx ks = mapM_ (kEq ctx ks)

kNEq :: Ctx -> Kind -> Kind -> Result ()
kNEq ctx k1 k2 = do
  case kEq ctx k1 k2 of 
    Left _ -> ok ()
    Right _ -> raise ("[K-Eq] kind " ++ pretty k1 ++ " cannot be " ++ pretty k2)

tEq ctx t1 t2 = case tEq'' ctx t1 t2 of
  Right x -> Right x
  Left err -> Left $ err ++ "\n    equality of " ++ pretty t1 ++ " and " ++ pretty t2 ++ "\n         in [" ++ pretty ctx ++ "]"

tEq'' :: Ctx -> Type -> Type -> Result ()
tEq'' ctx = tEq' ctx []

tEq' :: Ctx -> [Equiv] -> Type -> Type -> Result ()
tEq' ctx eqs t t' = do
  l <- tUnify ctx eqs (tNf t) (tNf t')
  if null l then ok () 
  else raise ("[T-Eq] type mismatch between " ++ pretty t ++ " and " ++ 
              pretty t' ++ ", the following variables should be equal: " ++ show l) 

uqsConsistent :: [Equiv] -> Result ()
uqsConsistent uqs = case ["\n  " ++ x ++ " is required to be both " ++ y ++ " and " ++ y' | 
        (x, y) <- uqs, (x', y') <- uqs, x == x', y /= y'] of
    [] -> ok ()
    xs -> raise ("[T-Unify] fail to compare contexts: " ++ join xs)

tUnify :: Ctx -> [Equiv] -> Type -> Type -> Result [Equiv]
tUnify ctx eqs (TVar a) (TVar b) =  case (find (\ (x, y) -> x == a && y == b) eqs,
                                          find (\ (x, y) -> x == b && y == a) eqs) of 
    (Nothing, Nothing) -> if a /= b then ok [(a, b)] else ok []
    _ -> ok []
tUnify ctx eqs (TApp d c) (TApp d' c') = do 
  d <- tUnify ctx eqs d d' 
  c <- tUnify ctx eqs c c'
  ok (d ++ c)
tUnify ctx eqs (TLam s k t)  (TLam s' k' t') = do
  kEq ctx k k'
  tUnify ctx ((s, s') : eqs) t t'
tUnify ctx eqs (EArr st1 t1 ctx1 st1' t1') (EArr st2 t2 ctx2 st2' t2') = do
  st <- tUnify ctx eqs st1 st2
  t <- tUnify ctx eqs t1 t2
  eqs' <- existUnify' ctx eqs (ctx1, st1', t1') (ctx2, st2', t2')
  ok (st ++ t ++ eqs')
tUnify ctx eqs (EAll s k cs t) (EAll s' k' cs' t') = do
  kEq ctx k k'
  let cs' = renCstrsM eqs cs'
  let ctx' = cs +-* ctx
  ce ctx' cs'
  let ctx'' = cs' +-* ctx
  ce ctx'' cs
  tUnify ctx' ((s, s') : eqs) t t'
tUnify ctx eqs (EChan t) (EChan t') = tUnify ctx eqs t t'
tUnify ctx eqs (EAcc t) (EAcc t') = tUnify ctx eqs t t'
tUnify ctx eqs EUnit EUnit = ok []
tUnify ctx eqs (SSend n k s t c) (SSend n' k' s' t' c') = do
  kEq ctx k k' 
  s <- tUnify ctx ((n, n') : eqs) s s' 
  t <- tUnify ctx ((n, n') : eqs) t t'
  c <- tUnify ctx eqs c c'
  ok (s ++ t ++ c)
tUnify ctx eqs (SRecv n k s t c) (SRecv n' k' s' t' c') = do
  kEq ctx k k' 
  s <- tUnify ctx ((n, n') : eqs) s s' 
  t <- tUnify ctx ((n, n') : eqs) t t'
  c <- tUnify ctx eqs c c'
  ok (s ++ t ++ c)
tUnify ctx eqs (SChoice l r) (SChoice l' r') = do
  l <- tUnify ctx eqs l l'
  r <- tUnify ctx eqs r r'
  ok (l ++ r)
tUnify ctx eqs (SBranch l r) (SBranch l' r') = do
  l <- tUnify ctx eqs l l'
  r <- tUnify ctx eqs r r'
  ok (l ++ r)
tUnify ctx eqs SEnd SEnd = ok []
tUnify ctx eqs (SDual t) (SDual t') = unreachable
tUnify ctx eqs SHEmpty SHEmpty = ok []
tUnify ctx eqs SHSingle SHSingle = ok []
tUnify ctx eqs (SHMerge l r) (SHMerge l' r') = do
  l <- tUnify ctx eqs l l'
  r <- tUnify ctx eqs r r'
  ok (l ++ r)
tUnify ctx eqs DEmpty DEmpty = ok []
tUnify ctx eqs (DMerge l r) (DMerge l' r') = do
  l <- tUnify ctx eqs l l'
  r <- tUnify ctx eqs r r'
  ok (l ++ r)
tUnify ctx eqs (DProj l t) (DProj l' t') = unreachable
tUnify ctx eqs SSEmpty SSEmpty  = ok []
tUnify ctx eqs (SSBind d t) (SSBind d' t') = do
  d <- tUnify ctx eqs d d'
  t <- tUnify ctx eqs t t'
  ok (d ++ t)
tUnify ctx eqs (SSMerge l r) (SSMerge l' r') = do
  l <- tUnify ctx eqs l l'
  r <- tUnify ctx eqs r r'
  ok (l ++ r)
tUnify ctx eqs a b = raise ("[T-Unify] could not unify " ++ pretty a ++ " and " ++ pretty b)

ctxUnifyH :: [Equiv] ->  [Equiv] -> Ctx -> Ctx -> Ctx -> Result [Result ()]
ctxUnifyH eqs uqs ctx [] ctx2 = ok [] 
ctxUnifyH eqs uqs ctx ((x, HasType t) : xs) ctx2 = case find (\(x', y') -> x == x') uqs of 
  Nothing -> do 
    t' <- x .? ctx2
    xs' <- ctxUnifyH eqs uqs ctx xs ctx2
    ok (tEq' ctx eqs t t' : xs')
  Just (_, y) -> do
    t' <- y .? ctx2
    xs' <- ctxUnifyH eqs uqs ctx xs ctx2
    ok (tEq' ctx eqs t t' : xs')
ctxUnifyH _ _ _ _ _ = raise "[T-Unify] expected context with only dom bindings"

{- dom binding ctxs only  -}
ctxUnify' :: [Equiv] -> [Equiv] -> Ctx -> Ctx -> Ctx -> Result [Equiv]
ctxUnify' eqs uqs ctx ctx1 ctx2 = do
  h <- ctxUnifyH eqs uqs ctx ctx1 ctx2
  let f ctx1 ctx2 uqs = case filter isLeft h of 
        [] -> ok ()
        xs -> raise ("[T-Unify] fail to compare contexts: " ++ join ["\n  " ++ s | (Left s) <- xs])
  f ctx1 ctx2 uqs
  f ctx2 ctx1 (map swap uqs)
  ok [ (x , y) | (x , y) <- uqs, x `notElem` map fst ctx1 ]

{- unification for ∃Γ.Σ;T -}
existEq ctx tri1 tri2 = case existEq'' ctx tri1 tri2 of
  Right x -> Right x
  Left err -> Left $ err ++ "\n    equality of " ++ pretty tri1 ++ " and " ++ pretty tri2 ++ "\n         in [" ++ pretty ctx ++ "]"

existEq'' :: Ctx -> (Ctx, Type, Type) -> (Ctx, Type, Type) -> Result ()
existEq'' ctx = existEq' ctx []
    
existEq' :: Ctx -> [Equiv] -> (Ctx, Type, Type) -> (Ctx, Type, Type) -> Result ()
existEq' ctx eqs tri1 tri2 = do
  l <- existUnify' ctx eqs tri1 tri2
  if null l then ok ()else raise ("[T-Eq] type mismatch between " ++ pretty tri1 ++ " and " ++ 
                                  pretty tri2 ++ ", the following variables should be equal: " ++ show l)

existUnify' :: Ctx -> [Equiv] -> (Ctx, Type, Type) -> (Ctx, Type, Type) -> Result [Equiv]
existUnify' ctx eqs (ctx1, st1, t1) (ctx2, st2, t2) = do
  st' <- tUnify ctx eqs st1 st2
  t' <- tUnify ctx eqs t1 t2
  let uqs = st' ++ t'
  uqsConsistent uqs
  ctxUnify' eqs uqs ctx ctx1 ctx2