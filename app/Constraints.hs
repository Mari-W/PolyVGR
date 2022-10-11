module Constraints where

import Ast
import Result
import Context
import Equality
import Data.List


stateDom :: Type -> Result Type
stateDom SSEmpty = ok DEmpty 
stateDom (SSBind d s) = ok d 
stateDom (TApp _ d) = ok d 
stateDom (SSMerge l r) = do
  dl <- stateDom l
  dr <- stateDom r
  ok (DMerge dl dr)
stateDom t = raise ("[CE] expected state to extract dom of, got " ++ show t)

type Disjoint = (String, String)

splitCstr :: Cstr -> [Disjoint]
splitCstr (DEmpty, _) = []
splitCstr (DProj l d, d') = case d of
  DMerge dl dr -> case l of
    LLeft -> splitCstr (dl, d')
    LRight -> splitCstr (dr, d')
  _ -> error "unreachable"
splitCstr (DMerge d d', d'') = splitCstr (d, d'') ++ splitCstr (d', d'')
splitCstr (TVar i, TVar j) = [(i, j)]
splitCstr (d, d') = splitCstr (d', d)

splitCstrs :: [Cstr] -> [Disjoint]
splitCstrs = concatMap splitCstr

filterCstrs :: Ctx -> [Cstr]
filterCstrs [] = []
filterCstrs (x : xs) = case x of
  (_, HasCstr c) -> c : filterCstrs xs
  _ -> filterCstrs xs

{-s earchCstr :: [Disjoint] -> Disjoint -> Result ()
searchCstr [] _ = raise "[CE] constraint not resolved"
searchCstr xs (_, DEmpty) = ok ()
searchCstr xs (DEmpty, _) = ok ()
searchCstr ((x, y) : xs) (a, b) = do
  case (domEq x a, domEq y b) of
    (Right _, Right _) -> ok ()
    _ -> case (domEq x b, domEq y a) of
      (Right _, Right _) -> ok ()
      _ -> searchCstr xs (a, b)


searchCstrs :: [Cstr] -> [Cstr] -> Result ()
searchCstrs atms (x : xs) = do
  searchCstr atms x
  searchCstrs atms xs
searchCstrs atms [] = ok () -}


statesDisjunct :: Ctx -> Type -> Type -> Result ()
statesDisjunct ctx ssl ssr = do
  dssl <- stateDom ssl
  dssr <- stateDom ssr
  let cstrs = splitCstr (dssl, dssr)
  let assm = splitCstrs (filterCstrs ctx)
  ok ()
