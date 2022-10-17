module Context where

import Ast
    ( Cstr, Ctx, Has(HasCstr, HasType, HasKind), Kind(..), Type(TVar) )
import Data.Foldable (find)
import Result ( ok, raise, Result )
import Data.List (tails)
import System.Random ( newStdGen, Random(randomRs) )
import System.IO.Unsafe ( unsafePerformIO )
import Pretty ( Pretty(pretty) )

(+*) :: (String, Kind) -> Ctx -> Result Ctx
(s, k) +* ctx = do
  s ?! ctx
  ok (ctx ++ [(s, HasKind k)])

(+.) :: (String, Type) -> Ctx -> Result Ctx
(s, t) +. ctx = do
  s ?! ctx
  ok (ctx ++ [(s, HasType t)])

(+-) :: Cstr -> Ctx -> Ctx
c +- ctx = do
  ctx ++ [("__constraint", HasCstr c)]
  
(+-*) :: [Cstr] -> Ctx -> Ctx
[] +-* ctx = ctx
(x : xs) +-* ctx = let ctx' = x +- ctx in
  xs +-* ctx'

(*?) :: String -> Ctx -> Result Kind
s *? ctx = case find (\(s', _) -> s' == s) (rev ctx) of
  Just (_, HasKind k) -> ok k
  _ -> raise ("[CTX] could not resolve kind " ++ s ++ " in " ++ pretty ctx)

(.?) :: String -> Ctx -> Result Type
s .? ctx = case find (\(s', _) -> s' == s) (rev ctx) of
  Just (_, HasType t) -> ok t
  _ -> raise ("[CTX] could not resolve type " ++ s ++ " in " ++ pretty ctx)

(?!) :: String -> Ctx -> Result ()
s ?! ctx = case find (\(s', _) -> s' == s) (rev ctx) of
  Just _ -> raise ("[CTX] variable " ++ s ++ " already defined")
  _ -> ok ()

freshVar :: String
freshVar = take 32 $ randomRs ('a','z') $ unsafePerformIO newStdGen

rev :: Ctx -> Ctx
rev = foldl (flip (:)) []

isDomCtx :: Ctx -> Result ()
isDomCtx [] = ok ()
isDomCtx (x : xs) = case x of  
  (_, HasKind (KDom _)) -> isDomCtx xs 
  _ -> raise ("[CTX] found non domain " ++ pretty x ++ " in ctx")

gd :: Ctx -> Ctx
gd [] = []
gd (x : xs) = case x of
  (_, HasKind k) -> case k of
    KShape -> x : gd xs
    KSession -> x : gd xs
    KState -> x : gd xs
    KLam d1 d2 -> case (d1, d2) of
      (KDom _, KType) -> x : gd xs
      (KDom _, KState) -> x : gd xs
      _ -> gd xs
    _ -> gd xs
  _ -> gd xs

gu :: Ctx -> Ctx
gu [] = []
gu (x : xs) = case x of
  (_, HasKind k) -> case k of
    KDom _ -> x : gu xs
    _ -> gu xs
  _ -> gu xs

domGu :: Ctx -> [Type]
domGu [] = []
domGu (x : xs) = case x of
  (s, HasKind k) -> case k of
    KDom _ -> TVar s : domGu xs
    _ -> domGu xs
  _ -> domGu xs

pairs :: [a] -> [(a, a)]
pairs l = [(x, y) | (x:ys) <- tails l, y <- ys]

combs :: [a] -> [a] -> [(a, a)]
combs l l' = [(x, y) | x <- l, y <- l']

merge :: [(Type, Type)] -> Ctx
merge = map (\(x, y) -> ("__constraint", HasCstr (x, y)))

dce2 :: Ctx -> Ctx
dce2 ctx = merge (pairs (domGu ctx))

dce12 :: Ctx -> Ctx -> Ctx
dce12 ctx ctx' = merge (combs (domGu ctx) (domGu ctx'))

dce :: Ctx -> Ctx -> Ctx
dce ctx ctx' = ctx ++ ctx' ++ dce2 ctx' ++ dce12 ctx ctx'