{-# LANGUAGE LambdaCase,FlexibleContexts #-}
module Context where

import Ast
    ( Cstr, Ctx, Has(HasCstr, HasType, HasKind), Kind(..), Type(TVar) )
import Data.Foldable (find)
import Result ( ok, raise, Result )
import Data.List (tails)
import System.Random ( newStdGen, Random(randomRs) )
import System.IO.Unsafe ( unsafePerformIO )
import Pretty ( Pretty(pretty) )
import Data.IORef
import Control.Monad.State
import Control.Monad.Except (MonadError)

kExt :: Ctx -> (String, Kind) -> Ctx
kExt ctx (s, k) = ctx ++ [(s, HasKind k)]

tExt :: Ctx -> (String, Type) -> Ctx
tExt ctx (s, t) = ctx ++ [(s, HasType t)]

cExt :: Ctx ->  Cstr -> Ctx
cExt ctx c = do
  ctx ++ [("__constraint", HasCstr c)]

csExt :: Ctx -> [Cstr] -> Ctx
csExt = foldl cExt

kRes :: MonadError String m => Ctx -> String -> m Kind
kRes ctx s = case find (\(s', _) -> s' == s) (filter (\case (str, HasKind _) -> True; _ -> False ) (rev ctx)) of
  Just (_, HasKind k) -> ok k
  _ -> raise $ "[CTX] could not resolve kind of " ++ s

tRes :: MonadError String m => Ctx -> String -> m Type
tRes ctx s = case find (\(s', _) -> s' == s) (filter (\case (str, HasType _) -> True; _ -> False ) (rev ctx)) of
  Just (_, HasType t) -> ok t
  _ -> raise $ "[CTX] could not resolve type of " ++ s


freshVar :: MonadState Int m => String -> m String
freshVar n = do
  s <- get
  put (s + 1)
  return $ "'" ++ n ++ show s

freshVar2 :: MonadState Int m => String -> m (String, String)
freshVar2 n = do
  s <- get
  put (s + 1)
  return ("'" ++ n ++ show s, "'~" ++ n ++ show s)

rev :: Ctx -> Ctx
rev = foldl (flip (:)) []

isDomCtx :: MonadError String m => Ctx -> m ()
isDomCtx [] = ok ()
isDomCtx (x : xs) = case x of
  (_, HasKind (KDom _)) -> isDomCtx xs
  _ -> raise ("[K-Arr] expected only domains in context, got: " ++ pretty x)

gd :: Ctx -> Ctx
gd [] = []
gd (x : xs) = case x of
  (_, HasKind k) -> case k of
    KShape -> x : gd xs
    KSession -> x : gd xs
    KState -> x : gd xs
    KArr d1 d2 -> case (d1, d2) of
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