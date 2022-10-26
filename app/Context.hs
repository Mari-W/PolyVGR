{-# LANGUAGE LambdaCase #-}
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

kExt :: Ctx -> (String, Kind) -> Ctx
kExt ctx (s, k) = ctx ++ [(s, HasKind k)]

tExt :: Ctx -> (String, Type) -> Ctx
tExt ctx (s, t) = ctx ++ [(s, HasType t)]

cExt :: Ctx ->  Cstr -> Ctx
cExt ctx c = do
  ctx ++ [("__constraint", HasCstr c)]

csExt :: Ctx -> [Cstr] -> Ctx
csExt = foldl cExt

kRes :: Ctx -> String -> Result Kind
kRes ctx s = case find (\(s', _) -> s' == s) (filter (\case (str, HasKind _) -> True; _ -> False ) (rev ctx)) of
  Just (_, HasKind k) -> ok k
  _ -> raise $ "[CTX] could not resolve kind of " ++ s

tRes :: Ctx -> String -> Result Type
tRes ctx s = case find (\(s', _) -> s' == s) (filter (\case (str, HasType _) -> True; _ -> False ) (rev ctx)) of
  Just (_, HasType t) -> ok t
  _ -> raise $ "[CTX] could not resolve type of " ++ s

{-# NOINLINE globalVar #-}
globalVar :: IORef Integer
globalVar = unsafePerformIO (newIORef 0)

{-# INLINE freshVar #-}
freshVar :: String -> String
freshVar n = unsafePerformIO $ do
  s <- readIORef globalVar
  writeIORef globalVar (s + 1)
  return $ "_" ++ n ++ show s

{-# INLINE freshVar2 #-}
freshVar2 :: String -> (String, String)
freshVar2 n = unsafePerformIO $ do
  s <- readIORef globalVar
  writeIORef globalVar (s + 1)
  return ("_" ++ n ++ show s, "_~" ++ n ++ show s)

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