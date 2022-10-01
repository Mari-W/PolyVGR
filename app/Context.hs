module Context where

import Ast
  ( Constr,
    Kind (KDom, KLam, KSession, KShape, KState, KType),
    Type,
  )
import Data.Foldable (find)
import Result ( ok, raise, Result )

data Has
  = HasType Type
  | HasKind Kind
  | HasConstr Constr

type Ctx = [(String, Has)]

(+*) :: (String, Kind) -> Ctx -> Result Ctx
(s, k) +* ctx = do
  s ?! ctx
  ok ((s, HasKind k) : ctx)

(+.) :: (String, Type) -> Ctx -> Result Ctx
(s, t) +. ctx = do
  s ?! ctx
  ok ((s, HasType t) : ctx)

(+-) :: (String, Constr) -> Ctx -> Result Ctx
(s, c) +- ctx = do
  ok ((s, HasConstr c) : ctx)

(*?) :: String -> Ctx -> Result Kind
s *? ctx = case find (\(s', _) -> s' == s) ctx of
  Just (_, HasKind k) -> ok k
  _ -> raise ("could not resolve kind " ++ s)

(.?) :: String -> Ctx -> Result Type
s .? ctx = case find (\(s', _) -> s' == s) ctx of
  Just (_, HasType t) -> ok t
  _ -> raise ("could not resolve type " ++ s)

(-?) :: String -> Ctx -> Result Constr
s -? ctx = case find (\(s', _) -> s' == s) ctx of
  Just (_, HasConstr c) -> ok c
  _ -> raise ("could not resolve constraint " ++ s)

(?!) :: String -> Ctx -> Result ()
s ?! ctx = case find (\(s', _) -> s' == s) ctx of
  Just _ -> raise ("variable " ++ s ++ " already defined")
  _ -> ok ()

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

dce :: Ctx -> Ctx -> Ctx
dce _ _ = []