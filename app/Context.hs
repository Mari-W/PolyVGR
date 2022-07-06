module Context where

import Ast (Dom, ExprType, Kind (KDom, KLam, KSession, KState, KType), Type, Constr)

data Has
  = HasType Type
  | HasKind Kind
  | HasConstr Constr

type Ctx = [Has]

typeAbsSafe :: Ctx -> Ctx
typeAbsSafe [] = []
typeAbsSafe (x : xs) = case x of
  HasKind k -> case k of
    KSession -> x : typeAbsSafe xs
    KState -> x : typeAbsSafe xs
    KLam d1 d2 -> case (d1, d2) of
      (KDom _, KType) -> x : typeAbsSafe xs
      (KDom _, KState) -> x : typeAbsSafe xs
      _ -> typeAbsSafe xs
    _ -> typeAbsSafe xs
  _ -> typeAbsSafe xs

noDomBinds :: Ctx -> Ctx
noDomBinds [] = []
noDomBinds (x : xs) = case x of
  HasKind k -> case k of
    KDom _ -> x : noDomBinds xs
    _ -> noDomBinds xs
  _ -> noDomBinds xs

disCtxExt :: Ctx -> Ctx -> Ctx
disCtxExt ctx1 ctx2 = []