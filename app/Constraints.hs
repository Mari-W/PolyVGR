module Constraints where

import Ast (Dom (DEmpty, DProj, DTree, DVar), Label (LLeft, LRight), Shape (SDisjoint), State (SSEmpty, SSMap, SSTree), Type, State, Constr)
import Context (Ctx, Has (HasConst))
import Equality (domEq)
import Result (Result, ok, raise)

filterConstrs :: Ctx -> [Constr]
filterConstrs [] = []
filterConstrs (x : xs) = case x of
  HasConst c -> c : filterConstrs xs
  _ -> filterConstrs xs

splitConstr :: Constr -> [Constr]
splitConstr (DEmpty, _) = []
splitConstr (DProj l d, d') = case d of
  DTree dl dr -> case l of
    LLeft -> splitConstr (dl, d')
    LRight -> splitConstr (dr, d')
  _ -> error "unreachable"
splitConstr (DTree d d', d'') = splitConstr (d, d'') ++ splitConstr (d', d'')
splitConstr (DVar i, DVar j) = [(DVar i, DVar j)]
splitConstr (d, d') = splitConstr (d', d)

splitConstrs :: [Constr] -> [Constr]
splitConstrs = concatMap splitConstr

searchConstr :: [Constr] -> Constr -> Result ()
searchConstr [] _ = raise "constraint not resolved"
searchConstr xs (_, DEmpty) = ok ()
searchConstr xs (DEmpty, _) = ok ()
searchConstr ((x, y) : xs) (a, b) = do
  case (domEq x a, domEq y b) of
    (Right _, Right _) -> ok ()
    _ -> case (domEq x b, domEq y a) of
      (Right _, Right _) -> ok ()
      _ -> searchConstr xs (a, b)

searchConstrs :: [Constr] -> [Constr] -> Result ()
searchConstrs atms (x : xs) = do
  searchConstr atms x
  searchConstrs atms xs
searchConstrs atms [] = ok ()

constrWellFormed :: Ctx -> Constr -> Result ()
constrWellFormed ctx c = searchConstrs (splitConstrs (filterConstrs ctx)) (splitConstr c)

dom :: State -> Dom
dom SSEmpty = DEmpty
dom (SSMap d _) = d
dom (SSTree s s') = DTree (dom s) (dom s)

constrWellFormed' :: Ctx -> (State, State) -> Result ()
constrWellFormed' ctx (s, s') = constrWellFormed ctx (dom s, dom s')