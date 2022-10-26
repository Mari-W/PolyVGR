module Constraints where

import Ast
    ( Cstr,
      Ctx,
      Has(HasCstr),
      Label(..),
      Type(DProj, DEmpty, DMerge, TVar) )
import Result ( ok, raise, Result )
import Context ( combs )
import Conversion ( tNf )
import Data.List ( find )
import Pretty ( Pretty(pretty) ) 

splitDom :: Type -> Result [Type]
splitDom DEmpty = ok []
splitDom (DMerge d d') = (++) <$> splitDom d <*> splitDom d'
splitDom (DProj l d) = ok [DProj l d]
splitDom (TVar x) = ok [TVar x]
splitDom t = raise ("[CE] expected state to extract dom of, got " ++ pretty t)

splitCstr :: Cstr -> Result [Cstr]
splitCstr (a, b) = do
  xs <- splitDom (tNf a)
  ys <- splitDom (tNf b)
  ok (combs xs ys ++ combs ys xs)

splitCstrs :: [Cstr] -> Result [Cstr]
splitCstrs x = fmap concat (mapM splitCstr x)

invLabel :: Label -> Label 
invLabel LLeft = LRight 
invLabel LRight = LLeft 

extCstrs :: [Cstr] -> [Cstr]
extCstrs cs = concatMap f cs where
  f (DProj l d, t) = case find (\ (t1, t2) -> t1 == DProj (invLabel l) d && t2 == t) cs of
    Nothing -> []
    Just _ -> [(d, t), (t, d)]
  f _ = []
  
fixExtCstrs :: [Cstr] -> [Cstr]
fixExtCstrs cs = do 
  let ext = extCstrs cs
  if null ext then cs else fixExtCstrs (ext ++ cs)

filterCstrs :: Ctx -> [Cstr]
filterCstrs [] = []
filterCstrs (x : xs) = case x of
  (_, HasCstr c) -> c : filterCstrs xs
  _ -> filterCstrs xs

searchCstr :: [Cstr] -> Cstr -> Result ()
searchCstr [] (a, b) = raise $ "[CE] constraint not satisfied: " ++ show a ++ " # " ++ show b
searchCstr ((x, y) : xs) (a, b) = if x == a && y == b 
  then ok ()
  else searchCstr xs (a, b)

searchCstrs :: [Cstr] -> [Cstr] -> Result ()
searchCstrs atms (x : xs) = do
  searchCstr atms x
  searchCstrs atms xs
searchCstrs atms [] = ok ()

ce :: Ctx -> [Cstr] -> Result ()
ce ctx cs = do
  assm <- fixExtCstrs <$> splitCstrs (filterCstrs ctx)
  cstrs <- splitCstrs cs
  searchCstrs assm cstrs