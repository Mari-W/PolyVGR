module Constraints where


import Ast
import Result
import Context
import Equality

split :: Constr -> Result [Constr]
split (DEmpty, _) = ok []
split (DProj l d, d') = case d of
  DMerge dl dr -> case l of
    LLeft -> split (dl, d')
    LRight -> split (dr, d')
  {- is this unreachable, i.e. is it type checked before searched? -}
  d -> raise ("[CS] projection to empty or single domain " ++ show d)
split (DMerge d d', d'') = do
  s <- split (d, d'')
  s' <- split (d', d'')
  ok (s ++ s')
{- termination enforced because it can only be domains here -}
split (d, d') = split (d', d)

splitM :: [Constr] -> Result [Constr] 
splitM [] = ok []
splitM (x : xs) = do
  s <- split x
  s' <- splitM xs
  ok (s ++ s')

search :: [Constr] -> Constr -> Result ()
search [] c = raise ("[CS] failed to resolve " ++ show c)
search xs (_, DEmpty) = ok ()
search xs (DEmpty, _) = ok ()
search ((x, y) : xs) (a, b) = do
  case (tEq [] x a, tEq [] y b) of
    (Right _, Right _) -> ok ()
    _ -> case (tEq [] x b, tEq [] y a) of
      (Right _, Right _) -> ok ()
      _ -> search xs (a, b)

searchM :: [Constr] -> [Constr] -> Result () 
searchM a (x : xs) = do
  search a x
  searchM a xs
searchM a []  = ok ()

isDom :: Type -> Result ()
isDom DEmpty = ok ()
isDom (DMerge d d') = do
  isDom d 
  isDom d'   
isDom (DProj _ d) = isDom d
isDom t = raise ("[CS] found non domain as constraint " ++ show t)

constrs :: Ctx -> Result [Constr]
constrs [] = ok []
constrs (x : xs) = case x of 
  (_, HasConstr (d, d')) -> do 
    isDom d
    isDom d'
    cont <- constrs xs
    ok ((d, d') : cont)
  _ -> constrs xs

resolve :: Ctx -> Constr -> Result ()
resolve ctx c = do
  cs <- constrs ctx
  cs' <- splitM cs
  c' <- split c 
  searchM cs' c' 