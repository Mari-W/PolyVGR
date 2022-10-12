module State where 

import Ast

import Result
import Equality 
import Constraints

type Proj = (Type, Type)

stDom :: Type -> Result Type
stDom SSEmpty = ok DEmpty 
stDom (SSBind d s) = ok d 
stDom (TApp _ d) = ok d 
stDom (SSMerge l r) = do
  dl <- stDom l
  dr <- stDom r
  ok (DMerge dl dr)
stDom t = raise ("[CE] expected state to extract dom of, got " ++ show t)

stDisj :: Ctx -> Type -> Type -> Result ()
stDisj ctx ssl ssr = do
  dssl <- stDom ssl
  dssr <- stDom ssr
  ce ctx [(dssl, dssr)]

stSplitDom :: Ctx -> Type -> Type -> Result (Type, Maybe Type)
stSplitDom ctx SSEmpty d = ok (SSEmpty, Nothing)
stSplitDom ctx (SSBind d1 s) d2 = do
  case tEq ctx d1 d2 of 
    Left _ -> ok (SSBind d1 s, Nothing)
    Right _ -> ok (SSEmpty, Just s)
stSplitDom ctx (SSMerge l r) d = do
  (t1, b1) <- stSplitDom ctx l d
  (t2, b2) <- stSplitDom ctx r d
  ok (case (b1, b2) of 
    (Nothing, Nothing) -> (SSMerge t1 t2, Nothing)
    (Just l, _) -> (SSMerge t1 t2, Just l)
    (_, Just r) -> (SSMerge t1 t2, Just r))
stSplitDom ctx t d = raise ("[T-Split] expected state to split, got " ++ show t)

splitSt :: Type -> Result [Proj]
splitSt SSEmpty = ok []
splitSt (SSBind d st) = ok [(d, st)]
splitSt (SSMerge l r) = do
  sl <- splitSt l
  sr <- splitSt r
  ok (sl ++ sr)
splitSt t = raise ("[T-Split] expected state to split, got " ++ show t)

stSplitSt :: Ctx -> Type -> Type -> Result (Type, Maybe Type)
stSplitSt ctx st1 st2 = ok (EUnit, Just EUnit)