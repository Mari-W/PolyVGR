module State where 

import Ast

import Result
import Equality 

stSplit :: Ctx -> Type -> Type -> Result (Type, Maybe Type)
stSplit ctx SSEmpty d = ok (SSEmpty, Nothing)
stSplit ctx (SSBind d1 s) d2 = do
  case tEq ctx d1 d2 of 
    Left _ -> ok (SSBind d1 s, Nothing)
    Right _ -> ok (SSEmpty, Just s)
stSplit ctx (SSMerge l r) d = do
  (t1, b1) <- stSplit ctx l d
  (t2, b2) <- stSplit ctx r d
  ok (case (b1, b2) of 
    (Nothing, Nothing) -> (SSMerge t1 t2, Nothing)
    (Just l, _) -> (SSMerge t1 t2, Just l)
    (_, Just r) -> (SSMerge t1 t2, Just r))
stSplit ctx t d = raise ("[T-Split] expected state to split, got " ++ show t)