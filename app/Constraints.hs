module Constraints where

import Ast
import Result
import Context
import Equality
import Data.List



dom :: Type -> Result Type
dom SSEmpty = ok DEmpty 
dom (SSBind d s) = ok d 
dom (TApp _ d) = ok d 
dom (SSMerge l r) = do
  dl <- dom l
  dr <- dom r
  ok (DMerge dl dr)
dom t = raise ("[CE] expected state to extract dom of, got " ++ show t)

flatten :: Type -> Result [String]
flatten (TVar x) = ok [x]
flatten DEmpty  = ok []
flatten (DProj l d) = do
  case d of
    DMerge dl dr -> case l of
      LLeft -> flatten dl
      LRight -> flatten dr
    _ -> unreachable
flatten (DMerge l r) = do
  fl <- flatten l
  fr <- flatten r
  ok (fl ++ fr)
flatten t = raise ("[CE] expected to flatten domain, got " ++ show t)


stateDisjunct :: Type -> Type -> Result ()
stateDisjunct ssl ssr = do
  dssl <- dom ssl
  dssr <- dom ssr
  fssl <- flatten dssl
  fssr <- flatten dssr
  ok ()
