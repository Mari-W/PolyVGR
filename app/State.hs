module State where 

import Ast
    ( Ctx, Type(TApp, DEmpty, DMerge, SSEmpty, SSBind, SSMerge) )
import Result ( ok, raise, Result )
import Equality ( tEq ) 
import Constraints ( ce )
import Pretty ( Pretty(pretty) )

type Proj = (Type, Type)

stDom :: Type -> Result Type
stDom SSEmpty = ok DEmpty 
stDom (SSBind d s) = ok d 
stDom (TApp _ d) = ok d
stDom (SSMerge l r) = do
  dl <- stDom l
  dr <- stDom r
  ok (DMerge dl dr)
stDom t = raise ("[CE] expected state to extract dom of, got " ++ pretty t)

stDisj :: Ctx -> Type -> Type -> Result ()
stDisj ctx ssl ssr = do
  dssl <- stDom ssl
  dssr <- stDom ssr
  ce ctx [(dssl, dssr)]

stSplitDom :: Ctx -> Type -> Type -> Maybe (Type,  Type)
stSplitDom ctx (SSBind d1 s) d2 = case tEq ctx d1 d2 of 
    Left _ -> Nothing
    Right _ -> Just (SSEmpty, s)
stSplitDom ctx (SSMerge l r) d = case (stSplitDom ctx l d, stSplitDom ctx r d) of 
    (Nothing, Nothing) -> Nothing
    (Just (re, l), _) -> Just (SSMerge re r, l)
    (_, Just (re, r)) -> Just (SSMerge l re, r)
stSplitDom ctx t d = Nothing 

splitSt :: Type -> Result [Proj]
splitSt SSEmpty = ok []
splitSt (SSBind d st) = ok [(d, st)]
splitSt (SSMerge l r) = (++) <$> splitSt l <*> splitSt r
splitSt t = raise ("[T-Split] expected state to split, got " ++ pretty t)

stSplitApp :: Ctx -> Type -> Type -> Maybe Type
stSplitApp ctx (TApp fd d) (TApp fd2 d2) =case tEq ctx fd fd2 of 
    Left _ -> Nothing
    Right _ -> case tEq ctx d d2 of
      Left s -> Nothing
      Right x0 -> Just SSEmpty 
stSplitApp ctx (SSMerge l r) d = case (stSplitApp ctx l d, stSplitApp ctx r d) of 
    (Nothing, Nothing) -> Nothing
    (Just s, _) -> Just (SSMerge s r)
    (_, Just s) -> Just (SSMerge l s)
stSplitApp ctx t d = Nothing 

stSplitSt :: Ctx -> Type -> Type -> Result Type
stSplitSt ctx st SSEmpty = ok st
stSplitSt ctx st (SSBind d s) = case stSplitDom ctx st d of   
  Nothing -> raise ("[T-Split] could not split " ++ pretty (SSBind d s) ++ " out of " ++ pretty st)
  Just (r, s2) -> do 
    tEq ctx s s2
    ok r
stSplitSt ctx st (SSMerge l r) = do
  st' <- stSplitSt ctx st l
  stSplitSt ctx st' r
stSplitSt ctx st (TApp f a) = case stSplitApp ctx st (TApp f a) of
  Nothing -> raise ("[T-Split] could not split " ++ pretty (TApp f a) ++ " out of " ++ pretty st)
  Just r -> ok r
stSplitSt ctx st t = raise ("[T-Split] expected state to split, got " ++ pretty t)