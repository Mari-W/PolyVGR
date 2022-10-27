{-# LANGUAGE FlexibleContexts #-}
module State where 

import Ast
    ( Ctx, Type(TApp, DEmpty, DMerge, SSEmpty, SSBind, SSMerge) )
import Result ( ok, raise, Result )
import Equality ( tEq, catchToEither ) 
import Constraints ( ce )
import Pretty ( Pretty(pretty) )
import Debug.Trace
import Control.Monad.Except (MonadError)
import Control.Monad.State (MonadState)

type Proj = (Type, Type)

stDom :: (MonadState Int m, MonadError String m) => Type -> m Type
stDom SSEmpty = ok DEmpty 
stDom (SSBind d s) = ok d 
stDom (TApp _ d) = ok d
stDom (SSMerge l r) = do
  dl <- stDom l
  dr <- stDom r
  ok (DMerge dl dr)
stDom t = raise ("[CE] expected state to extract dom of, got " ++ pretty t)

stDisj :: (MonadState Int m, MonadError String m) => Ctx -> Type -> Type -> m ()
stDisj ctx ssl ssr = do
  dssl <- stDom ssl
  dssr <- stDom ssr
  ce ctx [(dssl, dssr)]

stSplitDom :: (MonadState Int m, MonadError String m) => Ctx -> Type -> Type -> m (Maybe (Type,  Type))
stSplitDom ctx (SSBind d1 s) d2 = do
  teq <- catchToEither (tEq ctx d1 d2)
  case teq of 
    Left _ -> return Nothing
    Right _ -> return $ Just (SSEmpty, s)
stSplitDom ctx (SSMerge l r) d = do
  stl <- stSplitDom ctx l d
  str <- stSplitDom ctx r d
  case (stl, str) of 
    (Nothing, Nothing) -> return Nothing
    (Just (re, s), _) -> return $ Just (SSMerge re r, s)
    (_, Just (re, s)) -> return $ Just (SSMerge l re, s)
stSplitDom ctx t d = return Nothing 

stSplitApp :: (MonadState Int m, MonadError String m) => Ctx -> Type -> Type -> m (Maybe Type)
stSplitApp ctx (TApp fd d) (TApp fd2 d2) = do
  teq <- catchToEither $ tEq ctx fd fd2
  case teq of 
    Left _ -> return Nothing
    Right _ -> do
      teq2 <- catchToEither $ tEq ctx d d2
      case teq2 of
        Left s -> return Nothing
        Right x0 -> return $ Just SSEmpty 
stSplitApp ctx (SSMerge l r) d = do
  stl <- stSplitApp ctx l d
  str <- stSplitApp ctx r d
  case (stl, str) of 
    (Nothing, Nothing) -> return Nothing
    (Just re, _) -> return $ Just (SSMerge re r)
    (_, Just re) -> return $ Just (SSMerge l re)
stSplitApp ctx t d = return Nothing 

stSplitSt :: (MonadState Int m, MonadError String m) => Ctx -> Type -> Type -> m Type
stSplitSt ctx st SSEmpty = ok st
stSplitSt ctx st (SSBind d s) = do
  st' <- stSplitDom ctx st d
  case st' of   
    Nothing -> raise ("[T-Split] could not split " ++ pretty (SSBind d s) ++ " out of " ++ pretty st)
    Just (r, s2) -> do 
      tEq ctx s s2
      ok r
stSplitSt ctx st (SSMerge l r) = do
  st' <- stSplitSt ctx st l
  stSplitSt ctx st' r
stSplitSt ctx st (TApp f a) = do
  st' <- stSplitApp ctx st (TApp f a)
  case st' of
    Nothing -> raise ("[T-Split] could not split " ++ pretty (TApp f a) ++ " out of " ++ pretty st)
    Just r -> ok r
stSplitSt ctx st t = raise ("[T-Split] expected state to split, got " ++ pretty t)