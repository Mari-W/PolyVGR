{-# LANGUAGE  FlexibleContexts,ConstraintKinds #-}
{-# LANGUAGE LambdaCase #-}
module Typing where

import Ast
    ( AccBind,
      ChanBind,
      Ctx,
      Expr(..),
      Has(HasKind),
      Kind(KDom, KType, KShape, KSession),
      Label(LRight, LLeft),
      Program,
      Type(SDual, EPair, EAll, SSend, SRecv, EArr, SChoice, EUnit, EChan,
           SBranch, SSEmpty, EAcc, SEnd, SHSingle, SSMerge, SSBind, TVar, EInt, EBool),
      Val(..), BinOp (Add, Sub, Mul, Div, Or, And) )
import Constraints ( ce )
import Context ( dce, freshVar, tRes, kExt, csExt, tExt )
import Conversion ( tNf )
import Equality ( existEq, kEq, tEq, tUnify )
import Kinding ( kwf, cwf, kind', kind )
import Result ( ok, raise, Result )
import State ( stSplitDom, stSplitSt )
import Substitution ( renTM, subCstrs, subT )
import Pretty ( Pretty(pretty) )
import Debug.Trace
import Control.Monad.State (MonadState)
import Control.Monad.Except (MonadError, catchError, liftEither)


typeV' :: (MonadError String m, MonadState Int m) => Ctx  -> Val -> m Type
typeV' ctx v = catchError (typeV ctx v) $ \err -> 
  raise $ err ++ "\n\n-----------::        type of         ::-----------\n----  val  ----\n" 
              ++ pretty v ++ "\n----  ctx  ----\n[" ++ pretty ctx ++ "]"

typeV :: (MonadError String m, MonadState Int m) => Ctx -> Val -> m Type
{- T-Var -}
typeV ctx (VVar x) = tRes ctx x
{- T-Unit -}
typeV ctx VUnit = ok EUnit
{- T-Nat -}
typeV ctx (VInt i)  = ok EInt
{- T-Nat -}
typeV ctx (VBool b)  = ok EBool
{- T-Pair -}
typeV ctx (VPair l r) = do
  tl <- typeV' ctx l
  tr <- typeV' ctx r
  ok (EPair tl tr)
{- T-TAbs -}
typeV ctx (VTAbs s k cs v) = do
  let ctx' = kExt ctx (s, k)
  let ctx'' = csExt ctx' cs
  cwf ctx''
  tv <- typeV' ctx'' v
  kt <- kind' ctx (EAll s k cs tv)
  kEq ctx kt KType
  ok (EAll s k cs tv)
{- T-Chan -}
typeV ctx (VChan d) = do
  d' <- kind' ctx d
  case d' of
    KDom SHSingle -> ok (EChan d)
    _ -> raise ("[T-Chan] expected single domain, got " ++ pretty d')
{- T-Abs -}
typeV ctx (VAbs st s t e) = do
  let ctx' = tExt ctx (s, t)
  cwf ctx'
  (ctx', st', te) <- typeE' ctx' st e
  ke <- kind' ctx (EArr st t ctx' st' te)
  kEq ctx ke KType 
  ok (EArr st t ctx' st' te)

typeE' :: (MonadError String m, MonadState Int m) => Ctx -> Type -> Expr -> m (Ctx, Type, Type)
typeE' ctx st e = catchError (typeE ctx st e) $ \err -> 
  raise $ err ++ "\n\n-----------::        type of         ::-----------\n---- expr  ----\n" 
              ++ pretty e ++ "\n----  ctx  ----\n[" ++ pretty ctx ++ "]\n---- state ----\n" ++ pretty st

typeE :: (MonadError String m, MonadState Int m) => Ctx -> Type -> Expr -> m (Ctx, Type, Type)
{- T-Let -}
typeE ctx st (Let s e1 e2) = do
  (ctx1, ss1, t1) <- typeE' ctx st e1
  let ctx' = dce ctx ctx1
  let ctx'' = tExt ctx' (s, t1)
  cwf ctx''
  (ctx2, ss2, t2) <- typeE' ctx'' ss1 e2 
  ok (ctx1 ++ ctx2, ss2, t2)
{- T-Val -}
typeE ctx st (Val v) = do
  tv <- typeV' ctx v
  ok ([], st, tv)
{- T-Proj -}
typeE ctx st (Proj l v) = do
  tv <- typeV ctx v
  case (l, tv) of       
    (LLeft, EPair t _) -> ok ([], st, t)
    (LRight, EPair _ t) -> ok ([], st, t)
    _ -> raise ("[T-Proj] expected to project out of pair, got " ++ pretty tv)
{- T-App -}
typeE ctx st (App v a) = do
  tv <- typeV' ctx v
  case tv of
    EArr st1 t1 ctx1 st2 t2 -> do
      ta <- typeV' ctx a
      tEq ctx t1 ta
      st' <- stSplitSt ctx st st1
      ok ([], st', t2)
    _ -> raise ("[T-App] expected to apply to function, got " ++ pretty tv)
{- T-TApp -}
typeE ctx st (AApp v t) = do
  tv <- typeV' ctx v
  case tv of
    EAll s k cs c -> do
      kt <- kind' ctx t
      kEq ctx kt k
      ce ctx =<< subCstrs s t cs
      t <- tNf =<< subT s t c
      return ([], st, t)
    _ -> raise ("[T-TApp] expected to apply to forall abstraction, got " ++ pretty tv)
{- T-New -}
typeE ctx st (New t) = do
  kt <- kind' ctx t
  kEq ctx kt KSession 
  ok ([], st, EAcc t)
{- T-Request -}
typeE ctx st (Req v) = do
  tv <- typeV' ctx v
  case tv of 
    EAcc t -> do
      x <- freshVar "c" 
      ok ([(x, HasKind (KDom SHSingle))], SSMerge st (SSBind (TVar x) t), EChan (TVar x))
    _ -> raise ("[T-Request] expected access point to request to, got " ++ pretty tv)
{- T-Accept -}
typeE ctx st (Acc v) = do
  tv <- typeV' ctx v
  case tv of 
    EAcc t -> do
      x <- freshVar "c"
      tnf <- tNf (SDual t)
      ok ([(x, HasKind (KDom SHSingle))], SSMerge st (SSBind (TVar x) tnf), EChan (TVar x))
    _ -> raise ("[T-Accept] expected access point to request to, got " ++ pretty tv)
{- T-Send -}
typeE ctx st (Send v1 v2) = do 
  tv1 <- typeV' ctx v1
  tv2 <- typeV' ctx v2
  case tv2 of 
    EChan d1 -> do
      kd1 <- kind' ctx d1
      kEq ctx kd1 (KDom SHSingle)
      stSplitDom ctx st d1 >>= \case 
        Just (r , SSend x kd2 st1 t1 s) -> case kd2 of 
            KDom sh -> do
              ksh <- kind' ctx sh
              kEq ctx ksh KShape
              u <- tUnify ctx [] t1 tv1
              st1' <- renTM u st1
              st' <- stSplitSt ctx r st1'
              ok ([], SSMerge st' (SSBind d1 s), EUnit)
            _ -> raise ("[T-Send] can only abstract over domains, got " ++ pretty kd2)
        _ -> raise ("[T-Send] expected send channel (i.e !s) along a state including its binding, got "
                    ++ pretty tv1 ++ " and " ++ pretty st)
    _ -> raise ("[T-Send] expected channel to send on got " ++ pretty tv2)
{- T-Receive -}
typeE ctx st (Recv v) = do 
  tv <- typeV' ctx v
  case tv of 
    EChan d1 -> stSplitDom ctx st d1 >>= \case
        Just (r , SRecv x kd2 st1 t1 s) -> do
          kwf ctx kd2
          kd1 <- kind' ctx d1
          kEq ctx kd1 (KDom SHSingle)
          ok ([(x, HasKind kd2)], SSMerge r (SSMerge st1 (SSBind d1 s)), t1)
        _ -> raise ("[T-Recv] expected receive channel (i.e ?s) along a state including its binding, got " 
                    ++ pretty tv ++ " and " ++ pretty st)
    _ -> raise ("[T-Send] expected channel to receive on, got " ++ pretty tv)
{- T-Fork -}
typeE ctx st (Fork v) = do 
  tv <- typeV' ctx v
  case tv of
    EArr st1 EUnit ctx2 st2 EUnit -> do
      tEq ctx st2 SSEmpty 
      st' <- stSplitSt ctx st st1
      ok ([], st', EUnit)
    _ -> raise ("[T-Fork] expected Process (i.e (Σ; Unit -> Γ. ·; Unit) to fork, got " ++ pretty tv)
{- T-Close -}
typeE ctx st (Close v) = do
  tv <- typeV' ctx v
  case tv of
    EChan d1 -> stSplitDom ctx st d1 >>= \case
        Just (r , SEnd) -> do
          ok ([], r, EUnit)
        _ -> raise ("[T-Close] expected closable channel (i.e End) along its state binding, got " 
                    ++ pretty tv ++ " and " ++ pretty st)
    _ -> raise ("[T-Close] expected channel to close, got " ++ pretty tv)
{- T-Select -}
typeE ctx st (Sel l v) = do 
  tv <- typeV' ctx v
  case tv of 
    EChan d1 -> stSplitDom ctx st d1 >>= \case 
        Just (r , SChoice cl cr) -> case l of 
            LLeft -> ok ([], SSMerge r (SSBind d1 cl), EUnit)
            LRight -> ok ([], SSMerge r (SSBind d1 cr), EUnit)
        _ -> raise ("[T-Select] expected selectable channel (i.e s + s') along its state binding, got " 
                    ++ pretty tv ++ " and " ++ pretty st)
    _ -> raise ("[T-Select] expected channel to select from, got " ++ pretty tv)
{- T-Case -}
typeE ctx st (Case v e1 e2) = do 
  tv <- typeV' ctx v
  case tv of 
    (EChan d1) -> stSplitDom ctx st d1 >>= \case
        Just (r , SBranch s1 s2) -> do    
          tri1 @ (ctxl, stl, tl) <- typeE' ctx (SSMerge r (SSBind d1 s1)) e1
          tri2 @ (ctxr, str, tr) <- typeE' ctx (SSMerge r (SSBind d1 s2)) e2
          existEq ctx tri1 tri2 
          ok (ctxl, stl, tl)
        _ -> raise ("[T-Select] expected branched channel (i.e s & s') along a state including its binding, got " 
                    ++ pretty tv ++ " and " ++ pretty st)
    _ -> raise ("[T-Select] expected channel to case split on got " ++ pretty tv)
{- T-BinOp -}
typeE ctx st (BinOp v1 op v2) = do
  tv1 <- typeV' ctx v1
  tv2 <- typeV' ctx v2
  let opt t = (do
        tEq ctx tv1 t 
        tEq ctx tv2 t
        ok ([], st, t))
  case op of
    Add -> opt EInt
    Sub -> opt EInt
    Mul -> opt EInt
    Div -> opt EInt
    And -> opt EBool
    Or -> opt EBool

typeP :: (MonadError String m, MonadState Int m) => Program -> m ()
typeP (abs, cbs, es) = do
  ctx <- typeCA' [] abs
  (ctx', st') <- typeCC' ctx SSEmpty cbs
  st'' <- typeCE' ctx' st' es
  tEq ctx' st'' SSEmpty 

typeCA' :: (MonadError String m, MonadState Int m) => Ctx -> [AccBind] -> m Ctx
typeCA' ctx abs = catchError (typeCA ctx abs) $ \err -> 
  raise $ err ++ "\n\n-----------::        type of         ::-----------\n---- binds ----\n" 
              ++ pretty abs ++ "\n----  ctx  ----\n[" ++ pretty ctx ++ "]"

typeCA :: (MonadError String m, MonadState Int m) => Ctx -> [AccBind] -> m Ctx
typeCA ctx [] = ok ctx
typeCA ctx ((s, t) : xs) = case t of
    EAcc ty -> do 
      kt <- kind ctx ty
      kEq ctx kt KSession
      let ctx' = tExt ctx (s, t)
      typeCA' ctx' xs
    _ -> raise ("[T-NuAccess] expected access point binding, got " ++ pretty t)


typeCC' :: (MonadError String m, MonadState Int m) => Ctx -> Type -> [ChanBind] -> m (Ctx, Type)
typeCC' ctx st cbs = catchError (typeCC ctx st cbs) $ \err -> 
  raise $ err ++ "\n\n-----------::        type of         ::-----------\n---- binds ----\n" 
              ++ pretty cbs ++ "\n----  ctx  ----\n[" ++ pretty ctx ++ "]\n---- state ----\n" ++ pretty st

typeCC :: (MonadError String m, MonadState Int m) => Ctx -> Type -> [ChanBind] -> m (Ctx, Type) 
typeCC ctx st [] = ok (ctx, st)
typeCC ctx st (((s, s'), t) : xs) = do
  kt <- kind ctx t
  kEq ctx kt KSession
  let ctx' = dce ctx [(s, HasKind (KDom SHSingle)), (s', HasKind (KDom SHSingle))]
  tnf <- tNf (SDual t)
  typeCC' ctx' (SSMerge st (SSMerge (SSBind (TVar s) t) (SSBind (TVar s') tnf))) xs

typeCE' :: (MonadError String m, MonadState Int m) => Ctx -> Type -> [Expr] -> m Type
typeCE' ctx st es = catchError (typeCE ctx st es) $ \err -> 
  raise $ err ++ "\n\n-----------::        type of         ::-----------\n---- exprs ----\n" 
              ++ pretty es ++ "\n----  ctx  ----\n[" ++ pretty ctx ++ "]\n---- state ----\n" ++ pretty st

typeCE :: (MonadError String m, MonadState Int m) =>  Ctx -> Type -> [Expr] -> m Type
typeCE ctx st [] = ok st
typeCE ctx st (e : xs) = do
  (_, st', _) <- typeE' ctx st e
  _ <- stSplitSt ctx st st'
  typeCE' ctx st' xs
