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
           SBranch, SSEmpty, EAcc, SEnd, SHSingle, SSMerge, SSBind, TVar, EInt),
      Val(..) )
import Constraints ( ce )
import Context ( (+*), (+-*), (+.), (.?), dce, freshVar )
import Conversion ( tNf )
import Equality ( existEq, kEq, tEq, tUnify )
import Kinding ( kwf, cwf, kind', kind )
import Result ( ok, raise, Result )
import State ( stSplitDom, stSplitSt )
import Substitution ( renTM, subCstrs, subT )
import Pretty ( Pretty(pretty) )
import Debug.Trace

typeV' ctx v = case typeV ctx v of
  Right x -> Right x
  Left err -> Left $ err ++ "\n    type of " ++ pretty v ++ "\n         in [" ++ pretty ctx ++ "]"

typeV :: Ctx -> Val -> Result Type
{- T-Var -}
typeV ctx (VVar x) = do 
  t <- x .? ctx
  ok t
{- T-Unit -}
typeV ctx VUnit = ok EUnit
{- T-Nat -}
typeV ctx (VInt i)  = ok EInt
{- T-Pair -}
typeV ctx (VPair l r) = do
  tl <- typeV' ctx l
  tr <- typeV' ctx r
  ok (EPair tl tr)
{- T-TAbs -}
typeV ctx (VTAbs s k cs v) = do
  ctx' <- (s, k) +* ctx
  let ctx'' = cs +-* ctx'
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
  ctx' <- (s, t) +. ctx
  cwf ctx'
  (ctx', st', te) <- typeE' ctx' st e
  ke <- kind' ctx (EArr st t ctx' st' te)
  kEq ctx ke KType 
  ok (EArr st t ctx' st' te)

typeE' ctx st e = case typeE ctx st e of
  Right x -> Right x
  Left err -> Left $ err ++ "\n    type of " ++ pretty e ++ "\n         in [" ++ pretty ctx  ++ "]\n            {" ++ pretty st ++ "}"

typeE :: Ctx -> Type -> Expr -> Result (Ctx, Type, Type)
{- T-Let -}
typeE ctx st (Let s e1 e2) = do
  (ctx1, ss1, t1) <- typeE' ctx st e1
  let ctx' = dce ctx ctx1
  ctx' <- (s, t1) +. ctx'
  cwf ctx'
  (ctx2, ss2, t2) <- typeE' ctx' ss1 e2 
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
      ce ctx (subCstrs s t cs)
      ok ([], st, tNf (subT s t c))
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
      let x = freshVar "c"
      ok ([(x, HasKind (KDom SHSingle))], SSMerge st (SSBind (TVar x) t), EChan (TVar x))
    _ -> raise ("[T-Request] expected access point to request to, got " ++ pretty tv)
{- T-Accept -}
typeE ctx st (Acc v) = do
  tv <- typeV' ctx v
  case tv of 
    EAcc t -> let x = freshVar "c" in
      ok ([(x, HasKind (KDom SHSingle))], SSMerge st (SSBind (TVar x) (tNf (SDual t))), EChan (TVar x))
    _ -> raise ("[T-Accept] expected access point to request to, got " ++ pretty tv)
{- T-Send -}
typeE ctx st (Send v1 v2) = do 
  tv1 <- typeV' ctx v1
  tv2 <- typeV' ctx v2
  case tv2 of 
    EChan d1 -> do
      kd1 <- kind' ctx d1
      kEq ctx kd1 (KDom SHSingle)
      case stSplitDom ctx st d1 of 
        Just (r , SSend x kd2 st1 t1 s) -> case kd2 of 
            KDom sh -> do
              ksh <- kind' ctx sh
              kEq ctx ksh KShape
              u <- tUnify ctx [] tv1 t1
              let st1' = renTM u st1
              st' <- stSplitSt ctx r st1'
              ok ([], SSMerge st' (SSBind d1 s), EUnit)
            _ -> raise ("[T-Send] can only abstract over domains, got " ++ pretty kd2)
        _ -> raise ("[T-Send] expected send channel (i.e !s) along a state including its binding, got " ++ pretty tv1 ++ " and " ++ pretty st)
    _ -> raise ("[T-Send] expected channel to send on got " ++ pretty tv2)
{- T-Receive -}
typeE ctx st (Recv v) = do 
  tv <- typeV' ctx v
  case tv of 
    EChan d1 -> case stSplitDom ctx st d1 of 
        Just (r , SRecv x kd2 st1 t1 s) -> do
          kwf ctx kd2
          kd1 <- kind' ctx d1
          kEq ctx kd1 (KDom SHSingle)
          ok ([(x, HasKind kd2)], SSMerge r (SSMerge st1 (SSBind d1 s)), t1)
        _ -> raise ("[T-Recv] expected receive channel (i.e ?s) along a state including its binding, got " ++ pretty tv ++ " and " ++ pretty st)
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
    EChan d1 -> case stSplitDom ctx st d1 of 
        Just (r , SEnd) -> do
          ok ([], r, EUnit)
        _ -> raise ("[T-Close] expected closable channel (i.e End) along its state binding, got " ++ pretty tv ++ " and " ++ pretty st)
    _ -> raise ("[T-Close] expected channel to close, got " ++ pretty tv)
{- T-Select -}
typeE ctx st (Sel l v) = do 
  tv <- typeV' ctx v
  case tv of 
    EChan d1 -> case stSplitDom ctx st d1 of 
        Just (r , SChoice cl cr) -> case l of 
            LLeft -> ok ([], SSMerge r (SSBind d1 cl), EUnit)
            LRight -> ok ([], SSMerge r (SSBind d1 cr), EUnit)
        _ -> raise ("[T-Select] expected selectable channel (i.e s + s') along its state binding, got " ++ pretty tv ++ " and " ++ pretty st)
    _ -> raise ("[T-Select] expected channel to select from, got " ++ pretty tv)
{- T-Case -}
typeE ctx st (Case v e1 e2) = do 
  tv <- typeV' ctx v
  case tv of 
    (EChan d1) -> case stSplitDom ctx st d1 of
        Just (r , SBranch s1 s2) -> do    
          tri1 @ (ctxl, stl, tl) <- typeE' ctx (SSMerge r (SSBind d1 s1)) e1
          tri2 @ (ctxr, str, tr) <- typeE' ctx (SSMerge r (SSBind d1 s2)) e2
          existEq ctx tri1 tri2 
          ok (ctxl, stl, tl)
        _ -> raise ("[T-Select] expected branched channel (i.e s & s') along a state including its binding, got " ++ pretty tv ++ " and " ++ pretty st)
    _ -> raise ("[T-Select] expected channel to case split on got " ++ pretty tv)

typeP :: Program -> Result ()
typeP (abs, cbs, es) = do
  ctx <- typeCA' [] abs
  (ctx', st') <- typeCC' ctx SSEmpty cbs
  st'' <- typeCE' ctx' st' es
  tEq ctx' st'' SSEmpty 

typeCA' ctx abs = case typeCA ctx abs of
  Right x -> Right x
  Left err -> Left $ err ++ "\n    type of " ++ pretty abs ++ "\n         in [" ++ pretty ctx  ++ "]"

typeCA :: Ctx -> [AccBind] -> Result Ctx
typeCA ctx [] = ok ctx
typeCA ctx ((s, t) : xs) = case t of
    EAcc ty -> do 
      kt <- kind ctx ty
      kEq ctx kt KSession
      ctx' <- (s, t) +. ctx
      typeCA' ctx' xs
    _ -> raise ("[T-NuAccess] expected access point binding, got " ++ pretty t)

typeCC' ctx st cbs = case typeCC ctx st cbs of
  Right x -> Right x
  Left err -> Left $ err ++ "\n    type of " ++ pretty cbs ++ "\n         in [" ++ pretty ctx  ++ "]\n            {" ++ pretty st ++ "}"

typeCC :: Ctx -> Type -> [ChanBind] -> Result (Ctx, Type) 
typeCC ctx st [] = ok (ctx, st)
typeCC ctx st (((s, s'), t) : xs) = do
  kt <- kind ctx t
  kEq ctx kt KSession
  let ctx' = dce ctx [(s, HasKind (KDom SHSingle)), (s', HasKind (KDom SHSingle))]
  typeCC' ctx' (SSMerge st (SSMerge (SSBind (TVar s) t) (SSBind (TVar s') (tNf (SDual t))))) xs

typeCE' ctx st cbs = case typeCE ctx st cbs of
  Right x -> Right x
  Left err -> Left $ err ++ "\n    type of " ++ pretty cbs ++ "\n         in [" ++ pretty ctx  ++ "]"

typeCE :: Ctx -> Type -> [Expr] -> Result Type
typeCE ctx st [] = ok st
typeCE ctx st (e : xs) = do
  (_, st', _) <- typeE' ctx st e
  _ <- stSplitSt ctx st st'
  typeCE' ctx st' xs
