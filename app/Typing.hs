module Typing where

import Ast
import Constraints
import Context
import Conversion
import Equality
import Kinding
import Result
import State
import Substitution

typeV :: Ctx -> Val -> Result Type
{- T-Var -}
typeV ctx (VVar x) = do 
  t <- x .? ctx
  ok t
{- T-Unit -}
typeV ctx VUnit = ok EUnit
{- T-Pair -}
typeV ctx (VPair l r) = do
  tl <- typeV ctx l
  tr <- typeV ctx r
  ok (EPair tl tr)
{- T-TAbs -}
typeV ctx (VTAbs s k cs v) = do
  ctx' <- cs +-* ctx
  ctx' <- (s, k) +* ctx'
  tv <- typeV ctx' v
  kt <- kind ctx tv
  kEq ctx kt KType
  ok tv
{- T-Chan -}
typeV ctx (VChan d) = do
  d' <- kind ctx d
  case d' of
    KDom SHSingle -> ok (EChan d)
    _ -> raise ("[VT-Chan] expected single domain, got " ++ show d')
{- T-Abs -}
typeV ctx (VAbs st s t e) = do
  ctx' <- (s, t) +. ctx
  (ctx', st', te) <- typeE ctx' st e
  ke <- kind ctx te
  kEq ctx ke KType 
  ok (EArr st t ctx' st' te)

typeE :: Ctx -> Type -> Expr -> Result (Ctx, Type, Type)
{- T-Let -}
typeE ctx st (Let s e1 e2) = do
  (ctx1, ss1, t1) <- typeE ctx st e1
  let ctx' = dce ctx ctx1
  ctx' <- (s, t1) +. ctx'
  (ctx2, ss2, t2) <- typeE ctx' ss1 e2
  ok (ctx1 ++ ctx2, ss2, t2)
{- T-Val -}
typeE ctx st (Val v) = do
  tv <- typeV ctx v
  ok ([], st, tv)
{- T-Proj -}
typeE ctx st (Proj l v) = do
  tv <- typeV ctx v
  case (l, tv) of       
    (LLeft, EPair t _) -> ok ([], st, t)
    (LRight, EPair _ t) -> ok ([], st, t)
    _ -> raise ("[T-Proj] expected to project out of pair, got " ++ show tv)
{- T-App -}
typeE ctx st (App v a) = do
  tv <- typeV ctx v
  case tv of
    EArr st1 t1 ctx1 st2 t2 -> do
      {- splitte st1 aus st -}
      ta <- typeV ctx a
      tEq ctx t1 ta
      ok ([], st2, t2)
    _ -> raise ("[T-App] expected to apply to function, got " ++ show tv)
{- T-TApp -}
typeE ctx st (AApp v t) = do
  tv <- typeV ctx v
  case tv of
    EAll s k cs c -> do
      kt <- kind ctx t
      kEq ctx kt k
      ce ctx (subCstrs s t cs)
      ok ([], st, tNf (subT s t c))
    _ -> raise ("[T-TApp] expected to apply to forall abstraction, got " ++ show tv)
{- T-New -}
typeE ctx st (New t) = do
  kt <- kind ctx t
  kEq ctx kt KSession 
  ok ([], st, EAcc t)
{- T-Request -}
typeE ctx st (Req v) = do
  tv <- typeV ctx v
  case tv of 
    EAcc t -> do
      let x = freshVar
      ok ([(x, HasKind (KDom SHSingle))], SSMerge st (SSBind (TVar x) t), EChan (TVar x))
    _ -> raise ("[T-Request] expected access point to request to, got " ++ show tv)
{- T-Accept -}
typeE ctx st (Acc v) = do
  tv <- typeV ctx v
  case tv of 
    EAcc t -> do
      let x = freshVar
      ok ([(x, HasKind (KDom SHSingle))], SSMerge st (SSBind (TVar x) (SDual t)), EChan (TVar x))
    _ -> raise ("[T-Accept] expected access point to request to, got " ++ show tv)
{- T-Send -}
typeE ctx st (Send v1 v2) = do 
  tv1 <- typeV ctx v1
  tv2 <- typeV ctx v2
  case tv2 of 
    EChan d1 -> do
      kd1 <- kind ctx d1
      kEq ctx kd1 (KDom SHSingle)
      sp <- stSplitDom ctx st d1
      case sp of 
        (r , Just (SSend x kd2 st1 t1 s)) -> do
          case kd2 of 
            KDom _ -> do
              kwf ctx kd2
              {- todo tEq r (subT x ? st1), tEq tv1 (subT x ? t1)-}
              ok ([], SSBind d1 s, EUnit)
            _ -> raise ("[T-Send] can only abstract over domains, got " ++ show kd2)
        _ -> raise ("[T-Send] expected send channel (i.e !s) along a state including their binding, got " ++ show tv1 ++ " and " ++ show st)
    _ -> raise ("[T-Send] expected channel to send on got " ++ show tv2)
{- T-Receive -}
typeE ctx st (Recv v) = do 
  tv <- typeV ctx v
  case tv of 
    EChan d1 -> do
      sp <- stSplitDom ctx st d1
      case sp of 
        (r , Just (SRecv x kd2 st1 t1 s)) -> do
          kwf ctx kd2
          kd1 <- kind ctx d1
          kEq ctx kd1 (KDom SHSingle)
          ok ([(x, HasKind kd2)], SSMerge r (SSMerge st1 (SSBind d1 s)), t1)
        _ -> raise ("[T-Recv] expected receive channel (i.e ?s) along a state including their binding, got " ++ show tv ++ " and " ++ show st)
    _ -> raise ("[T-Send] expected channel to receive (i.e ?s) on got along their state binding" ++ show tv ++ " and " ++ show st)
{- T-Fork -}
typeE ctx st (Fork v) = do 
  tv <- typeV ctx v
  case tv of
    EArr st1 EUnit ctx2 SSEmpty EUnit -> ok ([], st, EUnit)
    _ -> raise ("[T-Fork] expected Process (i.e Unit -> Unit) to fork, got" ++ show tv)
{- T-Close -}
typeE ctx st (Close v) = do
  tv <- typeV ctx v
  case tv of
    EChan d1 -> do
      sp <- stSplitDom ctx st d1
      case sp of 
        (r , Just SEnd) -> do
          ok ([], r, EUnit)
        _ -> raise ("[T-Close] expected closable channel (i.e End) along their state binding, got " ++ show tv ++ " and " ++ show st)
    _ -> raise ("[T-Close] expected channel to close, got " ++ show tv)
{- T-Select -}
typeE ctx st (Sel l v) = do 
  tv <- typeV ctx v
  case tv of 
    EChan d1 -> do
      sp <- stSplitDom ctx st d1
      case sp of 
        (r , Just (SChoice cl cr)) -> do
          case l of 
            LLeft -> ok ([], SSMerge r (SSBind d1 cl), EUnit)
            LRight -> ok ([], SSMerge r (SSBind d1 cr), EUnit)
        _ -> raise ("[T-Select] expected selectable channel (i.e s + s') along their state binding, got " ++ show tv ++ " and " ++ show st)
    _ -> raise ("[T-Select] expected channel to select from, got " ++ show tv)
{- T-Case -}
typeE ctx st (Case v e1 e2) = do 
  tv <- typeV ctx v
  case tv of 
    (EChan d1) -> do
      sp <- stSplitDom ctx st d1
      case sp of
        (r , Just (SBranch s1 s2)) -> do    
          tri1 @ (ctxl, stl, tl) <- typeE ctx (SSMerge r (SSBind d1 s1)) e1
          tri2 @ (ctxr, str, tr) <- typeE ctx (SSMerge r (SSBind d1 s2)) e2
          existEq ctx tri1 tri2 
          ok (ctxl, stl, tl)
        _ -> raise ("[T-Select] expected branched channel (i.e s & s') along a state including their binding, got " ++ show tv ++ " and " ++ show st)
    _ -> raise ("[T-Select] expected channel to case split on got " ++ show tv)