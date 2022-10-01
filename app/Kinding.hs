module Kinding where

import Ast
import Context
import Equality
import Result

kf :: Ctx -> Kind -> Result ()
kf ctx KType = ok ()
kf ctx KSession = ok ()
kf ctx KState = ok ()
kf ctx KShape = ok ()
kf ctx (KDom t) = do
  k <- kind ctx t
  kEq ctx k KShape
kf ctx (KLam k k') = do
  kf ctx k
  kf ctx k'
  ok ()

kind :: Ctx -> Type -> Result Kind
{- K-Var -}
kind ctx (TVar s) = s *? ctx
{- K-App -}
kind ctx (TApp f a) = do
  f' <- kind ctx f
  a' <- kind ctx a
  case f' of
    KLam d c -> do
      kEq ctx d a'
      ok c
    _ -> raise ("[K-App] expected type level abstraction to apply to, got " ++ show f')
{- K-Lam -}
kind ctx (TLam s d t) = do
  kd <- kind ctx d
  case kd of
    KDom sh -> do
      sh' <- kind ctx sh
      kEq ctx sh' KShape
      ctx' <- (s, sh') +* gd ctx
      k <- kind ctx' t
      kEqs ctx' k [KType, KState]
      ok (KLam kd k)
    _ -> raise ("[K-Lam] can only abstract over domains, got " ++ show d)
{- K-All -}
kind ctx (EAll s k cs t) = todo
{- K-Arr -}
kind ctx (EArr s1 t1 s2 t2) = todo
{- K-Chan -}
kind ctx (EChan d) = do
  d' <- kind ctx d
  case d' of
    KDom SHSingle -> ok KType
    _ -> raise ("[K-Chan] expected single domain, got " ++ show d')
{- K-AccessPoint -}
kind ctx (EAcc s) = do
  s' <- kind ctx s
  kEq ctx s' KSession
  ok KType
{- K-Unit -}
kind ctx EUnit = ok KType
{- K-Pair -}
kind ctx (EPair l r) = do
  l' <- kind ctx l
  r' <- kind ctx r
  kEq ctx l' KType
  kEq ctx r' KType
  ok KType
{- K-Send -}
kind ctx (SSend s d ss t cont) = do
  cont' <- kind ctx cont
  kEq ctx cont' KSession
  d' <- kind ctx d
  case d' of
    KDom sh -> do
      sh' <- kind ctx sh
      kEq ctx sh' KShape
      ctx' <- (s, sh') +* gd ctx
      ss' <- kind ctx' ss
      kEq ctx' ss' KState
      t' <- kind ctx' t
      kEq ctx' t' KType
      ok KSession
    _ -> raise ("[K-Recv] can only abstract over domains, got " ++ show d)
{- K-Recv -}
kind ctx (SRecv s d ss t cont) = do
  cont' <- kind ctx cont
  kEq ctx cont' KSession
  d' <- kind ctx d
  case d' of
    KDom sh -> do
      sh' <- kind ctx sh
      kEq ctx sh' KShape
      ctx' <- (s, sh') +* gd ctx
      ss' <- kind ctx' ss
      kEq ctx' ss' KState
      t' <- kind ctx' t
      kEq ctx' t' KType
      ok KSession
    _ -> raise ("[K-Recv] can only abstract over domains, got " ++ show d)
{- K-Branch -}
kind ctx (SBranch s1 s2) = do
  s1' <- kind ctx s1
  kEq ctx s1' KSession
  s2' <- kind ctx s2
  kEq ctx s2' KSession
  ok KSession
{- K-Choice -}
kind ctx (SChoice s1 s2) = do
  s1' <- kind ctx s1
  kEq ctx s1' KSession
  s2' <- kind ctx s2
  kEq ctx s2' KSession
  ok KSession
{- K-End -}
kind ctx SEnd = ok KSession
{- K-Dual -}
kind ctx (SDual s) = do
  s' <- kind ctx s
  kEq ctx s' KSession
  ok KSession
{- K-ShapeEmpty -}
kind ctx SHEmpty = ok KShape
{- K-ShapeChan -}
kind ctx SHSingle = ok KShape
{- K-ShapePair -}
kind ctx (SHDisjoint sh1 sh2) = do
  sh1' <- kind ctx sh1
  kEq ctx sh1' KShape
  sh2' <- kind ctx sh2
  kEq ctx sh2' KShape
  ok KShape
{- K-EmptyDom -}
kind ctx DEmpty = ok (KDom SHEmpty)
{- K-DomMerge -}
kind ctx (DMerge d1 d2) = do
  d1' <- kind ctx d1
  case d1' of
    KDom sh1 -> do
      sh1' <- kind ctx sh1
      kEq ctx sh1' KShape
      d2' <- kind ctx d2
      case d2' of
        KDom sh2 -> do
          sh2' <- kind ctx sh2
          kEq ctx sh2' KShape
          ok (KDom (SHDisjoint sh1 sh2))
        _ -> raise ("[K-DomMerge] expected to merge domains, got " ++ show d2)
    _ -> raise ("[K-DomMerge] expected to merge domains, got " ++ show d1)
{- K-DomProj -}
{- !! check disjointness -}
kind ctx (DProj l d) = do
  d' <- kind ctx d
  case d' of
    KDom (SHDisjoint sh1 sh2) -> do
      sh1' <- kind ctx sh1
      kEq ctx sh1' KShape
      sh2' <- kind ctx sh2
      kEq ctx sh2' KShape
      case l of
        LLeft -> ok (KDom sh1)
        LRight -> ok (KDom sh2)
    _ -> raise ("[K-DomProj] expected merged domain, got " ++ show d)
{- K-StEmpty -}
kind ctx SSEmpty = ok KState
{- K-StChan -}
kind ctx (SSBind d s) = do
  s' <- kind ctx s
  kEq ctx s' KSession
  d' <- kind ctx d
  case d' of
    KDom SHSingle -> do
      ok KState
    _ -> raise ("[K-StChan] expected single domain, got " ++ show d)
{- K-StMerge -}
{- !! check disjointness -}
kind ctx (SSMerge ss1 ss2) = do
  ss1' <- kind ctx ss1
  kEq ctx ss1' KState
  ss2' <- kind ctx ss2
  kEq ctx ss2' KState
  ok KState
