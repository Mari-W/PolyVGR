module Kinding where

import Ast
import Context
import Equality
import Result
import Constraints

kwf :: Ctx -> Kind -> Result ()
kwf ctx KType = ok ()
kwf ctx KSession = ok ()
kwf ctx KState = ok ()
kwf ctx KShape = ok ()
kwf ctx (KDom t) = do
  k <- kind ctx t
  kEq k KShape
kwf ctx (KLam k k') = do
  kwf ctx k
  kwf ctx k'
  ok ()

cwf :: Ctx -> Result ()
cwf ctx = cwf' (rev ctx)

cwf' :: Ctx -> Result ()
cwf' [] = ok ()
cwf' ((x, h) : xs) = case h of 
  HasType t -> do 
    kt <- kind xs t
    kEq kt KType 
    cwf' xs
  HasKind k -> do 
    kwf xs k
    cwf' xs
  HasConstr (l, r) -> do
    kl <- kind xs l
    kr <- kind xs r
    case (kl, kr) of 
      (KDom _, KDom _) -> cwf' xs
      _ -> raise ("[CF-ConsCstr] expected domains as constraints, got " ++ show kl ++ " and " ++ show kr)   


kind :: Ctx -> Type -> Result Kind
{- K-Var -}
kind ctx (TVar s) = s *? ctx
{- K-App -}
kind ctx (TApp f a) = do
  kf <- kind ctx f
  ka <- kind ctx a
  case kf of
    KLam d c -> do
      kEq d ka
      ok c
    _ -> raise ("[K-App] expected type level abstraction to apply to, got " ++ show kf)
{- K-Lam -}
kind ctx (TLam s d t) = do
  kd <- kind ctx d
  case kd of
    KDom sh -> do
      ksh <- kind ctx sh
      kEq ksh KShape
      ctx' <- (s, kd) +* gd ctx
      kt <- kind ctx' t
      kEqs kt [KType, KState]
      ok (KLam kd kt)
    _ -> raise ("[K-Lam] can only abstract over domains, got " ++ show d)
{- K-All -}
kind ctx (EAll s k cs t) = do
  kNEq k KType 
  kNEq k KState 
  ctx' <- (s, k) +* ctx
  ctx' <- cs +-* ctx'
  cwf ctx'
  kt <- kind ctx' t
  kEq kt KType
  ok KType 
{- K-Arr -}
kind ctx (EArr s1 t1 ctx2 s2 t2) = do
  domOnly ctx2
  ks1 <- kind ctx s1
  kEq ks1 KState 
  kt1 <- kind ctx t1
  kEq kt1 KType 
  let ctx' = dce ctx ctx2
  cwf ctx'
  ks2 <- kind ctx' s2
  kEq ks2 KState 
  kt2 <- kind ctx' t2
  kEq kt2 KType 
  ok KType
{- K-Chan -}
kind ctx (EChan d) = do
  kd <- kind ctx d
  case kd of
    KDom SHSingle -> ok KType
    _ -> raise ("[K-Chan] expected single domain, got " ++ show kd)
{- K-AccessPoint -}
kind ctx (EAcc s) = do
  ks <- kind ctx s
  kEq ks KSession
  ok KType
{- K-Unit -}
kind ctx EUnit = ok KType
{- K-Pair -}
kind ctx (EPair l r) = do
  kl <- kind ctx l
  kr <- kind ctx r
  kEq kl KType
  kEq kr KType
  ok KType
{- K-Send -}
kind ctx (SSend s k ss t c) = do
  kc <- kind ctx c
  kEq kc KSession
  case k of
    KDom sh -> do
      ksh <- kind ctx sh
      kEq ksh KShape
      ctx' <- (s, k) +* gd ctx
      kss <- kind ctx' ss
      kEq kss KState
      kt <- kind ctx' t
      kEq kt KType
      ok KSession
    _ -> raise ("[K-Recv] can only abstract over domains, got " ++ show k)
{- K-Recv -}
kind ctx (SRecv s k ss t c) = do
  kc <- kind ctx c
  kEq kc KSession
  case k of
    KDom sh -> do
      ksh <- kind ctx sh
      kEq ksh KShape
      ctx' <- (s, k) +* gd ctx
      kss <- kind ctx' ss
      kEq kss KState
      kt <- kind ctx' t
      kEq kt KType
      ok KSession
    _ -> raise ("[K-Recv] can only abstract over domains, got " ++ show k)
{- K-Branch -}
kind ctx (SBranch l r) = do
  kl <- kind ctx l
  kEq kl KSession
  kr <- kind ctx r
  kEq kr KSession
  ok KSession
{- K-Choice -}
kind ctx (SChoice l r) = do
  kl <- kind ctx l
  kEq kl KSession
  kr <- kind ctx r
  kEq kr KSession
  ok KSession
{- K-End -}
kind ctx SEnd = ok KSession
{- K-Dual -}
kind ctx (SDual s) = do
  ks <- kind ctx s
  kEq ks KSession
  ok KSession
{- K-ShapeEmpty -}
kind ctx SHEmpty = ok KShape
{- K-ShapeChan -}
kind ctx SHSingle = ok KShape
{- K-ShapePair -}
kind ctx (SHDisjoint l r) = do
  kl <- kind ctx l
  kEq kl KShape
  kr <- kind ctx r
  kEq kr KShape
  ok KShape
{- K-EmptyDom -}
kind ctx DEmpty = ok (KDom SHEmpty)
{- K-DomMerge -}
kind ctx (DMerge l r) = do
  kl <- kind ctx l
  case kl of
    KDom shl -> do
      kshl <- kind ctx shl
      kEq kshl KShape
      kr <- kind ctx r
      case kr of
        KDom shr -> do
          kshr <- kind ctx shr
          kEq kshr KShape
          ok (KDom (SHDisjoint shl shr))
        _ -> raise ("[K-DomMerge] expected to merge domains, got " ++ show r)
    _ -> raise ("[K-DomMerge] expected to merge domains, got " ++ show l)
{- K-DomProj -}
kind ctx (DProj l d) = do
  kd <- kind ctx d
  case kd of
    KDom (SHDisjoint shl shr) -> do
      kshl <- kind ctx shl
      kEq kshl KShape
      kshr <- kind ctx shr
      kEq kshr KShape
      case l of
        LLeft -> ok (KDom shl)
        LRight -> ok (KDom shr)
    _ -> raise ("[K-DomProj] expected merged domain, got " ++ show d)
{- K-StEmpty -}
kind ctx SSEmpty = ok KState
{- K-StChan -}
kind ctx (SSBind d s) = do
  ks <- kind ctx s
  kEq ks KSession
  kd <- kind ctx d
  case kd of
    KDom SHSingle -> do
      ok KState
    _ -> raise ("[K-StChan] expected single domain, got " ++ show d)
{- K-StMerge -}
kind ctx (SSMerge ssl ssr) = do
  stateDisjunct ssl ssr
  kssl <- kind ctx ssl
  kEq kssl KState
  kssr <- kind ctx ssr
  kEq kssr KState
  ok KState
