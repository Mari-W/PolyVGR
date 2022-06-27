module Ast where

data Kind
  = KType
  | KSession
  | KState
  | KShape
  | KDom Shape
  | KLam Kind Kind

data Label
  = LLeft
  | LRight

data Shape
  = SEmpty
  | SSingle
  | SDisjoint Shape Shape

data ExprType
  = TForAll Kind Config ExprType
  | TLam ((SessState, ExprType) -> (SessState, ExprType))
  | TChan Dom
  | TAccess SessType
  | TUnit
  | TTup ExprType ExprType

data SessType
  = SSend
  | SRecv
  | SChoice SessType SessType
  | SBranch SessType SessType
  | End
  | Dual SessType

data Dom
  = DEmpty
  | DTree Shape Shape
  | DProj Label Dom

data SessState
  = SSEmpty
  | SSMap Dom SessType
  | SSTree SessState SessState

data Config

data Has
  = HasType ExprType
  | HasKind Kind
  | HasDisCon Dom Dom

type Ctx = [Has]