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

data Type 
  = TVar Int
  | TApp Type Type
  | TLam Shape Type
  | TExpr ExprType
  | TSess Session
  | TDom Dom
  | TState State

data ExprType
  = TForAll Kind Config ExprType
  | TArr (State, ExprType) (State, ExprType)
  | TChan Dom
  | TAccess Session
  | TUnit
  | TPair ExprType ExprType

data Session
  = SSend Shape State ExprType Session
  | SRecv Shape State ExprType Session
  | SChoice Session Session
  | SBranch Session Session
  | SEnd
  | SDual Session

data Dom
  = DEmpty  
  | DTree Dom Dom
  | DProj Label Dom

data State
  = SSEmpty
  | SSMap Dom Session
  | SSTree State State

data Config