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

type Constr = (Dom, Dom) 

data ExprType
  = ETVar Int
  | ETForAll Kind [Constr] ExprType
  | ETArr (State, ExprType) (State, ExprType)
  | ETChan Dom
  | ETAccess Session
  | ETUnit
  | ETPair ExprType ExprType

data Session
  = SVar Int
  | SSend Shape State ExprType Session
  | SRecv Shape State ExprType Session
  | SChoice Session Session
  | SBranch Session Session
  | SEnd
  | SDual Session

data Dom
  = DVar Int
  | DEmpty  
  | DTree Dom Dom
  | DProj Label Dom

data State
  = SSEmpty
  | SSMap Dom Session
  | SSTree State State
