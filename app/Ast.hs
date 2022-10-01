module Ast where
  
data Kind
  = KType
  | KSession
  | KState
  | KShape
  | KDom Type
  | KLam Kind Kind
  deriving (Show, Eq)

data Type
  = TVar String
  | TApp Type Type
  | TLam String Type Type
  | EAll String Kind [Constr] Type
  | EArr Type Type Type Type
  | EChan Type
  | EAcc Type
  | EUnit
  | EPair Type Type
  | SSend String Type Type Type Type
  | SRecv String Type Type Type Type
  | SChoice Type Type
  | SBranch Type Type
  | SEnd
  | SDual Type
  | SHEmpty
  | SHSingle
  | SHDisjoint Type Type
  | DEmpty
  | DMerge Type Type
  | DProj Label Type
  | SSEmpty
  | SSBind Type Type
  | SSMerge Type Type
  deriving (Show, Eq)

data Expr 
  = Var String
  | Let String Expr Expr
  | App Expr Expr
  | Abs Type String Type Expr
  | TAbs String Kind [Constr] Expr
  | Pair Expr Expr
  | Proj Label Expr
  | AApp Expr Type
  | Fork Expr
  | Acc Expr
  | Req Expr
  | Send Expr
  | Recv Expr
  | Sel Label Expr
  | Case Expr Expr Expr
  | Close Expr
  | New Type
  | Unit

data Val 
  = VVar String
  | VChan String
  | VAbs Type String Type Expr
  | VTAvs String Kind [Constr] Val
  | VUnit
  | VPair Val Val

data Label
  = LLeft
  | LRight
  deriving (Show, Eq)

type Constr = (Type, Type)