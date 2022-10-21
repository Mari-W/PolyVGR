module Ast where

data Kind
  = KType
  | KSession
  | KState
  | KShape
  | KDom Type
  | KArr Kind Kind
  deriving (Show, Eq, Ord)

data Label
  = LLeft
  | LRight
  deriving (Show, Eq, Ord)

data Type
  = TVar String
  | TApp Type Type
  | TLam String Kind Type 
  | EAll String Kind [Cstr] Type
  | EArr Type Type Ctx Type Type
  | EChan Type
  | EAcc Type
  | EUnit
  | EInt
  | EPair Type Type
  | SSend String Kind Type Type Type
  | SRecv String Kind Type Type Type
  | SChoice Type Type
  | SBranch Type Type
  | SEnd
  | SDual Type
  | SHEmpty
  | SHSingle
  | SHMerge Type Type
  | DEmpty
  | DMerge Type Type
  | DProj Label Type
  | SSEmpty
  | SSBind Type Type
  | SSMerge Type Type
  deriving (Show, Eq, Ord)

data Expr 
  = Let String Expr Expr
  | Val Val
  | Proj Label Val
  | App Val Val
  | AApp Val Type
  | Fork Val
  | Acc Val
  | Req Val
  | Send Val Val
  | Recv Val
  | Sel Label Val
  | Case Val Expr Expr
  | Close Val
  | New Type
  deriving (Show, Eq, Ord)

data Val 
  = VVar String
  | VInt Integer
  | VUnit
  | VPair Val Val
  | VTAbs String Kind [Cstr] Val
  | VChan Type
  | VAbs Type String Type Expr
  deriving (Show, Eq, Ord)

type Cstr = (Type, Type)

data Has
  = HasType Type
  | HasKind Kind
  | HasCstr Cstr
  deriving (Show, Eq, Ord)

type Ctx = [(String, Has)]

type ChanBind = ((String, String), Type)
type AccBind = (String, Type)
type Program = ([AccBind], [ChanBind], [Expr])

data ExprCtx
  = ECHole   
  | ECLet String ExprCtx Expr
  deriving (Show, Eq, Ord)