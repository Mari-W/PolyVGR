{-# LANGUAGE FlexibleContexts #-}
module Parser where

import Ast
    ( Expr(..),
      Has(HasKind),
      Kind(KArr, KType, KSession, KState, KShape, KDom),
      Label(LRight, LLeft),
      Type(SSEmpty, SSMerge , TApp, TLam, EAll, EArr, EChan, EAcc, EUnit, EPair,
           SSend, SRecv, SChoice, SBranch, SEnd, SDual, SHEmpty, SHSingle,
           SHMerge, DEmpty, DProj, SSBind, DMerge, TVar, EInt),
      Val(VPair, VVar, VChan, VAbs, VTAbs, VUnit, VInt) )
import Result (Result, ok, raise, ResultT)
import Text.ParserCombinators.Parsec
    ( alphaNum, letter, parse, many, many1, optional, space, noneOf, option, sepBy1, unexpected, eof, (<|>), sepBy, oneOf, try, lookAhead )
import qualified Text.ParserCombinators.Parsec.Token as Token
import Data.List (isInfixOf)
import Text.Parsec.Language (emptyDef)
import Control.Monad.IO.Class (liftIO)
import Text.Parsec.Combinator (optionMaybe)


parseFile :: String -> ResultT IO Expr
parseFile file = do
  prog <- liftIO $ readFile file
  case parse (whiteSpace *> expr1 <* whiteSpace <* eof) "" prog of
    Left pe -> liftIO $ print pe >> fail "parse error"
    Right ex -> return ex

parseString :: String -> Result Expr
parseString s = do
  case parse (whiteSpace *> expr1 <* whiteSpace <* eof) "" s of
    Left pe -> raise "parse error"
    Right ex -> ok ex

{- tokens -}

langDef = emptyDef {
  Token.commentStart = "/*",
  Token.commentEnd = "*/",
  Token.commentLine = "//",
  Token.identStart = letter,
  Token.identLetter = alphaNum,
  Token.reservedOpNames = ["->", "→", "=>", "⇒", "λ", "𝜆", "\\", "𝕀", "𝕏", "π₁", "π₂", "π", "Λ",  "·", "*", "+", "⊕", "↦", ";", ":", "×", "#", "~", "."],
  Token.reservedNames  = ["Type", "Session", "State", "Shape", "Dom", "left", "right", "proj1", "proj2", "all", "forall", "ex", "exists", "Chan", "Unit", "Int", "I", "X", "let", "in", "fork", "accept", "request", "send", "on", "receive", "select",  "case", "of", "close", "new", "chan", "unit"],
  Token.caseSensitive = True
}

lexer = Token.makeTokenParser langDef

identifier = Token.identifier lexer
reserved  = Token.reserved lexer
reservedOp = Token.reservedOp lexer
parens = Token.parens lexer
braces = Token.braces lexer
brackets = Token.brackets lexer
angles = Token.angles lexer
semi = Token.semi lexer
comma = Token.comma lexer
space = Token.whiteSpace lexer
commaSep1 = Token.commaSep1 lexer
commaSep = Token.commaSep lexer
semiSep1 = Token.semiSep1 lexer
whiteSpace = Token.whiteSpace lexer
integer = Token.integer lexer
symbol = Token.symbol lexer

{- keywords -}

kwFunArr = reservedOp "->" <|> reservedOp "→"
kwCstrArr = reservedOp "=>" <|> reservedOp "⇒"
kwTupTimes = reservedOp "*" <|> reservedOp "×"
kwLambda = reservedOp "λ" <|> reservedOp "𝜆" <|> reservedOp "\\"
kwForall = reserved "all" <|> reserved "forall" <|> reservedOp "∀"
kwExists = reserved "ex" <|> reserved "exists" <|> reservedOp "∃"
kwShEmpty = reservedOp "I" <|> reservedOp "𝕀"
kwShSingle = reservedOp "X" <|> reservedOp "𝕏"
kwTLambda = reservedOp "Λ" <|> reservedOp "\\\\"
kwProj1 = reservedOp "π₁" <|> reserved "proj1"
kwProj2 = reservedOp "π₂" <|> reserved "proj2"
kwLab1 = reservedOp "1" <|> reserved "left"
kwLab2 = reservedOp "2" <|> reserved "right"
kwCtxEmpty = reservedOp "*" <|> reservedOp "·"
kwChoice = reservedOp "+" <|> reservedOp "⊕"
kwBind = reservedOp "->" <|> reservedOp "↦" <|> reservedOp "→"


kType = do
  reserved "Type"
  return KType

kSession = do
  reserved "Session"
  return KSession

kState = do
  reserved "State"
  return KState

kShape = do
  reserved "Shape"
  return KShape

kDom = do
  reserved "Dom"
  KDom <$> shape2

kind1 = foldr1 KArr <$> sepBy1 kind2 kwFunArr
kind2 = kType <|> kSession <|> kState <|> kShape <|> kDom <|> parens kind1


{- labels -}

lLeft = do
  kwLab1
  return LLeft

lRight = do
  kwLab2
  return LRight

label = lLeft <|> lRight

lProj1 = do
  kwProj1
  return LLeft

lProj2 = do
  kwProj2
  return LRight

lProj = lProj1 <|> lProj2


{- types -}

tVar = TVar <$> identifier

tApp = do
  f <- parens tLam <|> tVar
  TApp f <$> dom3

domBind = do
  id <- identifier
  reservedOp ":"
  d <- kDom
  return (id, d)

tLam = do
  kwLambda
  (id, d) <- parens domBind
  reservedOp "."
  c <- braces state1 <|> et1
  return (TLam id d c)

cstr = do
  t1 <- dom2
  reservedOp "#"
  t2 <- dom2
  return (t1, t2)
cstrs = do
  commaSep1 cstr

kBind = do
  id <- identifier
  reservedOp ":"
  k <- kind1
  return (id, k)

et1 = eAll <|> et2
et2 = foldr1 EPair <$> sepBy1 et4 kwTupTimes
et4 = eChan <|> eUnit <|> eInt <|> eAcc <|> eArr <|> try (parens et1) <|> tApp

eAll = do
  kwForall
  (id, k) <- parens kBind
  reservedOp "."
  cs <- option [] (try $ do
      cs <- parens cstrs
      kwCstrArr
      return cs)
  EAll id k cs <$> et1

ctxBind = do
  id <- identifier
  reservedOp ":"
  k <- kDom
  return (id, HasKind k)
ctxBinds = commaSep1 ctxBind
ctxEmpty = do
  kwCtxEmpty
  return []
ctx1 = ctxEmpty <|> ctxBinds

stTy = do
  st <- braces state1
  reservedOp ";"
  t <- et1
  return (st, t)

ctxStTy = do
  ctx <- option [] (do
    kwExists
    ctx <- ctx1
    reservedOp "."
    return ctx)
  (st, t) <- stTy
  return (ctx, st, t)

isArr = try $ lookAhead $ do
    symbol "("
    symbol "{"

eArr = isArr *> parens (do
  (st1, t1) <- stTy
  kwFunArr
  (ctx, st2, t2) <- ctxStTy
  return (EArr st1 t1 ctx st2 t2))

eChan = do
  reserved "Chan"
  EChan <$> dom3

eAcc = EAcc <$> brackets session1

eUnit = do
  reserved "Unit"
  return EUnit

eInt = do
  reserved "Int"
  return EInt


domStTy = do
  kwExists
  (id, d) <- domBind
  reservedOp "."
  (st, t) <- stTy
  return (id, d, st, t)

session1 = foldr1 SBranch <$> sepBy1 session2 (reservedOp "&")
session2 = foldr1 SChoice <$> sepBy1 session3 kwChoice
session3 = sSend <|> sRecv <|> session4
session4 = sDual <|> session5
session5 = sEnd <|> tVar <|> parens session1

sSend = do
  reservedOp "!"
  (id, d, st, t) <- parens domStTy
  reservedOp "."
  SSend id d st t <$> session3

sRecv = do
  reservedOp "?"
  (id, d, st, t) <- parens domStTy
  reservedOp "."
  SRecv id d st t <$> session3

sEnd = do
  reserved "End"
  return SEnd

sDual = do
  reservedOp "~"
  SDual <$> session4

shape1 = foldr1 SHMerge <$> semiSep1 shape2
shape2 = shEmpty <|> shSingle <|> tVar <|> parens shape1

shEmpty = do
  kwShEmpty
  return SHEmpty

shSingle = do
  kwShSingle
  return SHSingle

shMerge = do
  t <- shape2
  SHMerge t <$> shape2

dom1 = foldr1 DMerge <$> commaSep1 dom2
dom2 = dProj <|> dom3
dom3 = dEmpty <|> tVar <|> parens dom1

dEmpty = do
  reservedOp "*"
  return DEmpty

dMerge = do
  t <- dom2
  reservedOp ","
  DMerge t <$> dom1

dProj = do
  l <- lProj
  DProj l <$> dom3

state1 = foldr SSMerge SSEmpty <$> commaSep state2 <* optional (reservedOp ",")

state2 = do
  d <- dom3
  let pb = SSBind d <$ kwBind <*> session1
  case d of
    TVar s -> TApp d <$> dom3 <|> pb
    _ -> pb


{- expressions & values -}

let1 = do
  reserved "let"
  var <- identifier
  reservedOp "="
  exp <- expr1
  reserved "in"
  Let var exp <$> expr1

proj = do
  l <- lProj
  Proj l <$> val1

fork = do
  reserved "fork"
  Fork <$> val1

acc = do
  reserved "accept"
  Acc <$> val1

req = do
  reserved "request"
  Req <$> val1

send = do
  reserved "send"
  v <- val1
  reserved "on"
  Send v <$> val1

recv = do
  reserved "receive"
  Recv <$> val1

sel = do
  reserved "select"
  v <- label
  reserved "on"
  Sel v <$> val1

case1 = do
  reserved "case"
  v <- val1
  reserved "of"
  (e, e_) <- braces (do
    e <- expr1
    reservedOp ";"
    e_ <- expr1
    return (e, e_))
  return (Case v e e_)

close = do
  reserved "close"
  Close <$> val1

new = do
  reserved "new"
  New <$> session1

val = Val <$> val1

vVar = VVar <$> identifier

vChan = do
  reserved "chan"
  VChan . TVar <$> identifier

stBindTy = do
  st <- braces state1
  reservedOp ";"
  id <- identifier
  reservedOp ":"
  t <- et1
  return (st, id, t)

vAbs = do
  kwLambda
  (st, id, t) <- parens stBindTy
  reservedOp "."
  VAbs st id t <$> expr1

vTAbs = do
  kwTLambda
  (id, k) <- parens kBind
  reservedOp "."
  cs <- option [] (do
    cs <- parens cstrs
    kwCstrArr
    return cs)
  VTAbs id k cs <$> val1

vUnit = do
  reserved "unit"
  return VUnit

vInt =  VInt <$> integer

vPair = angles $ do
  v <- val1
  reservedOp ","
  VPair v <$> val1

aapp v = do
  t <- brackets (tLam <|> dom1 <|> shape1 <|> session1)
  return $ AApp v t

expr1 = let1 <|> expr2
expr2 = expr3 <|> (do
  l <- many1 val1
  case l of
    [] -> undefined
    [v] -> do
      mt <- optionMaybe $ brackets (tLam <|> dom1 <|> shape1 <|> session1)
      case mt of
        Nothing -> return $ Val v
        Just t -> return $ AApp v t
    [v1, v2] -> return $ App v1 v2
    _ -> unexpected "nested applications not allowed in A-normal form")
expr3 = fork <|> acc <|> req <|> send <|> recv <|> sel <|> case1 <|> close <|> new <|> proj <|> parens expr1

val1 = vAbs <|> vTAbs <|> val2
val2 = vChan <|> vUnit <|> vPair <|> parens val1 <|> vInt <|> vVar