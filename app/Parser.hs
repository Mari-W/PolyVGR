{-# LANGUAGE FlexibleContexts, CPP #-}
module Parser where

import Ast
    ( Expr(..),
      Has(HasKind),
      Kind(KArr, KType, KSession, KState, KShape, KDom),
      Label(LRight, LLeft),
      Type(SSEmpty, SSMerge , TApp, TLam, EAll, EArr, EChan, EAcc, EUnit, EPair,
           SSend, SRecv, SChoice, SBranch, SEnd, SDual, SHEmpty, SHSingle,
           SHMerge, DEmpty, DProj, SSBind, DMerge, TVar),
      Val(VPair, VVar, VChan, VAbs, VTAbs, VUnit) )
import Result (Result, ok, raise)
import Text.ParserCombinators.Parsec
    ( alphaNum, letter, parse, spaces, string, many, char, many1, optional, space, noneOf, option, sepBy1, unexpected, try, eof, (<?>), (<|>), sepBy )
import Debug.Trace ( trace )
import Data.List (isInfixOf)

#define tl trace (__FILE__ ++":"++ show __LINE__)

parseFile :: String -> IO (Result Expr)
parseFile file = do
  prog <- readFile file
  case parse (spaces *> expr1 <* spaces <* eof) "" prog of
    Left pe -> print pe >> fail "parse error"
    Right ex -> return (ok ex)

parseString :: String -> Result Expr
parseString s = do
  case parse (spaces *> expr1 <* spaces <* eof) "" s of
    Left pe -> raise "parse error"
    Right ex -> ok ex


{- keywords -}

kws = ["Type", "Session", "State", "Shape", "Dom", "left", "right", "proj1", "proj2", "all", "forall", "ex", "exists", "Chan", "Unit", "I", "X", "let", "in", "fork", "accept", "request", "send", "on", "receive", "select",  "case", "of", "close", "new", "chan", "unit"]
syms = ["->", "→", "=>", "⇒", "λ", "𝜆", "\\", "𝕀", "𝕏", "π₁", "π₂", "π", "Λ", "{", "}", "(", ")",  "[", "]",  "·", "*", "+", "⊕", "↦", ";", ":", "×", "#", "~"]
kwFunArr = string "->" <|> string "→"
kwCstrArr = string "=>" <|> string "⇒"
kwTupTimes = char '*' <|> char '×'
kwLambda = char 'λ' <|> char '𝜆' <|> char '\\'
kwForall = string "all" <|> string "forall" <|> string "∀"
kwExists = string "ex" <|> string "exists" <|> string "∃"
kwShEmpty = char 'I' <|> char '𝕀'
kwShSingle = char 'X' <|> char '𝕏'
kwTLambda = char 'Λ' <|> char '\\'
kwProj1 = string "π₁" <|> string "proj1"
kwProj2 = string "π₂" <|> string "proj2"
kwLab1 = string "1" <|> string "left"
kwLab2 = string "2" <|> string "right"
kwCtxEmpty = string "*" <|> string "·"
kwChoice = char '+' <|> char '⊕'
kwBind = string "->" <|> string "↦" <|> string "→"


{- util -}

surround cl cr r = do
  char cl
  spaces
  r_ <- try r
  spaces
  char cr
  return r_

brackets = tl $ surround '[' ']'

parens = tl $ surround '(' ')'

braces = tl $ surround '{' '}'

angles = tl $ surround '<' '>'

space1 = tl $ do
  space
  spaces

identifier = tl $ do
  s <- many1 alphaNum
  if s `elem` kws then 
    fail $ "identifier " ++ s ++ " is a reserved keyword"
  else
    if any (`isInfixOf` s) syms then 
      fail $ "identifier " ++ s ++ " contains a reserved symbol"
    else
      return s


{- kinds -}

kType = tl $ do
  string "Type"
  return KType

kSession = tl $ do
  string "Session"
  return KSession

kState = tl $ do
  string "State"
  return KState

kShape = tl $ do
  string "Shape"
  return KShape

kDom = tl $ do
  string "Dom"
  spaces
  KDom <$> shape2

kind1 = foldr1 KArr <$> sepBy1 kind2 (spaces *> kwFunArr <* spaces)
kind2 = tl (kType <|> kSession <|> kState <|> kShape <|> kDom <|> parens kind1) <?> "kind"


{- labels -}

lLeft = tl $ do
  kwLab1
  return LLeft

lRight = tl $ do
  kwLab2
  return LRight

label = tl $lLeft <|> lRight

lProj1 = tl $ do
  kwProj1
  return LLeft

lProj2 = tl $ do
  kwProj2
  return LRight

lProj = tl $ lProj1 <|> lProj2


{- types -}

tVar = tl $ TVar <$> identifier

tApp = tl $ do
  f <- parens tLam <|> tVar
  space1
  TApp f <$> dom3

domBind = tl $ do
  id <- identifier
  spaces
  string ":"
  spaces
  d <- kDom
  return (id, d)

tLam = tl $ do
  kwLambda
  (id, d) <- parens domBind
  spaces
  string "."
  spaces
  c <- state1 <|> et1
  return (TLam id d c)

cstr = tl $ do
  t <- dom1
  spaces
  string "#"
  spaces
  t_ <- dom1
  return (t, t)
cstrs = tl $ do
  sepBy1 cstr (char ',')

kBind = tl $ do
  id <- identifier
  spaces
  string ":"
  spaces
  k <- kind1
  return (id, k)

et1 = tl $ eAll <|> et2
et2 = tl $ foldr1 EPair <$> sepBy1 et3 (spaces *> kwTupTimes <* spaces)
et3 = tl $ foldr1 TApp <$> sepBy1 et4 space1
et4 = tl $ eChan <|> eUnit <|> eAcc <|> parens et1

eAll = tl $ do
  kwForall
  (id, k) <- parens kBind
  spaces
  string "."
  cs <- option [] (do
      cs <- parens cstrs
      spaces
      kwCstrArr
      return cs) <?> "constraints"
  spaces
  EAll id k cs <$> et1

ctxBind = tl $ do
  id <- identifier
  spaces
  char ':'
  spaces
  k <- kDom
  return (id, HasKind k)
ctxBinds = tl $ sepBy1 ctxBind (char ',')
ctxEmpty = tl $ do
  kwCtxEmpty
  return []
ctx1 = tl $ ctxEmpty <|> ctxBinds 

stTy = tl $ do
  st <- braces state1
  spaces
  char ';'
  spaces
  t <- et1
  return (st, t)

ctxStTy = tl $ do
  ctx <- option [] (do
    kwExists
    spaces
    ctx <- ctx1
    char '.'
    spaces
    return ctx) <?> "context"
  (st, t) <- stTy
  return (ctx, st, t)

eArr = tl $ parens $ do
  (st1, t1) <- stTy
  spaces
  kwFunArr
  (ctx, st2, t2) <- ctxStTy
  return (EArr st1 t1 ctx st2 t2)

eChan = tl $ do
  string "Chan"
  space1
  EChan <$> dom3

eAcc = tl $ EAcc <$> brackets session1

eUnit = tl $ do
  spaces
  string "Unit"
  return EUnit

domStTy = tl $ do
  kwExists
  (id, d) <- domBind
  spaces
  char '.'
  spaces
  (st, t) <- stTy
  return (id, d, st, t)

session1 = tl $ foldr1 SBranch <$> sepBy1 session2 (spaces *> char '&' <* spaces)
session2 = tl $ foldr1 SChoice <$> sepBy1 session3 (spaces *> kwChoice <* spaces)
session3 = tl $ sSend <|> sRecv <|> session4
session4 = tl $ sDual <|> session5
session5 = tl $ sEnd <|> tVar <|> parens session1

sSend = tl $ do
  char '!'
  (id, d, st, t) <- parens domStTy
  spaces
  char '.'
  spaces
  SSend id d st t <$> session3

sRecv = tl $ do
  char '?'
  (id, d, st, t) <- parens domStTy
  spaces
  char '.'
  spaces
  SRecv id d st t <$> session3

sEnd = tl $ do
  string "End"
  return SEnd

sDual = tl $ do
  char '~'
  SDual <$> session4

shape1 = tl $ foldr1 SHMerge <$> sepBy1 shape2 (spaces *> char ';' <* spaces)
shape2 = tl $ shEmpty <|> shSingle <|> tVar <|> parens shape1 

shEmpty = tl $ do
  kwShEmpty
  return SHEmpty

shSingle = tl $ do
  kwShSingle
  return SHSingle

shMerge = tl $ do
  t <- shape2
  spaces
  SHMerge t <$> shape2

dom1 = tl $ foldr1 DMerge <$> sepBy1 dom2 (spaces *> char ',' <* spaces)
dom2 = tl $ dProj <|> dom3
dom3 = tl $ dEmpty <|> tVar <|> parens dom1 

dEmpty = tl $ do
  char '*'
  return DEmpty

dMerge = tl $ do
  t <- dom2
  spaces
  char ','
  spaces
  DMerge t <$> dom1

dProj = tl $ do
  l <- lProj
  spaces
  DProj l <$> dom3

state1 =  foldr SSMerge SSEmpty <$> sepBy state2 (spaces *> char ',' <* spaces) <* optional (char ',')

state2 = do
  d <- dom3
  spaces
  let pb = SSBind d <$ kwBind <* spaces <*> session1
  case d of 
    TVar s -> TApp d <$ space1 <*> dom3 <|> pb
    _ -> pb

{- expressions & values -}

let1 = tl $ do
  string "let"
  space1
  var <- identifier
  spaces
  char '='
  spaces
  exp <- expr1
  space1
  string "in"
  space1
  Let var exp <$> expr1

{- app = tl $ do
  v <- val2
  space1
  App v <$> val1 -}

proj = tl $ do
  l <- lProj
  space1
  Proj l <$> val1

aapp = tl $ do
  v <- val2
  spaces
  t <- brackets (tLam <|> dom1 <|> shape1 <|> session1 <?> "expected type not of kind State or Type")
  return (AApp v t)

fork = tl $ do
  string "fork"
  space1
  Fork <$> val1

acc = tl $ do
  string "accept"
  space1
  Acc <$> val1

req = tl $ do
  string "request"
  space1
  Req <$> val1

send = tl $ do
  string "send"
  space1
  v <- val1
  space1
  string "on"
  space1
  Send v <$> val1

recv = tl $ do
  string "receive"
  space1
  Recv <$> val1

sel = tl $ do
  string "select"
  space1
  v <- label
  space
  spaces
  string "on"
  space1
  Sel v <$> val1

case_ = tl $ do
  string "case"
  space1
  v <- val1
  space
  spaces
  string "of"
  space1
  (e, e_) <- braces (do
    e <- expr1
    spaces
    char ';'
    spaces
    e_ <- expr1
    return (e, e_))
  return (Case v e e_)

close = tl $ do
  string "close"
  space1
  Close <$> val1

new = tl $ do
  string "new"
  space1
  New <$> session1

val = tl $ Val <$> val1

vVar = tl $ VVar <$> identifier

vChan = tl $ do
  string "chan"
  space1
  VChan . TVar <$> identifier

stBindTy = tl $ do
  st <- braces state1
  spaces
  char ';'
  spaces
  id <- identifier
  spaces
  char ':'
  spaces
  t <- et1
  return (st, id, t)

vAbs = tl $ do
  kwLambda
  spaces
  (st, id, t) <- parens stBindTy
  spaces
  char '.'
  spaces
  VAbs st id t <$> expr1

vTAbs = tl $ do
  kwTLambda
  (id, k) <- parens kBind
  spaces
  char '.'
  spaces
  cs <- option [] (do
    cs <- parens cstrs
    spaces
    kwCstrArr
    return cs)
  spaces
  VTAbs id k cs <$> val1

vUnit = tl $ do
  string "unit"
  return VUnit

vPair = tl $ angles $ do
  v <- val1
  spaces
  char ','
  spaces
  VPair v <$> val1

expr1 = tl $ let1 <|> expr2 
expr2 = expr3 <|> (do 
  l <- sepBy1 val1 space1
  case l of 
    [] -> undefined 
    [v] -> return $ Val v
    [v1, v2] -> return $ App v1 v2
    _ -> unexpected "nested applications not allowed in A-normal form")
expr3 = tl (fork <|> acc <|> req <|> send <|> recv <|> sel <|> case_ <|> close <|> new <|> parens expr1) <?> "expr" 

val1 = tl $ vAbs <|> vTAbs <|> val2
val2 = tl (vChan <|> vUnit <|> vPair <|> parens val1 <|> vVar) <?> "val" 