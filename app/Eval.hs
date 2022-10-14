{-# LANGUAGE LambdaCase #-}
module Eval where
import Ast
import Substitution
import Data.Foldable
import Typing
import Result
import Context

evalV :: Val -> Result Program
evalV v = evalE (Val v)

evalE :: Expr -> Result Program
evalE e = evalP ([], [], [e])

fixEvalEs :: [Expr] -> [Expr]
fixEvalEs es = let es' = map evalE' es in
  if es == es'  then es' else fixEvalEs es'

evalE' :: Expr -> Expr
evalE' (App (VAbs _ x _ e) v) = subE x v e
evalE' (AApp (VTAbs x _ _ v) t) = Val (subTV x t v)
evalE'  (Let x (Val v) e) = subE x v e
evalE'  (Let x e1 e2) = Let x (evalE' e1) e2
evalE'  (Proj l (VPair v1 v2)) = case l of   
  LLeft -> Val v1
  LRight -> Val v2
evalE'  e = e

fixEvalP :: Program -> Result Program
fixEvalP p = do
  p' <- evalP p
  if p == p' then ok p else fixEvalP p'

evalP :: Program -> Result Program
evalP tri @ (abs, cbs, es) = do
  let es' = fixEvalEs es
  p' <- findFork tri
  typeP p'
  ok p'

replaceFirst :: Eq a => a -> a -> [a] -> [a]
replaceFirst a b [] = []
replaceFirst a b (x : xs) = if x == a then b : xs else x : replaceFirst a b xs

removeFirst :: Eq a => a -> [a] -> [a]
removeFirst a [] = []
removeFirst a (x : xs) = if x == a then xs else x : removeFirst a xs


findFork :: Program -> Result Program
findFork p @ (abs, cbs, es) = case [x | x@Fork {} <- es] of
  f @ (Fork v) : _ -> evalP (abs, cbs, App v VUnit : replaceFirst f (Val VUnit) es)
  _ -> findNew p

findNew :: Program -> Result Program
findNew p @ (abs, cbs, es) = case [x | x@New {} <- es] of
  f @ (New t) : _ -> do
    let v = freshVar 
    evalP (abs ++ [(v, t)], cbs, replaceFirst f (Val (VVar v)) es)
  _ -> findReqAcc abs p

findReqAcc :: [AccBind] -> Program -> Result Program
findReqAcc (f @ (v, EAcc s) : xs) p @ (abs, cbs, es) = 
  case ([x | x@(Req (VVar y)) <- es, v == y], [x | x@(Acc (VVar y)) <- es, v == y]) of
    (r @ (Req _) : _, a @ (Acc _) : _) -> do
      let v = freshVar 
      let v' = freshVar 
      evalP (removeFirst f abs, 
             cbs ++ [((v, v'), s)], 
             replaceFirst r (Val (VChan (TVar v))) (replaceFirst a (Val (VChan (TVar v'))) es)
       )
    _ -> findReqAcc xs p
findReqAcc [] p @ (abs, cbs, es) = findSendRecv cbs p
findReqAcc _ _ = unreachable 

findSendRecv :: [ChanBind] -> Program -> Result Program
findSendRecv (f @ ((v, v'), SSend sa k st t c) : xs) p @ (abs, cbs, es) = 
  case (v == sa, [x | x@(Send _ (VChan (TVar y))) <- es, v == y], [x | x@(Recv (VChan (TVar y))) <- es, v' == y]) of
    (True, s @ (Send sent _) : _, r @ Recv {} : _) -> do
      evalP (abs, 
             replaceFirst f ((v, v'), c) cbs, 
             replaceFirst s (Val VUnit) (replaceFirst r (Val sent) es)
       )
    _ -> findSendRecv xs p
findSendRecv [] p @ (abs, cbs, es) = findSelCase cbs p
findSendRecv (x : xs) p = findSendRecv xs p

findSelCase :: [ChanBind] -> Program -> Result Program 
findSelCase (f @ ((v, v'), SChoice sl sr) : xs) p @ (abs, cbs, es) = 
  case ([x | x@(Sel _ (VChan (TVar y))) <- es, v == y], [x | x@(Case (VChan (TVar y)) _ _) <- es, v' == y]) of
    (s @ (Sel l _) : _, c @ (Case _ e1 e2) : _) -> do
      evalP (abs, 
             replaceFirst f ((v, v'), case l of {LLeft -> sl; LRight -> sr}) cbs, 
             replaceFirst s (Val VUnit) (replaceFirst c (case l of {LLeft -> e1; LRight -> e2}) es)
       )
    _ -> findSelCase xs p
findSelCase [] p @ (abs, cbs, es) = findClose cbs p
findSelCase (x : xs) p = findSelCase xs p

findClose :: [ChanBind] -> Program -> Result Program 
findClose (f @ ((v, v'), SEnd) : xs) p @ (abs, cbs, es) = 
  case ([x | x@(Close (VChan (TVar y))) <- es, v == y], [x | x@(Close (VChan (TVar y))) <- es, v' == y]) of
    (c1 @ Close {} : _, c2 @ Close {} : _) -> do
      evalP (abs, 
             cbs,
             replaceFirst c1 (Val VUnit) (replaceFirst c2 (Val VUnit) es)
       )
    _ -> findSelCase xs p
findClose [] p @ (abs, cbs, es) = ok p
findClose (x : xs) p = findClose xs p