{-# LANGUAGE LambdaCase #-}
module Eval where
  
import Ast
    ( AccBind,
      ChanBind,
      Expr(..),
      ExprCtx(..),
      Label(LRight, LLeft),
      Program,
      Type(TVar, EAcc, SSend, SChoice, SEnd),
      Val(..) )
import Substitution ( subE, subTV )
import Data.Foldable ()
import Typing ( typeP )
import Result ( ok, Result, ResultT )
import Control.Applicative ( Alternative((<|>)) )
import Data.Maybe ()
import Data.Functor ( (<&>) )
import Data.Data ()
import Context (freshVar)
import Debug.Trace
import Pretty
import Control.Monad.Error.Class (liftEither)
import Control.Monad.IO.Class (liftIO)

evalV :: Val -> ResultT IO Program
evalV v = evalE (Val v)

evalE :: Expr -> ResultT IO Program
evalE e = evalP ([], [], [e])

splitExpr :: Expr -> (ExprCtx, Expr)
splitExpr e @ (Let x (Val v) b) = (ECHole, e)
splitExpr (Let x e b) = let (ce', e') = splitExpr e in
  (ECLet x ce' b, e')
splitExpr e = (ECHole, e)

mergeExpr :: ExprCtx -> Expr -> Expr
mergeExpr ECHole e = e
mergeExpr (ECLet x ec b) e = Let x (mergeExpr ec e) b

mapExprCtx :: (Expr ->  Expr) -> Expr -> Expr
mapExprCtx f e = let (ce', e') = splitExpr e in
  mergeExpr ce' (f e')

findEC :: [Expr] -> (Expr -> Bool) -> Maybe ([Expr], ExprCtx, Expr, [Expr])
findEC [] f = Nothing
findEC (e : es) f = let (ce', e') = splitExpr e in
  if f e' then Just ([], ce', e', es) 
  else fmap (\(es1, ce'', e'', es2) -> (es1 ++ [e], ce'', e'', es2)) (findEC es f)

findEC2 :: [Expr] -> (Expr -> Bool) -> (Expr -> Bool) -> Maybe ([Expr], ExprCtx, Expr, [Expr], ExprCtx, Expr, [Expr])
findEC2 es f1 f2 = case findEC es f1 of
     Just (es1, ce1, e1, es1') -> case (findEC es1 f2, findEC es1' f2) of
        (Just (es2, ce2, e2, es2'), Nothing) -> Just (es2, ce2, e2, es2', ce1, e1, es1')
        (Nothing, Just (es2, ce2, e2, es2')) -> Just (es1, ce1, e1, es2, ce2, e2, es2')
        _ -> Nothing
     Nothing -> Nothing

evalE' :: Expr -> Expr
evalE' (App (VAbs _ x _ e) v) = subE x v e
evalE' (AApp (VTAbs x _ _ v) t) = Val (subTV x t v)
evalE' (Let x (Val v) e) = subE x v e
evalE' (Let x e1 e2) = Let x (evalE' e1) e2
evalE' (Proj l (VPair v1 v2)) = case l of   
  LLeft -> Val v1
  LRight -> Val v2
evalE' e = e

fixEvalEs :: [Expr] -> [Expr]
fixEvalEs es = let es' = map (mapExprCtx evalE') es in
  if es == es' then es' else fixEvalEs es'

evalP :: Program -> ResultT IO Program
evalP p @ (abs, cbs, es) = 
  let es' = fixEvalEs es in
  let p = (abs, cbs, es') in
  case tryEvalC p of
    Nothing -> ok p
    Just p' -> do
      liftIO $ putStrLn $ pretty p'
      liftEither $ typeP p'
      evalP p'

tryEvalC :: Program -> Maybe Program
tryEvalC p @ (abs, cbs, _) = tryEvalFork p <|> 
                             tryEvalNew p <|> 
                             tryEvalReqAcc abs p <|> 
                             tryEvalSendRecv cbs p <|> 
                             tryEvalSelCase cbs p <|> 
                             tryEvalClose cbs p

tryEvalFork :: Program -> Maybe Program
tryEvalFork p @ (abs, cbs, es) = findEC es isFork <&> \(es1, ce, Fork v, es2) -> 
  (abs, cbs, es1 ++ [App v VUnit, mergeExpr ce (Val VUnit)] ++ es2)

tryEvalNew :: Program -> Maybe Program
tryEvalNew p @ (abs, cbs, es) = findEC es isNew <&> \(es1, ce, New t, es2) -> 
    let v = freshVar "ap" in
    (abs ++ [(v, EAcc t)], cbs, es1 ++ [mergeExpr ce (Val (VVar v))] ++ es2)

tryEvalReqAcc :: [AccBind] -> Program -> Maybe Program
tryEvalReqAcc (a @ (x, EAcc s) : xs) p @ (abs, cbs, es) = case findEC2 es (isReq x) (isAcc x) of  
  Just (les, lce, l, mes, rce, r, res) -> let v = freshVar "c" in let v' = freshVar "~c" in 
    (case (l, r) of  
      (Req {}, Acc {}) -> Just (VChan (TVar v), VChan (TVar v'))
      (Acc {}, Req {}) -> Just (VChan (TVar v'), VChan (TVar v))
      _ -> Nothing
    ) <&> (\(l, r) -> (abs, cbs ++ [((v, v'), s)], les ++ [mergeExpr lce (Val l)] ++ mes ++ [mergeExpr rce (Val r)] ++ res))
  _ -> tryEvalReqAcc xs p
tryEvalReqAcc _ _ = Nothing

tryEvalSendRecv :: [ChanBind] -> Program -> Maybe Program
tryEvalSendRecv (cb @ ((x, x'), SSend sa k st t c) : xs) p @ (abs, cbs, es) = case findEC2 es (isSend x) (isRecv x') of  
  Just (les, lce, l, mes, rce, r, res) ->
    (case (l, r) of  
      (Send sv _, Recv {}) -> Just (VUnit, sv)
      (Recv {}, Send sv _) -> Just (sv, VUnit)
      _ -> Nothing
    ) <&> (\(l, r) -> (abs, replace cbs cb ((x, x'), c) , les ++ [mergeExpr lce (Val l)] ++ mes ++ [mergeExpr rce (Val r)] ++ res))
  _ -> tryEvalSendRecv xs p
tryEvalSendRecv _ _ = Nothing

tryEvalSelCase :: [ChanBind] -> Program -> Maybe Program
tryEvalSelCase (cb @ ((x, x'), SChoice sl sr) : xs) p @ (abs, cbs, es) = case findEC2 es (isSel x) (isCase x') of  
  Just (les, lce, l, mes, rce, r, res) ->
    (case (l, r) of  
      (Sel l _, Case _ e1 e2) -> 
        Just (Val VUnit, case l of {LLeft -> e1; LRight -> e2}, case l of {LLeft -> sl; LRight -> sr})
      (Case _ e1 e2, Sel l _) -> 
        Just (case l of {LLeft -> e1; LRight -> e2}, Val VUnit, case l of {LLeft -> sl; LRight -> sr})
      _ -> Nothing
    ) <&> (\(l, r, t) -> (abs, replace cbs cb ((x, x'), t) , les ++ [mergeExpr lce l] ++ mes ++ [mergeExpr rce r] ++ res))
  _ -> tryEvalSelCase xs p
tryEvalSelCase _ _ = Nothing

tryEvalClose :: [ChanBind] -> Program -> Maybe Program
tryEvalClose (cb @ ((x, x'), SEnd) : xs) p @ (abs, cbs, es) = case findEC2 es (isClose x) (isClose x') of  
  Just (les, lce, l, mes, rce, r, res) ->
    (case (l, r) of  
      (Close {}, Close {}) -> Just (VUnit, VUnit)
      _ -> Nothing
    ) <&> (\(l, r) -> (abs, remove cbs cb, les ++ [mergeExpr lce (Val l)] ++ mes ++ [mergeExpr rce (Val r)] ++ res))
  _ -> tryEvalClose xs p
tryEvalClose _ _ = Nothing

split :: Eq a => a -> [a] -> ([a], [a])
split x = fmap (drop 1) . break (x ==)

remove :: Eq a => [a] -> a -> [a]
remove as a = let (l, r) = split a as in l ++ r

replace ::  Eq a => [a] -> a -> a -> [a]
replace as a b = let (l, r) = split a as in l ++ [b] ++ r

isNew :: Expr -> Bool
isNew New {} = True
isNew _ = False

isFork :: Expr -> Bool
isFork Fork {} = True
isFork _ = False

isReq :: String -> Expr -> Bool
isReq s (Req (VVar s')) = s == s'
isReq _ _ = False

isAcc :: String -> Expr -> Bool
isAcc s (Acc (VVar s'))  = s == s'
isAcc _ _ = False

isSend :: String -> Expr -> Bool
isSend s (Send _ (VChan (TVar s'))) = s == s'
isSend _ _ = False

isRecv :: String -> Expr -> Bool
isRecv s (Recv (VChan (TVar s'))) = s == s'
isRecv _ _ = False

isSel :: String -> Expr -> Bool
isSel s (Sel _ (VChan (TVar s'))) = s == s'
isSel _ _ = False

isCase :: String -> Expr -> Bool
isCase s (Case (VChan (TVar s')) _ _) = s == s'
isCase _ _ = False

isClose :: String -> Expr -> Bool
isClose s (Close (VChan (TVar s'))) = s == s'
isClose _ _ = False