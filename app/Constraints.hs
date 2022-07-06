module Constraints where

import Ast (Dom (DEmpty, DTree))
import Context (Ctx, Const, Has (HasConst))
import Result (Result)

{- constrWellFormed :: Ctx -> Const -> Result ()
 -}

filterConsts :: Ctx -> [Const]
filterConsts [] = []
filterConsts (x : xs) = case x of
  HasConst c -> c : filterConsts xs
  _ -> filterConsts xs

splitConsts :: [Const] -> [Const]
splitConsts [] = []




