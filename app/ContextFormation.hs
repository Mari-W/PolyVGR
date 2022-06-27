module ContextFormation where

import Ast (Ctx, Has (HasKind, HasType, HasDisCon))
import Result (Result, ok, raise)

contextWellFormed :: Ctx -> Result ()
contextWellFormed [] = ok ()
contextWellFormed (x:xs) = do
    case x of
         HasKind k -> ok ()
         HasType t -> ok ()
         HasDisCon d1 d2 -> ok ()
    contextWellFormed xs