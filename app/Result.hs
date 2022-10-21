{-# LANGUAGE FlexibleContexts #-}
module Result where
import Control.Monad.Except (ExceptT, MonadError (throwError))

type Result r = Either String r

type ResultT m r = ExceptT String m r

raise :: MonadError String m => String -> m r
raise = throwError 

ok :: MonadError String m => r -> m r
ok = return

todo :: MonadError String m => m r
todo = raise "unimplemented" 

unreachable ::  MonadError String m => m r
unreachable = raise "unreachable"