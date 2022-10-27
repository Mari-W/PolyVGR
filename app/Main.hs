{-# LANGUAGE FlexibleContexts #-}
module Main where

import Ast ( Type(SSEmpty) )
import Typing ( typeE' )
import Pretty ( Pretty(pretty) )
import Eval ( evalE )
import Parser (parseFile)
import System.Environment ( getArgs )
import Context (freshVar)
import Result (ResultT, raise)
import Control.Monad.IO.Class (liftIO, MonadIO)
import Control.Monad.Error.Class (liftEither)
import Control.Monad.State (MonadState, StateT (runStateT))
import Control.Monad.Except (MonadError, runExceptT)

run :: (MonadState Int m, MonadIO m, MonadError String m) => m ()
run = do
  args <- liftIO getArgs
  arg1 <- case args of
    [a] -> return a
    _ -> raise "expected path to file as the only argument"
  p <- parseFile arg1
  t <- typeE' [] SSEmpty p
  liftIO $ putStrLn ("-----------::          expr           ::-----------\n\n" ++ pretty p ++
                     "\n\n-----------::        has type         ::-----------\n\n" ++ pretty t ++
                     "\n\n-----------::      communication      ::-----------\n")
  (_, _, e) <- evalE p
  liftIO $ putStrLn "-----------::          done           ::-----------" 

main :: IO ()
main = do
  res <- runExceptT (runStateT run 0)
  case res of    
    Left s -> putStrLn s
    Right _ -> return ()