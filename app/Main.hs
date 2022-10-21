module Main where

import Ast ( Type(SSEmpty) )
import Typing ( typeE' )
import Pretty ( Pretty(pretty) )
import Eval ( evalE )
import Parser (parseFile)
import System.Environment ( getArgs )
import Context (freshVar)
import Result (ResultT, raise)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Error.Class (liftEither)
import Control.Monad.Except (runExceptT)

run :: ResultT IO ()
run = do
  args <- liftIO getArgs
  arg1 <- case args of
    [a] -> return a
    _ -> raise "expected path to file as the only argument"
  p <- parseFile arg1
  t <- liftEither $ typeE' [] SSEmpty p
  (_, _, e) <- evalE p
  liftIO $ putStrLn (pretty e) 

main :: IO ()
main = do
  res <- runExceptT run
  case res of    
    Left s -> putStrLn s
    Right x0 -> return ()