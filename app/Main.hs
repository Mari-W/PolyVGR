module Main where

import Ast
import Kinding
import Typing
import Pretty 
import Eval
import Parser (parseFile)
import Text.Parsec
import System.Environment
import Context (freshVar)

main :: IO ()
main = do
  args <- getArgs
  case args of 
    [s] -> do
      p <- parseFile s
      case p of
        Left str -> putStrLn ("Parse Error\n" ++  str)
        Right ex -> do
          putStrLn ("Parsed: " ++ pretty ex)
          case typeE' [] SSEmpty ex of
            Left str -> putStrLn ("Type Error\n" ++  str)
            Right (_, _, t) -> do
              putStrLn ("Type: " ++ pretty t)
              case evalE ex of
                Left str ->  putStrLn ("Eval Error\n" ++  str)
                Right (_, _, ts) ->  putStrLn ("Remaining Threads: " ++ pretty ts)
    _ -> error "expected path to file as the only argument"
