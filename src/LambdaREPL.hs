module LambdaREPL (runREPL) where

import System.Console.Readline

runREPL :: IO ()
runREPL = readline "lambda> " >>= putStrLn . show
