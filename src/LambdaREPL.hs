module LambdaREPL (runREPL) where

import Lambda
import LambdaParser
import System.Console.Readline

runREPL :: IO ()
runREPL = readline "lambda> " >>= loop
    where
        loop (Just s) = addHistory s >> doREPL s >> runREPL
        loop Nothing = return ()

doREPL :: String -> IO ()
doREPL s = case parseLambda s of
      Left e -> putStrLn e
      Right ast -> putStrLn . show $ simplify . fromAST $ ast
