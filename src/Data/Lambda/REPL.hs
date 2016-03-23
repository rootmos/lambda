module Data.Lambda.REPL (runREPL) where

import Data.Maybe
import Data.Lambda
import Data.Lambda.Parser
import System.Console.Readline
import Data.List (isPrefixOf, stripPrefix)

runREPL :: IO ()
runREPL = runREPL' empty >> return ()

runREPL' :: Program -> IO Program
runREPL' program = readline "lambda> " >>= loop
    where
        loop (Just s) = addHistory s >> doREPL program s >>= runREPL'
        loop Nothing = return program

doREPL :: Program -> String -> IO Program
doREPL program s
    | ":d " `isPrefixOf` s = do
        putStrLn . show $ resolve' program (fromJust $ stripPrefix ":d " s)
        return program
    | otherwise = case parseLambda s of
                    Left e -> putStrLn e >> return program
                    Right ast -> do
                        let newExpr = simplify . fromAST $ ast
                        putStrLn . show $ newExpr
                        return $ exprProgram newExpr
