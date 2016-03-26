module Data.Lambda.REPL ( runREPL
                        , doREPL
                        ) where

import Data.Maybe
import Data.Lambda
import Data.Lambda.Parser
import System.Console.Readline
import Data.List (isPrefixOf, stripPrefix)
import Control.Monad.State

runREPL :: IO ()
runREPL = evalStateT runREPL' baseProgram

runREPL' :: StateT Program IO ()
runREPL' = lift (readline "lambda> ") >>= loop
    where
        loop (Just s) = do
            lift $ addHistory s
            maybeOutput <- doREPL s
            case maybeOutput of
              Just output -> lift $ putStrLn output
              Nothing -> return ()
            runREPL'
        loop Nothing = return ()

doREPL :: Monad m => String -> StateT Program m (Maybe String)
doREPL "" = return Nothing
doREPL s
    | ":d " `isPrefixOf` s = do
        program <- get
        let name = (fromJust $ stripPrefix ":d " s)
        case resolve' program name  of
          Just expr -> return . Just $ show expr
          Nothing -> return . Just $ name ++ " is not defined"
    | ":p" `isPrefixOf` s = get >>= return . Just . show
    | otherwise = case parseLambda s of
                    Left e -> return (Just e)
                    Right ast -> do
                        let newExpr = simplify . fromAST $ ast
                        modify $ \program -> program `append` newExpr
                        return . Just . show $ newExpr
