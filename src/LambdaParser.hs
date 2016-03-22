{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
module LambdaParser (AST(..), Name, parseLambda) where

import Text.Parsec
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (haskellDef)
import Data.Bifunctor

type Name = String

data AST = V Name | L Name AST | A AST AST
    deriving (Show, Eq)


parseLambda :: String -> Either String AST
parseLambda = first show . parse lambdaParser "parsing lambda"

lambdaParser :: Parsec String st AST
lambdaParser = try lambda <|> try app <|> variable

variable :: Parsec String st AST
variable = V <$> variableName

variableName :: Parsec String st Name
variableName = many1 alphaNum <* spaces

app :: Parsec String st AST
app = parens funAndArg
    where
        funAndArg = do
            fun <- lambdaParser
            _ <- spaces
            arg <- lambdaParser
            return $ A fun arg

lambda :: Parsec String st AST
lambda = parens $ lambdaSymbol >> do
    name <- variableName
    _ <- dot
    body <- lambdaParser
    return $ L name body
        where
            lambdaSymbol = (oneOf ['\\', 'λ']) >> spaces

lexer = P.makeTokenParser haskellDef 
parens = P.parens lexer
dot = P.dot lexer

