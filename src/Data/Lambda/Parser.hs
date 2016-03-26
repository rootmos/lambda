{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
module Data.Lambda.Parser (AST(..), Name, parseLambda) where

import Text.Parsec
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (haskellDef)
import Data.Bifunctor

type Name = String

data AST = V Name | L Name AST | A AST AST | D Name AST
    deriving (Show, Eq)


parseLambda :: String -> Either String AST
parseLambda = first show . parse topLevelLambdaParser "parsing lambda"

topLevelLambdaParser :: Parsec String st AST
topLevelLambdaParser = (try defParser <|> lambdaParser) <* eof

defParser :: Parsec String st AST
defParser = D <$> variableName <* symbol ":=" <*> lambdaParser

lambdaParser :: Parsec String st AST
lambdaParser = try lambda <|> try app <|> variable 

variable :: Parsec String st AST
variable = V <$> variableName

variableName :: Parsec String st Name
variableName = many1 alphaNum <* spaces

app :: Parsec String st AST
app = parens $ chainl1 lambdaParser (spaces >> return A)

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
symbol = P.symbol lexer

