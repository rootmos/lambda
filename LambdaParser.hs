module LambdaParser where

import Text.Parsec
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (haskellDef)
import Test.Hspec hiding (context)
import Data.Bifunctor
import Data.Either
import Debug.Trace

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
symbol = P.symbol lexer
dot = P.dot lexer

spec_parseLambda :: SpecWith ()
spec_parseLambda = describe "parseLambda" $ do
    it "should parse: x" $ do
        parseLambda "x" `shouldBe` (Right (V "x"))
    it "should parse: foo" $ do
        parseLambda "foo" `shouldBe` (Right (V "foo"))
    it "should complain on empty string" $ do
        parseLambda "" `shouldSatisfy` isLeft
    it "should parse: (x y)" $ do
        parseLambda "(x y)" `shouldBe` (Right (A (V "x") (V "y")))
    it "should parse: (\\x.y)" $ do
        parseLambda "(\\x.y)" `shouldBe` (Right (L "x" (V "y")))
    it "should parse: (λ foo . bar)" $ do
        parseLambda "(λ foo . bar)" `shouldBe` (Right (L "foo" (V "bar")))
    it "should parse: (λx.(y z))" $ do
        parseLambda "(λx.(y z))" `shouldBe` (Right (L "x" (A (V "y") (V "z"))))
    it "should parse: ((λx.y) z)" $ do
        parseLambda "((λx.y) z)" `shouldBe` (Right (A (L "x" (V "y")) (V "z")))

main :: IO ()
main = hspec $ do
    spec_parseLambda
