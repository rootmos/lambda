module LambdaParserSpec (spec) where

import LambdaParser
import Test.Hspec
import Data.Either

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

spec :: SpecWith ()
spec = do
    spec_parseLambda
