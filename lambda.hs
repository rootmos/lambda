module Lamda where

import Test.Hspec
import Data.List

type VariableName = String

data Expr = Variable VariableName | Lambda VariableName Expr | App Expr Expr
    deriving Show

data Error = VariableNotFree VariableName Expr

subst :: VariableName -> Expr -> Either Error Expr
subst x expr = Right expr

free :: Expr -> [VariableName]
free (Variable v) = [v]
free (Lambda v expr) = delete v $ free expr
free (App m n) = sort . nub $ free m ++ free n

main :: IO ()
main = hspec $ do
    describe "free" $ do
        it "returns [x] for x" $ do
            free (Variable "x") `shouldBe` ["x"]
        it "returns [] for Lambda x x" $ do
            free (Lambda "x" (Variable "x")) `shouldBe` []
        it "returns [y] for Lambda x y" $ do
            free (Lambda "x" (Variable "y")) `shouldBe` ["y"]
        it "returns [x,y] for App x y" $ do
            free (App (Variable "x") (Variable "y")) `shouldBe` ["x", "y"]
        it "returns [y] for Lambda x (App x y)" $ do
            free (Lambda "x" (App (Variable "x") (Variable "y"))) `shouldBe` ["y"]
        it "returns [x] for Lambda y (App x y)" $ do
            free (Lambda "y" (App (Variable "x") (Variable "y"))) `shouldBe` ["x"]
        it "returns [y,z] for App (Lambda x z) y" $ do
            free (App (Lambda "x" (Variable "z")) (Variable "y")) `shouldBe` ["y","z"]
        it "returns [y,z] for App y (Lambda x z)" $ do
            free (App (Variable "y") (Lambda "x" (Variable "z"))) `shouldBe` ["y","z"]
        it "returns [x] for App x x" $ do
            free (App (Variable "x") (Variable "x")) `shouldBe` ["x"]
