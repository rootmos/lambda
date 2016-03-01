module Lamda where

import Test.Hspec
import Data.List
import Data.Graph.Inductive
import Data.Graph.Inductive.PatriciaTree
import Control.Monad.State

type Name = String

data AST = V Name | L Name AST | A AST AST
    deriving Show

free :: AST -> [Name]
free (V v) = [v]
free (L v expr) = delete v $ free expr
free (A m n) = sort . nub $ free m ++ free n

alphaEquivalent :: AST -> AST -> Bool
alphaEquivalent (V _) (V _) = True
alphaEquivalent (L x e) (L y f) = (x `elem` free e) == (y `elem` free f) && e `alphaEquivalent` f
alphaEquivalent _ _ = False


data NodeLabel = Let Name | Variable Name | Lambda Name | App
    deriving (Show, Eq)
data EdgeLabel = Binding | Body | Function | Argument
    deriving (Show, Eq)

type Expr = Gr NodeLabel EdgeLabel
type ExprNode = LNode NodeLabel
type ExprEdge = LEdge EdgeLabel

variable :: Name -> State Expr ExprNode
variable n = do
    node <- get >>= return . head . newNodes 1
    let lnode = (node, Variable n)
    modify $ insNode lnode
    return lnode 

lambda :: Name -> ExprNode -> State Expr ExprNode
lambda x body = do
    node <- get >>= return . head . newNodes 1
    let lambdaNode = (node, Lambda x)
    let bodyEdge = (fst lambdaNode, fst body, Body)
    modify $ insNode lambdaNode
    modify $ insEdge bodyEdge
    return lambdaNode

foo = execState (variable "x" >>= lambda "y") empty

main :: IO ()
main = hspec $ do
    describe "free" $ do
        it "returns [x] for x" $ do
            free (V "x") `shouldBe` ["x"]
        it "returns [] for L x x" $ do
            free (L "x" (V "x")) `shouldBe` []
        it "returns [y] for L x y" $ do
            free (L "x" (V "y")) `shouldBe` ["y"]
        it "returns [x,y] for A x y" $ do
            free (A (V "x") (V "y")) `shouldBe` ["x", "y"]
        it "returns [y] for L x (A x y)" $ do
            free (L "x" (A (V "x") (V "y"))) `shouldBe` ["y"]
        it "returns [x] for L y (A x y)" $ do
            free (L "y" (A (V "x") (V "y"))) `shouldBe` ["x"]
        it "returns [y,z] for A (L x z) y" $ do
            free (A (L "x" (V "z")) (V "y")) `shouldBe` ["y","z"]
        it "returns [y,z] for A y (L x z)" $ do
            free (A (V "y") (L "x" (V "z"))) `shouldBe` ["y","z"]
        it "returns [x] for A x x" $ do
            free (A (V "x") (V "x")) `shouldBe` ["x"]
    describe "alphaEquivalent" $ do
        it "claims that x is alpha-equivalent to y" $ do
            (V "x") `alphaEquivalent` (V "y") `shouldBe` True
        it "claims that λx.x is alpha-equivalent to λy.y" $ do
            (L "x" (V "x")) `alphaEquivalent` (L "y" (V "y")) `shouldBe` True
        it "claims that λx.λx.x is not alpha-equivalent to λy.λx.y" $ do
            (L "x" (L "x" (V "x"))) `alphaEquivalent` (L "y" (L "x" (V "y"))) `shouldBe` False
        it "claims that λx.λx.x is alpha-equivalent to λy.λx.x" $ do
            (L "x" (L "x" (V "x"))) `alphaEquivalent` (L "y" (L "x" (V "x"))) `shouldBe` True
        it "claims that λx.x y is not alpha equivalent to λx.x" $ do
            (L "x" (A (V "x") (V "y"))) `alphaEquivalent` (L "x" (V "x")) `shouldBe` False
