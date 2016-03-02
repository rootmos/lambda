module Lamda where

import Test.Hspec hiding (context)
import Data.Graph.Inductive
import Control.Monad.State

type Name = String

data AST = V Name | L Name AST | A AST AST
    deriving Show


data NodeLabel = Variable Name | Lambda Name | App
    deriving (Show, Eq)
data EdgeLabel = Binding | Body | Function | Argument
    deriving (Show, Eq)

type Expr = Gr NodeLabel EdgeLabel
type ExprNode = LNode NodeLabel
type ExprEdge = LEdge EdgeLabel

variable :: Monad m => Name -> StateT Expr m ExprNode
variable n = do
    node <- newNode
    let lnode = (node, Variable n)
    modify $ insNode lnode
    return lnode

lambda :: Monad m => Name -> ExprNode -> StateT Expr m ExprNode
lambda x body = do
    node <- newNode
    let lambdaNode = (node, Lambda x)
    let bodyEdge = (node, fst body, Body)
    modify $ insNode lambdaNode
    modify $ insEdge bodyEdge

    expr <- get
    let toBeBound = filter (\n -> isFree expr n && variableName expr n == x) $ bfs (fst body) expr
    mapM_ (\n -> modify $ insEdge (n, node, Binding)) toBeBound

    return lambdaNode

app :: Monad m => ExprNode -> ExprNode -> StateT Expr m ExprNode
app fun arg = do
    node <- newNode
    let appNode = (node, App)
    modify $ insNode appNode
    modify $ insEdge (fst appNode, fst fun, Function)
    modify $ insEdge (fst appNode, fst arg, Argument)
    return appNode

newNode :: Monad m => StateT Expr m Node
newNode = get >>= return . head . newNodes 1

buildExpr :: Monad m => StateT Expr m a -> m (a, Expr)
buildExpr = flip runStateT empty

free :: Expr -> [ExprNode]
free expr = labNodes $ labnfilter labledIsFreeVariable expr
    where
        labledIsFreeVariable ln @ (n, _)
            | labledIsVariable ln = Binding `notElem` map edgeLabel (out expr n)
            | otherwise = False
        labledIsVariable (_, Variable _) = True
        labledIsVariable _ = False

variableName :: Expr -> Node -> Name
variableName expr n = let (Variable name) = lab' $ context expr n in name

isVariable :: Expr -> Node -> Bool
isVariable expr n = case lab' $ context expr n of
                      Variable _ -> True
                      _ -> False

isFree :: Expr -> Node -> Bool
isFree expr n = isVariable expr n && case map edgeLabel . out' $ context expr n of
                                       [Binding] -> False
                                       [] -> True
                                       _ -> error "Invariant violated!"

main :: IO ()
main = hspec $ do
    describe "variable" $ do
        it "should create a lone node" $ do
            ((n, Variable "x"), expr)  <- buildExpr $ variable "x"
            out expr n `shouldBe` []
            inn expr n `shouldBe` []

    describe "lambda" $ do
        it "should bind x in: λx.x " $ do
            ([(ln, Lambda _), (xn, Variable _)], expr) <- buildExpr $ do
                x <- variable "x"
                l <- lambda "x" x
                return [l, x]
            out expr ln `shouldBe` [(ln, xn, Body)]
            inn expr ln `shouldBe` [(xn, ln, Binding)]
            out expr xn `shouldBe` [(xn, ln, Binding)]
        it "should not bind x in: λy.x " $ do
            ([(ln,_), (xn, _)], expr) <- buildExpr $ do
                x <- variable "x"
                l <- lambda "y" x
                return [l, x]
            out expr ln `shouldBe` [(ln, xn, Body)]
            inn expr ln `shouldBe` []
            out expr xn `shouldBe` []
        it "should bind both x in: λx.x x" $ do
            ([(ln,_), (xn1, _), (xn2, _)], expr) <- buildExpr $ do
                x1 <- variable "x"
                x2 <- variable "x"
                l <- lambda "x" =<< app x1 x2
                return [l, x1, x2]
            inn expr ln `shouldBe` [(xn1, ln, Binding), (xn2, ln, Binding)]
            out expr xn1 `shouldBe` [(xn1, ln, Binding)]
            out expr xn2 `shouldBe` [(xn2, ln, Binding)]
        it "should bind x in: λx.x x" $ do
            ([(ln,_), (xn1, _), (xn2, _)], expr) <- buildExpr $ do
                x1 <- variable "x"
                x2 <- variable "x"
                l <- lambda "x" =<< app x1 x2
                return [l, x1, x2]
            inn expr ln `shouldBe` [(xn1, ln, Binding), (xn2, ln, Binding)]
            out expr xn1 `shouldBe` [(xn1, ln, Binding)]
            out expr xn2 `shouldBe` [(xn2, ln, Binding)]

    describe "app" $ do
        it "should connect the function and argument in: x y" $ do
            ([(a, App), (x, Variable _), (y, Variable _)], expr) <- buildExpr $ do
                x <- variable "x"
                y <- variable "y"
                a <- app x y
                return [a, x, y]
            out expr a `shouldBe` [(a, x, Function), (a, y, Argument)]
            inn expr a `shouldBe` []

    describe "free" $ do
        it "claims x is free in: x" $ do
            (x, expr) <- buildExpr $ variable "x"
            free expr `shouldBe` [x]
        it "claims nothing is free in: λx.x" $ do
            (_, expr) <- buildExpr $ lambda "x" =<< variable "x"
            free expr `shouldBe` []
        it "claims [y] is free in: λx.y" $ do
            (y, expr) <- buildExpr $ do
               y <- variable "y"
               _ <- lambda "x" y
               return y
            free expr `shouldBe` [y]
        it "claims [x, y] is free in: x y" $ do
            ([x,y], expr) <- buildExpr $ do
               x <- variable "x"
               y <- variable "y"
               _ <- app x y
               return [x, y]
            free expr `shouldBe` [x, y]
        it "claims [y] is free in: λx.x y" $ do
            (y, expr) <- buildExpr $ do
               x <- variable "x"
               y <- variable "y"
               _ <- lambda "x" =<< app x y
               return y
            free expr `shouldBe` [y]
        it "claims [x] is free in: λy.x y" $ do
            (x, expr) <- buildExpr $ do
               x <- variable "x"
               y <- variable "y"
               _ <- lambda "y" =<< app x y
               return x
            free expr `shouldBe` [x]
        it "claims nothing is free in: λx.λy.x y" $ do
            (_, expr) <- buildExpr $ do
               x <- variable "x"
               y <- variable "y"
               lambda "x" =<< lambda "y" =<< app x y
            free expr `shouldBe` []
        it "claims nothing is free in: λx.λy.λz.x y" $ do
            (_, expr) <- buildExpr $ do
               x <- variable "x"
               y <- variable "y"
               lambda "x" =<< lambda "y" =<< lambda "z" =<< app x y
            free expr `shouldBe` []
        it "claims [y,z] is free in: (λx.z) y" $ do
            ([y,z], expr) <- buildExpr $ do
               y <- variable "y"
               z <- variable "z"
               f <- lambda "x" z
               _ <- app f y
               return [y, z]
            free expr `shouldBe` [y, z]
        it "claims [y,z] is free in: y (λx.z)" $ do
            ([y,z], expr) <- buildExpr $ do
               y <- variable "y"
               z <- variable "z"
               f <- lambda "x" z
               _ <- app y f
               return [y, z]
            free expr `shouldBe` [y, z]
        it "claims [x] is free in: x x y" $ do
            (x, expr) <- buildExpr $ do
               x <- variable "x"
               _ <- app x x
               return x
            free expr `shouldBe` [x]

