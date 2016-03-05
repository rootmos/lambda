module Lamda where

import Test.Hspec hiding (context)
import Test.QuickCheck
import Data.Graph.Inductive
import Control.Monad.State
import Debug.Trace

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

type ExprT m a = StateT Expr m a

data Pair = Pair { node :: ExprNode, expr :: Expr }
    deriving (Show)


instance Arbitrary Pair where
    arbitrary = genExpr >>= buildExprT'
        where
            genExpr :: Gen (ExprT Gen ExprNode)
            genExpr = oneof [genVariable, genLambda, genApp]
            genVariable :: Gen (ExprT Gen ExprNode)
            genVariable = return $ variable =<< lift genVariableName
            genLambda :: Gen (ExprT Gen ExprNode)
            genLambda = do
                name <- genVariableName
                body <- genExpr
                return $ body >>= lambda name
            genApp :: Gen (ExprT Gen ExprNode)
            genApp = do
                fM <- genExpr
                aM <- genExpr
                return $ do
                   f <- fM
                   a <- aM
                   app f a
            genVariableName :: Gen Name
            genVariableName = elements ["a","b","c","u","v","w","x","y","z"]

variable :: Monad m => Name -> ExprT m ExprNode
variable n = do
    node <- newNode
    let lnode = (node, Variable n)
    modify $ insNode lnode
    return lnode

lambda :: Monad m => Name -> ExprNode -> ExprT m ExprNode
lambda x (b, _) = do
    node <- newNode
    let lambdaNode = (node, Lambda x)
    let bodyEdge = (node, b, Body)
    modify $ insNode lambdaNode
    modify $ insEdge bodyEdge

    expr <- get
    let toBeBound = filter (\n -> isFree expr n && variableName expr n == x) $ bfs b expr
    mapM_ (\n -> modify $ insEdge (n, node, Binding)) toBeBound

    return lambdaNode

app :: Monad m => ExprNode -> ExprNode -> ExprT m ExprNode
app fun arg = do
    node <- newNode
    let appNode = (node, App)
    modify $ insNode appNode
    modify $ insEdge (fst appNode, fst fun, Function)
    modify $ insEdge (fst appNode, fst arg, Argument)
    return appNode

newNode :: Monad m => ExprT m Node
newNode = get >>= return . head . newNodes 1

buildExprT :: Monad m => ExprT m a -> m (a, Expr)
buildExprT = flip runStateT empty

buildExprT' :: Monad m => ExprT m ExprNode -> m Pair
buildExprT' e = do
    (node, expr) <- flip runStateT empty $ e
    return $ Pair node expr

runExprT :: Monad m => ExprT m a -> m a
runExprT = flip evalStateT empty

free :: Expr -> [ExprNode]
free expr = labNodes $ labnfilter labledIsFreeVariable expr
    where
        labledIsFreeVariable ln @ (n, _)
            | labledIsVariable ln = Binding `notElem` map edgeLabel (out expr n)
            | otherwise = False
        labledIsVariable (_, Variable _) = True
        labledIsVariable _ = False

variableName :: Expr -> Node -> Name
variableName expr n = let (Variable name) = lab' $ context expr n
                       in name

isVariable :: Expr -> Node -> Bool
isVariable expr n = case lab' $ context expr n of
                      Variable _ -> True
                      _ -> False

isFree :: Expr -> Node -> Bool
isFree expr n = isVariable expr n && case map edgeLabel . out' $ context expr n of
                                       [Binding] -> False
                                       [] -> True
                                       _ -> error "Invariant violated: non-binding edge out from variable, or too many outgoing edges from variable"

body :: Expr -> Node -> ExprNode
body expr node = let [(_, b, Body)] = out expr node
                  in labNode' $ context expr b

argument :: Expr -> Node -> ExprNode
argument expr node = let [(_, a, Argument)] = filter (\(_, _, t) -> t == Argument) $ out expr node
                      in labNode' $ context expr a

function :: Expr -> Node -> ExprNode
function expr node = let [(_, f, Function)] = filter (\(_, _, t) -> t == Function) $ out expr node
                      in labNode' $ context expr f

parent :: Expr -> Node -> Maybe (Node, EdgeLabel)
parent expr node = case filter relevantEdge $ inn expr node of
                     [] -> Nothing
                     [(i, _, t)] -> Just (i, t)
                     _ -> error "Invariant violated: more than one parent"
                    where
                        relevantEdge (_, _, Body) = True
                        relevantEdge (_, _, Function) = True
                        relevantEdge (_, _, Argument) = True
                        relevantEdge _ = False

parents :: Expr -> Node -> [(Node, EdgeLabel)]
parents expr node = case parent expr node of
                      Just p@(parentNode, _) -> p : parents expr parentNode
                      Nothing -> []

alphaEquivalent :: (ExprNode, Expr) -> (ExprNode, Expr) -> Bool
((n1, Variable _), expr1) `alphaEquivalent` ((n2, Variable _), expr2)
    | isFree expr1 n1 = False
    | isFree expr2 n2 = False
    | otherwise = bindingHeight expr1 n1 == bindingHeight expr2 n2
        where
            bindingHeight expr n = length $ takeWhile (\(m, _) -> m /= bindingNode expr n) $ parents expr n
            bindingNode expr n = let [(_, ln, Binding)] = out expr n in ln

((n1, Lambda _), expr1) `alphaEquivalent` ((n2, Lambda _), expr2) =
    (body expr1 n1, expr1) `alphaEquivalent` (body expr2 n2, expr2)

((n1, App), expr1) `alphaEquivalent` ((n2, App), expr2) =
    (function expr1 n1, expr1) `alphaEquivalent` (function expr2 n2, expr2)
    && (argument expr1 n1, expr1) `alphaEquivalent` (argument expr2 n2, expr2)

(_, _) `alphaEquivalent` (_, _) = False

substitute :: Monad m => ExprNode -> (Name, ExprNode) -> ExprT m ExprNode
substitute v@(n, Variable vn) (name, m)
    | vn == name = return m
    | otherwise = return v

with :: a -> b -> (a, b)
a `with` b = (a,b)

main :: IO ()
main = hspec $ do
    describe "parent" $ do
        it "should return Nothing for orphans" $ runExprT $ do
            (x, _) <- variable "x"
            expr <- get
            lift $ parent expr x `shouldBe` Nothing
        it "should return Just (l, Body) for x in: λy.x" $ runExprT $ do
            x@(xn, _) <- variable "x"
            (l, _) <- lambda "y" x
            expr <- get
            lift $ parent expr xn `shouldBe` Just (l, Body)
        it "should return Just (a, Function) for x in: x y" $ runExprT $ do
            x@(xn, _) <- variable "x"
            y <- variable "y"
            (a, _) <- app x y
            expr <- get
            lift $ parent expr xn `shouldBe` Just (a, Function)
        it "should return Just (a, Argument) for x in: y x" $ runExprT $ do
            x@(xn, _) <- variable "x"
            y <- variable "y"
            (a, _) <- app y x
            expr <- get
            lift $ parent expr xn `shouldBe` Just (a, Argument)

    describe "parents" $ do
        it "should return [] for orphans" $ runExprT $ do
            (x, _) <- variable "x"
            expr <- get
            lift $ parents expr x `shouldBe` []
        it "should return [(a2, Argument), (a1, Function), (l, Body)] for x in: λu.(v x) w" $ runExprT $ do
            x@(xn, _) <- variable "x"
            v <- variable "v"
            w <- variable "w"
            a2@(an2, _) <- app v x
            a1@(an1, _) <- app a2 w
            (l, _) <- lambda "u" a1
            expr <- get
            lift $ parents expr xn `shouldBe` [(an2, Argument), (an1, Function), (l, Body)]


    describe "variable" $ do
        it "should create a lone node" $ runExprT $ do
            (n, Variable "x") <- variable "x"
            expr <- get
            lift $ out expr n `shouldBe` []
            lift $ inn expr n `shouldBe` []

    describe "lambda" $ do
        it "should bind x in: λx.x " $ runExprT $ do
            x@(xn, Variable _) <- variable "x"
            (ln, Lambda _) <- lambda "x" x
            expr <- get
            lift $ out expr ln `shouldBe` [(ln, xn, Body)]
            lift $ inn expr ln `shouldBe` [(xn, ln, Binding)]
            lift $ out expr xn `shouldBe` [(xn, ln, Binding)]
        it "should not bind x in: λy.x " $ runExprT $ do
            x@(xn, _) <- variable "x"
            (ln, _) <- lambda "y" x
            expr <- get
            lift $ out expr ln `shouldBe` [(ln, xn, Body)]
            lift $ inn expr ln `shouldBe` []
            lift $ out expr xn `shouldBe` []
        it "should bind both x in: λx.x x" $ runExprT $ do
            x1@(xn1, _) <- variable "x"
            x2@(xn2, _) <- variable "x"
            (ln, _) <- lambda "x" =<< app x1 x2
            expr <- get
            lift $ inn expr ln `shouldBe` [(xn1, ln, Binding), (xn2, ln, Binding)]
            lift $ out expr xn1 `shouldBe` [(xn1, ln, Binding)]
            lift $ out expr xn2 `shouldBe` [(xn2, ln, Binding)]
        it "should bind x in: λx.x x" $ runExprT $ do
            x1@(xn1,_) <- variable "x"
            x2@(xn2, _) <- variable "x"
            (ln, _) <- lambda "x" =<< app x1 x2
            expr <- get
            lift $ inn expr ln `shouldBe` [(xn1, ln, Binding), (xn2, ln, Binding)]
            lift $ out expr xn1 `shouldBe` [(xn1, ln, Binding)]
            lift $ out expr xn2 `shouldBe` [(xn2, ln, Binding)]

    describe "app" $ do
        it "should connect the function and argument in: x y" $ runExprT $ do
            x@(xn, Variable _) <- variable "x"
            y@(yn, Variable _) <- variable "y"
            (a, App) <- app x y
            expr <- get
            lift $ out expr a `shouldBe` [(a, xn, Function), (a, yn, Argument)]
            lift $ inn expr a `shouldBe` []

    describe "free" $ do
        it "claims x is free in: x" $ runExprT $ do
            x <- variable "x"
            expr <- get
            lift $ free expr `shouldBe` [x]
        it "claims nothing is free in: λx.x" $ runExprT $ do
            _ <- lambda "x" =<< variable "x"
            expr <- get
            lift $ free expr `shouldBe` []
        it "claims [y] is free in: λx.y" $ runExprT $ do
            y <- variable "y"
            _ <- lambda "x" y
            expr <- get
            lift $ free expr `shouldBe` [y]
        it "claims [x, y] is free in: x y" $ runExprT $ do
            x <- variable "x"
            y <- variable "y"
            _ <- app x y
            expr <- get
            lift $ free expr `shouldBe` [x, y]
        it "claims [y] is free in: λx.x y" $ runExprT $ do
            x <- variable "x"
            y <- variable "y"
            _ <- lambda "x" =<< app x y
            expr <- get
            lift $ free expr `shouldBe` [y]
        it "claims [x] is free in: λy.x y" $ runExprT $ do
            x <- variable "x"
            y <- variable "y"
            _ <- lambda "y" =<< app x y
            expr <- get
            lift $ free expr `shouldBe` [x]
        it "claims nothing is free in: λx.λy.x y" $ runExprT $ do
            x <- variable "x"
            y <- variable "y"
            _ <- lambda "x" =<< lambda "y" =<< app x y
            expr <- get
            lift $ free expr `shouldBe` []
        it "claims nothing is free in: λx.λy.λz.x y" $ runExprT $ do
            x <- variable "x"
            y <- variable "y"
            _ <- lambda "x" =<< lambda "y" =<< lambda "z" =<< app x y
            expr <- get
            lift $ free expr `shouldBe` []
        it "claims [y,z] is free in: (λx.z) y" $ runExprT $ do
            y <- variable "y"
            z <- variable "z"
            f <- lambda "x" z
            _ <- app f y
            expr <- get
            lift $ free expr `shouldBe` [y, z]
        it "claims [y,z] is free in: y (λx.z)" $ runExprT $ do
            y <- variable "y"
            z <- variable "z"
            f <- lambda "x" z
            _ <- app y f
            expr <- get
            lift $ free expr `shouldBe` [y, z]
        it "claims [x] is free in: x x y" $ runExprT $ do
            x <- variable "x"
            _ <- app x x
            expr <- get
            lift $ free expr `shouldBe` [x]

    describe "alphaEquivalent" $ do
        it "claims x and y are not alpha-equivalent" $ do
            expr1 <- buildExprT $ variable "x"
            expr2 <- buildExprT $ variable "y"
            (expr1 `alphaEquivalent` expr2) `shouldBe` False
        it "claims λx.x and y are not alpha-equivalent" $ do
            expr1 <- buildExprT $ lambda "x" =<< variable "x"
            expr2 <- buildExprT $ variable "y"
            (expr1 `alphaEquivalent` expr2) `shouldBe` False
        it "claims x y and z are not alpha-equivalent" $ do
            expr1 <- buildExprT $ do
               x <- variable "x"
               y <- variable "y"
               app x y
            expr2 <- buildExprT $ variable "z"
            (expr1 `alphaEquivalent` expr2) `shouldBe` False
        it "claims x y and u v are not alpha-equivalent" $ do
            expr1 <- buildExprT $ do
               x <- variable "x"
               y <- variable "y"
               app x y
            expr2 <- buildExprT $ do
               u <- variable "u"
               v <- variable "v"
               app u v
            (expr1 `alphaEquivalent` expr2) `shouldBe` False
        it "claims λx.λy.x y and λu.λu.u u are not alpha-equivalent" $ do
            expr1 <- buildExprT $ do
               x <- variable "x"
               y <- variable "y"
               lambda "x" =<< lambda "y" =<< app x y
            expr2 <- buildExprT $ do
               u1 <- variable "u"
               u2 <- variable "u"
               lambda "u" =<< lambda "u" =<< app u1 u2
            (expr1 `alphaEquivalent` expr2) `shouldBe` False
        it "claims λx.x and λy.y are alpha-equivalent" $ do
            expr1 <- buildExprT $ lambda "x" =<< variable "x"
            expr2 <- buildExprT $ lambda "y" =<< variable "y"
            (expr1 `alphaEquivalent` expr2) `shouldBe` True
        it "claims λx.y and λz.z are not alpha-equivalent" $ do
            expr1 <- buildExprT $ lambda "x" =<< variable "y"
            expr2 <- buildExprT $ lambda "z" =<< variable "z"
            (expr1 `alphaEquivalent` expr2) `shouldBe` False

        -- Examples from: https://en.wikipedia.org/wiki/Lambda_calculus#.CE.B1-conversion
        it "claims λx.λx.x and λy.λx.x are alpha-equivalent" $ do
            expr1 <- buildExprT $ lambda "x" =<< lambda "x" =<< variable "x"
            expr2 <- buildExprT $ lambda "y" =<< lambda "x" =<< variable "x"
            (expr1 `alphaEquivalent` expr2) `shouldBe` True
        it "claims λx.λx.x and λy.λx.y are not alpha-equivalent" $ do
            expr1 <- buildExprT $ lambda "x" =<< lambda "x" =<< variable "x"
            expr2 <- buildExprT $ lambda "y" =<< lambda "x" =<< variable "y"
            (expr1 `alphaEquivalent` expr2) `shouldBe` False
        it "claims λx.λy.x and λy.λy.y are not alpha-equivalent" $ do
            expr1 <- buildExprT $ lambda "x" =<< lambda "y" =<< variable "x"
            expr2 <- buildExprT $ lambda "y" =<< lambda "y" =<< variable "y"
            (expr1 `alphaEquivalent` expr2) `shouldBe` False

        it "claims λx.y x and λx.x y are not alpha-equivalent" $ do
            expr1 <- buildExprT $ do
               x <- variable "x"
               y <- variable "y"
               lambda "x" =<< app x y
            expr2 <- buildExprT $ do
               x <- variable "x"
               y <- variable "y"
               lambda "x" =<< app y x
            (expr1 `alphaEquivalent` expr2) `shouldBe` False
        
        it "claims λy.λx.y x and λy.λx.x y are not alpha-equivalent" $ do
            expr1 <- buildExprT $ do
               x <- variable "x"
               y <- variable "y"
               lambda "y" =<< lambda "x" =<< app x y
            expr2 <- buildExprT $ do
               x <- variable "x"
               y <- variable "y"
               lambda "y" =<< lambda "x" =<< app y x
            (expr1 `alphaEquivalent` expr2) `shouldBe` False
    describe "substitute" $ do
        it "should satisfy x[x := n] = n" $ runExprT $ do
            x <- variable "x"
            n <- variable "n"
            m <- x `substitute` ("x" `with` n)
            lift $ m `shouldBe` n
        it "should satisfy y[x := n] = y" $ runExprT $ do
            y <- variable "y"
            n <- variable "n"
            m <- y `substitute` ("x" `with` n)
            lift $ m `shouldBe` y
