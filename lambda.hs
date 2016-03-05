{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances #-}
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

type Program = Gr NodeLabel EdgeLabel
type ProgramNode = LNode NodeLabel
type ProgramEdge = LEdge EdgeLabel

newtype ProgramT m a = ProgramT {unProgramT :: StateT Program m a}
    deriving (Monad, MonadState Program, Applicative, Functor, MonadTrans)

data Expr = Expr { exprNode :: ProgramNode, exprProgram :: Program }

instance Arbitrary (ProgramT Gen ProgramNode) where
    arbitrary = genProgram
        where
            genProgram :: Gen (ProgramT Gen ProgramNode)
            genProgram = oneof [genVariable, genLambda, genApp]
            genVariable :: Gen (ProgramT Gen ProgramNode)
            genVariable = return $ variable =<< lift genVariableName
            genLambda :: Gen (ProgramT Gen ProgramNode)
            genLambda = do
                n <- genVariableName
                b <- genProgram
                return $ b >>= lambda n
            genApp :: Gen (ProgramT Gen ProgramNode)
            genApp = do
                fM <- genProgram
                aM <- genProgram
                return $ do
                   f <- fM
                   a <- aM
                   app f a
            genVariableName :: Gen Name
            genVariableName = elements ["a","b","c","u","v","w","x","y","z"]

instance Arbitrary Expr where
    arbitrary = arbitrary >>= buildProgramT

instance Show Expr where
    show (Expr (_, Variable name) _) = name
    show (Expr (ln, Lambda name) expr) = "(λ" ++ name ++ "." ++ show (Expr (body expr ln) expr) ++ ")"
    show (Expr (an, App) expr) = "(" ++ show (Expr (function expr an) expr) ++ " " ++ show (Expr ( argument expr an) expr) ++ ")"


variable :: Monad m => Name -> ProgramT m ProgramNode
variable n = ProgramT $ do
    node <- unProgramT $ newNode
    let lnode = (node, Variable n)
    modify $ insNode lnode
    return lnode

lambda :: Monad m => Name -> ProgramNode -> ProgramT m ProgramNode
lambda x (b, _) = ProgramT $ do
    node <- unProgramT $ newNode
    let lambdaNode = (node, Lambda x)
    let bodyEdge = (node, b, Body)
    modify $ insNode lambdaNode
    modify $ insEdge bodyEdge

    expr <- get
    let toBeBound = filter (\n -> isFree expr n && variableName expr n == x) $ bfs b expr
    mapM_ (\n -> modify $ insEdge (n, node, Binding)) toBeBound

    return lambdaNode

app :: Monad m => ProgramNode -> ProgramNode -> ProgramT m ProgramNode
app fun arg = ProgramT $ do
    node <- unProgramT $ newNode
    let appNode = (node, App)
    modify $ insNode appNode
    modify $ insEdge (fst appNode, fst fun, Function)
    modify $ insEdge (fst appNode, fst arg, Argument)
    return appNode

newNode :: Monad m => ProgramT m Node
newNode = ProgramT $ get >>= return . head . newNodes 1

buildProgramT :: Monad m => ProgramT m ProgramNode -> m Expr
buildProgramT p = do
    (node, expr) <- flip runStateT empty $ unProgramT p
    return $ Expr node expr

runProgramT :: Monad m => ProgramT m a -> m a
runProgramT = flip evalStateT empty . unProgramT

free :: Program -> [ProgramNode]
free expr = labNodes $ labnfilter labledIsFreeVariable expr
    where
        labledIsFreeVariable ln @ (n, _)
            | labledIsVariable ln = Binding `notElem` map edgeLabel (out expr n)
            | otherwise = False
        labledIsVariable (_, Variable _) = True
        labledIsVariable _ = False

variableName :: Program -> Node -> Name
variableName expr n = let (Variable name) = lab' $ context expr n
                       in name

isVariable :: Program -> Node -> Bool
isVariable expr n = case lab' $ context expr n of
                      Variable _ -> True
                      _ -> False

isFree :: Program -> Node -> Bool
isFree expr n = isVariable expr n && case map edgeLabel . out' $ context expr n of
                                       [Binding] -> False
                                       [] -> True
                                       _ -> error "Invariant violated: non-binding edge out from variable, or too many outgoing edges from variable"

body :: Program -> Node -> ProgramNode
body expr node = let [(_, b, Body)] = out expr node
                  in labNode' $ context expr b

argument :: Program -> Node -> ProgramNode
argument expr node = let [(_, a, Argument)] = filter (\(_, _, t) -> t == Argument) $ out expr node
                      in labNode' $ context expr a

function :: Program -> Node -> ProgramNode
function expr node = let [(_, f, Function)] = filter (\(_, _, t) -> t == Function) $ out expr node
                      in labNode' $ context expr f

parent :: Program -> Node -> Maybe (Node, EdgeLabel)
parent expr node = case filter relevantEdge $ inn expr node of
                     [] -> Nothing
                     [(i, _, t)] -> Just (i, t)
                     _ -> error "Invariant violated: more than one parent"
                    where
                        relevantEdge (_, _, Body) = True
                        relevantEdge (_, _, Function) = True
                        relevantEdge (_, _, Argument) = True
                        relevantEdge _ = False

parents :: Program -> Node -> [(Node, EdgeLabel)]
parents expr node = case parent expr node of
                      Just p@(parentNode, _) -> p : parents expr parentNode
                      Nothing -> []

alphaEquivalent :: Expr -> Expr -> Bool
(Expr (n1, Variable _) expr1) `alphaEquivalent` (Expr (n2, Variable _) expr2)
    | isFree expr1 n1 = False
    | isFree expr2 n2 = False
    | otherwise = bindingHeight expr1 n1 == bindingHeight expr2 n2
        where
            bindingHeight expr n = length $ takeWhile (\(m, _) -> m /= bindingNode expr n) $ parents expr n
            bindingNode expr n = let [(_, ln, Binding)] = out expr n in ln

(Expr (n1, Lambda _) expr1) `alphaEquivalent` (Expr (n2, Lambda _) expr2) =
    (Expr (body expr1 n1) expr1) `alphaEquivalent` (Expr (body expr2 n2) expr2)

(Expr (n1, App) expr1) `alphaEquivalent` (Expr (n2, App) expr2) =
    (Expr (function expr1 n1) expr1) `alphaEquivalent` (Expr (function expr2 n2) expr2)
    && (Expr (argument expr1 n1) expr1) `alphaEquivalent` (Expr (argument expr2 n2) expr2)

_ `alphaEquivalent` _ = False

substitute :: Monad m => ProgramNode -> (Name, ProgramNode) -> ProgramT m ProgramNode
substitute v@(_, Variable vn) (name, m)
    | vn == name = return m
    | otherwise = return v

with :: a -> b -> (a, b)
a `with` b = (a,b)

main :: IO ()
main = hspec $ do
    describe "parent" $ do
        it "should return Nothing for orphans" $ runProgramT $ do
            (x, _) <- variable "x"
            expr <- get
            lift $ parent expr x `shouldBe` Nothing
        it "should return Just (l, Body) for x in: λy.x" $ runProgramT $ do
            x@(xn, _) <- variable "x"
            (l, _) <- lambda "y" x
            expr <- get
            lift $ parent expr xn `shouldBe` Just (l, Body)
        it "should return Just (a, Function) for x in: x y" $ runProgramT $ do
            x@(xn, _) <- variable "x"
            y <- variable "y"
            (a, _) <- app x y
            expr <- get
            lift $ parent expr xn `shouldBe` Just (a, Function)
        it "should return Just (a, Argument) for x in: y x" $ runProgramT $ do
            x@(xn, _) <- variable "x"
            y <- variable "y"
            (a, _) <- app y x
            expr <- get
            lift $ parent expr xn `shouldBe` Just (a, Argument)

    describe "parents" $ do
        it "should return [] for orphans" $ runProgramT $ do
            (x, _) <- variable "x"
            expr <- get
            lift $ parents expr x `shouldBe` []
        it "should return [(a2, Argument), (a1, Function), (l, Body)] for x in: λu.(v x) w" $ runProgramT $ do
            x@(xn, _) <- variable "x"
            v <- variable "v"
            w <- variable "w"
            a2@(an2, _) <- app v x
            a1@(an1, _) <- app a2 w
            (l, _) <- lambda "u" a1
            expr <- get
            lift $ parents expr xn `shouldBe` [(an2, Argument), (an1, Function), (l, Body)]


    describe "variable" $ do
        it "should create a lone node" $ runProgramT $ do
            (n, Variable "x") <- variable "x"
            expr <- get
            lift $ out expr n `shouldBe` []
            lift $ inn expr n `shouldBe` []

    describe "lambda" $ do
        it "should bind x in: λx.x " $ runProgramT $ do
            x@(xn, Variable _) <- variable "x"
            (ln, Lambda _) <- lambda "x" x
            expr <- get
            lift $ out expr ln `shouldBe` [(ln, xn, Body)]
            lift $ inn expr ln `shouldBe` [(xn, ln, Binding)]
            lift $ out expr xn `shouldBe` [(xn, ln, Binding)]
        it "should not bind x in: λy.x " $ runProgramT $ do
            x@(xn, _) <- variable "x"
            (ln, _) <- lambda "y" x
            expr <- get
            lift $ out expr ln `shouldBe` [(ln, xn, Body)]
            lift $ inn expr ln `shouldBe` []
            lift $ out expr xn `shouldBe` []
        it "should bind both x in: λx.x x" $ runProgramT $ do
            x1@(xn1, _) <- variable "x"
            x2@(xn2, _) <- variable "x"
            (ln, _) <- lambda "x" =<< app x1 x2
            expr <- get
            lift $ inn expr ln `shouldBe` [(xn1, ln, Binding), (xn2, ln, Binding)]
            lift $ out expr xn1 `shouldBe` [(xn1, ln, Binding)]
            lift $ out expr xn2 `shouldBe` [(xn2, ln, Binding)]
        it "should bind x in: λx.x x" $ runProgramT $ do
            x1@(xn1,_) <- variable "x"
            x2@(xn2, _) <- variable "x"
            (ln, _) <- lambda "x" =<< app x1 x2
            expr <- get
            lift $ inn expr ln `shouldBe` [(xn1, ln, Binding), (xn2, ln, Binding)]
            lift $ out expr xn1 `shouldBe` [(xn1, ln, Binding)]
            lift $ out expr xn2 `shouldBe` [(xn2, ln, Binding)]

    describe "app" $ do
        it "should connect the function and argument in: x y" $ runProgramT $ do
            x@(xn, Variable _) <- variable "x"
            y@(yn, Variable _) <- variable "y"
            (a, App) <- app x y
            expr <- get
            lift $ out expr a `shouldBe` [(a, xn, Function), (a, yn, Argument)]
            lift $ inn expr a `shouldBe` []

    describe "free" $ do
        it "claims x is free in: x" $ runProgramT $ do
            x <- variable "x"
            expr <- get
            lift $ free expr `shouldBe` [x]
        it "claims nothing is free in: λx.x" $ runProgramT $ do
            _ <- lambda "x" =<< variable "x"
            expr <- get
            lift $ free expr `shouldBe` []
        it "claims [y] is free in: λx.y" $ runProgramT $ do
            y <- variable "y"
            _ <- lambda "x" y
            expr <- get
            lift $ free expr `shouldBe` [y]
        it "claims [x, y] is free in: x y" $ runProgramT $ do
            x <- variable "x"
            y <- variable "y"
            _ <- app x y
            expr <- get
            lift $ free expr `shouldBe` [x, y]
        it "claims [y] is free in: λx.x y" $ runProgramT $ do
            x <- variable "x"
            y <- variable "y"
            _ <- lambda "x" =<< app x y
            expr <- get
            lift $ free expr `shouldBe` [y]
        it "claims [x] is free in: λy.x y" $ runProgramT $ do
            x <- variable "x"
            y <- variable "y"
            _ <- lambda "y" =<< app x y
            expr <- get
            lift $ free expr `shouldBe` [x]
        it "claims nothing is free in: λx.λy.x y" $ runProgramT $ do
            x <- variable "x"
            y <- variable "y"
            _ <- lambda "x" =<< lambda "y" =<< app x y
            expr <- get
            lift $ free expr `shouldBe` []
        it "claims nothing is free in: λx.λy.λz.x y" $ runProgramT $ do
            x <- variable "x"
            y <- variable "y"
            _ <- lambda "x" =<< lambda "y" =<< lambda "z" =<< app x y
            expr <- get
            lift $ free expr `shouldBe` []
        it "claims [y,z] is free in: (λx.z) y" $ runProgramT $ do
            y <- variable "y"
            z <- variable "z"
            f <- lambda "x" z
            _ <- app f y
            expr <- get
            lift $ free expr `shouldBe` [y, z]
        it "claims [y,z] is free in: y (λx.z)" $ runProgramT $ do
            y <- variable "y"
            z <- variable "z"
            f <- lambda "x" z
            _ <- app y f
            expr <- get
            lift $ free expr `shouldBe` [y, z]
        it "claims [x] is free in: x x y" $ runProgramT $ do
            x <- variable "x"
            _ <- app x x
            expr <- get
            lift $ free expr `shouldBe` [x]

    describe "alphaEquivalent" $ do
        it "claims x and y are not alpha-equivalent" $ do
            expr1 <- buildProgramT $ variable "x"
            expr2 <- buildProgramT $ variable "y"
            (expr1 `alphaEquivalent` expr2) `shouldBe` False
        it "claims λx.x and y are not alpha-equivalent" $ do
            expr1 <- buildProgramT $ lambda "x" =<< variable "x"
            expr2 <- buildProgramT $ variable "y"
            (expr1 `alphaEquivalent` expr2) `shouldBe` False
        it "claims x y and z are not alpha-equivalent" $ do
            expr1 <- buildProgramT $ do
               x <- variable "x"
               y <- variable "y"
               app x y
            expr2 <- buildProgramT $ variable "z"
            (expr1 `alphaEquivalent` expr2) `shouldBe` False
        it "claims x y and u v are not alpha-equivalent" $ do
            expr1 <- buildProgramT $ do
               x <- variable "x"
               y <- variable "y"
               app x y
            expr2 <- buildProgramT $ do
               u <- variable "u"
               v <- variable "v"
               app u v
            (expr1 `alphaEquivalent` expr2) `shouldBe` False
        it "claims λx.λy.x y and λu.λu.u u are not alpha-equivalent" $ do
            expr1 <- buildProgramT $ do
               x <- variable "x"
               y <- variable "y"
               lambda "x" =<< lambda "y" =<< app x y
            expr2 <- buildProgramT $ do
               u1 <- variable "u"
               u2 <- variable "u"
               lambda "u" =<< lambda "u" =<< app u1 u2
            (expr1 `alphaEquivalent` expr2) `shouldBe` False
        it "claims λx.x and λy.y are alpha-equivalent" $ do
            expr1 <- buildProgramT $ lambda "x" =<< variable "x"
            expr2 <- buildProgramT $ lambda "y" =<< variable "y"
            (expr1 `alphaEquivalent` expr2) `shouldBe` True
        it "claims λx.y and λz.z are not alpha-equivalent" $ do
            expr1 <- buildProgramT $ lambda "x" =<< variable "y"
            expr2 <- buildProgramT $ lambda "z" =<< variable "z"
            (expr1 `alphaEquivalent` expr2) `shouldBe` False

        -- Examples from: https://en.wikipedia.org/wiki/Lambda_calculus#.CE.B1-conversion
        it "claims λx.λx.x and λy.λx.x are alpha-equivalent" $ do
            expr1 <- buildProgramT $ lambda "x" =<< lambda "x" =<< variable "x"
            expr2 <- buildProgramT $ lambda "y" =<< lambda "x" =<< variable "x"
            (expr1 `alphaEquivalent` expr2) `shouldBe` True
        it "claims λx.λx.x and λy.λx.y are not alpha-equivalent" $ do
            expr1 <- buildProgramT $ lambda "x" =<< lambda "x" =<< variable "x"
            expr2 <- buildProgramT $ lambda "y" =<< lambda "x" =<< variable "y"
            (expr1 `alphaEquivalent` expr2) `shouldBe` False
        it "claims λx.λy.x and λy.λy.y are not alpha-equivalent" $ do
            expr1 <- buildProgramT $ lambda "x" =<< lambda "y" =<< variable "x"
            expr2 <- buildProgramT $ lambda "y" =<< lambda "y" =<< variable "y"
            (expr1 `alphaEquivalent` expr2) `shouldBe` False

        it "claims λx.y x and λx.x y are not alpha-equivalent" $ do
            expr1 <- buildProgramT $ do
               x <- variable "x"
               y <- variable "y"
               lambda "x" =<< app x y
            expr2 <- buildProgramT $ do
               x <- variable "x"
               y <- variable "y"
               lambda "x" =<< app y x
            (expr1 `alphaEquivalent` expr2) `shouldBe` False
        
        it "claims λy.λx.y x and λy.λx.x y are not alpha-equivalent" $ do
            expr1 <- buildProgramT $ do
               x <- variable "x"
               y <- variable "y"
               lambda "y" =<< lambda "x" =<< app x y
            expr2 <- buildProgramT $ do
               x <- variable "x"
               y <- variable "y"
               lambda "y" =<< lambda "x" =<< app y x
            (expr1 `alphaEquivalent` expr2) `shouldBe` False
    describe "substitute" $ do
        it "should satisfy x[x := n] = n" $ runProgramT $ do
            x <- variable "x"
            n <- variable "n"
            m <- x `substitute` ("x" `with` n)
            lift $ m `shouldBe` n
        it "should satisfy y[x := n] = y" $ runProgramT $ do
            y <- variable "y"
            n <- variable "n"
            m <- y `substitute` ("x" `with` n)
            lift $ m `shouldBe` y

    describe "Expr's show instance" $ do
        it "shows x correctly" $ do
            p <- buildProgramT $ variable "x"
            show p `shouldBe` "x"
        it "shows λx.y correctly" $ do
            p <- buildProgramT $ lambda "x" =<< variable "y"
            show p `shouldBe` "(λx.y)"
        it "shows x y correctly" $ do
            p <- buildProgramT $ do
               x <- variable "x"
               y <- variable "y"
               app x y
            show p `shouldBe` "(x y)"

