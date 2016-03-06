{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances #-}
module Lamda where

import Test.Hspec hiding (context)
import Test.QuickCheck
import Data.Graph.Inductive
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Writer
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

instance Monad m => Arbitrary (ProgramT m ProgramNode) where
    arbitrary = genProgram =<< (liftM getPositive $ arbitrary)
        where
            genProgram :: Monad m => Int -> Gen (ProgramT m ProgramNode)
            genProgram l
                | l > 0 = oneof [genVariable, genLambda (l - 1), genApp (l - 1)]
                | otherwise = genVariable
            genVariable :: Monad m => Gen (ProgramT m ProgramNode)
            genVariable = genVariableName >>= return . variable
            genLambda :: Monad m => Int -> Gen (ProgramT m ProgramNode)
            genLambda l = do
                n <- genVariableName
                b <- genProgram l
                return $ b >>= lambda n
            genApp :: Monad m => Int -> Gen (ProgramT m ProgramNode)
            genApp l = do
                fM <- genProgram l
                aM <- genProgram l
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


showHighlighted :: (Node -> Bool) -> Expr -> String
showHighlighted p (Expr (vn, Variable name) _)
    | p vn = highlight name
    | otherwise = name
showHighlighted p (Expr (ln, Lambda name) expr)
    | p ln = highlight $ str
    | otherwise = str
        where
            str = "(λ" ++ name ++ "." ++ showHighlighted p (Expr (body expr ln) expr) ++ ")"
showHighlighted p (Expr (an, App) expr)
    | p an = highlight $ str
    | otherwise = str
        where
            str = "(" ++ show (Expr (function expr an) expr) ++ " " ++ showHighlighted p (Expr ( argument expr an) expr) ++ ")"

highlight :: String -> String
highlight s = "<<" ++ s ++ ">>"

spec_Expr_Show_instance :: SpecWith ()
spec_Expr_Show_instance = describe "Expr's show instance" $ do
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


instance Eq Expr where
    (Expr (n1, _) p1) == (Expr (n2, _) p2) = (pathifier n1 p1) == (pathifier n2 p2)
        where
            pathifier n p = bfsWith (\c -> ((map edgeLabel $ out' c), lab' c)) n p

spec_Expr_Eq_instance :: SpecWith ()
spec_Expr_Eq_instance = describe "Expr's Eq instance" $ do
    it "is reflexive" $ property $
        \e -> (e :: Expr) == (e :: Expr)
    it "sees the difference between variables" $ do
        p1 <- buildProgramT $ variable "x"
        p2 <- buildProgramT $ variable "y"
        p1 `shouldNotBe` p2
    it "claims variables are the same even though they are from truly different graphs" $ do
        p1 <- buildProgramT $ variable "z" >> variable "x"
        p2 <- buildProgramT $ variable "x"
        p1 `shouldBe` p2
    it "sees the difference between bound and free variables" $ do
        p1 <- buildProgramT $ do
            x <- variable "x"
            _ <- lambda "x" x
            return x
        p2 <- buildProgramT $ variable "x"
        p1 `shouldNotBe` p2



variable :: Monad m => Name -> ProgramT m ProgramNode
variable n = ProgramT $ do
    node <- unProgramT $ newNode
    let lnode = (node, Variable n)
    modify $ insNode lnode
    return lnode

spec_variable :: SpecWith ()
spec_variable = describe "variable" $ do
    it "should create a lone node" $ runProgramT $ do
        (n, Variable "x") <- variable "x"
        expr <- get
        lift $ out expr n `shouldBe` []
        lift $ inn expr n `shouldBe` []



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

spec_lambda :: SpecWith ()
spec_lambda = describe "lambda" $ do
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



app :: Monad m => ProgramNode -> ProgramNode -> ProgramT m ProgramNode
app fun arg = ProgramT $ do
    node <- unProgramT $ newNode
    let appNode = (node, App)
    modify $ insNode appNode
    modify $ insEdge (fst appNode, fst fun, Function)
    modify $ insEdge (fst appNode, fst arg, Argument)
    return appNode

spec_app :: SpecWith ()
spec_app = describe "app" $ do
    it "should connect the function and argument in: x y" $ runProgramT $ do
        x@(xn, Variable _) <- variable "x"
        y@(yn, Variable _) <- variable "y"
        (a, App) <- app x y
        expr <- get
        lift $ out expr a `shouldBe` [(a, xn, Function), (a, yn, Argument)]
        lift $ inn expr a `shouldBe` []



newNode :: Monad m => ProgramT m Node
newNode = ProgramT $ get >>= return . head . newNodes 1

buildProgramT :: Monad m => ProgramT m ProgramNode -> m Expr
buildProgramT p = do
    (node, expr) <- flip runStateT empty $ unProgramT p
    return $ Expr node expr

buildProgram :: ProgramT Identity ProgramNode -> Expr
buildProgram = runIdentity . buildProgramT

runProgramT :: Monad m => ProgramT m a -> m a
runProgramT = withProgramT empty

runProgram :: ProgramT Identity a -> a
runProgram = runIdentity . withProgramT empty

withProgramT :: Monad m => Program -> ProgramT m a -> m a
withProgramT program = flip evalStateT program . unProgramT

withProgram :: Program -> ProgramT Identity a -> a
withProgram program = runIdentity . withProgramT program


free :: Program -> [ProgramNode]
free expr = labNodes $ labnfilter labledIsFreeVariable expr
    where
        labledIsFreeVariable ln @ (n, _)
            | labledIsVariable ln = Binding `notElem` map edgeLabel (out expr n)
            | otherwise = False
        labledIsVariable (_, Variable _) = True
        labledIsVariable _ = False

spec_free :: SpecWith ()
spec_free = describe "free" $ do
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

argument' :: Expr -> Expr
argument' (Expr (n, _) expr) = Expr (argument expr n) expr

function :: Program -> Node -> ProgramNode
function expr node = let [(_, f, Function)] = filter (\(_, _, t) -> t == Function) $ out expr node
                      in labNode' $ context expr f

function' :: Expr -> Expr
function' (Expr (n, _) expr) = Expr (function expr n) expr



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

spec_parent :: SpecWith ()
spec_parent = describe "parent" $ do
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





parents :: Program -> Node -> [(Node, EdgeLabel)]
parents expr node = case parent expr node of
                      Just p@(parentNode, _) -> p : parents expr parentNode
                      Nothing -> []

spec_parents :: SpecWith ()
spec_parents = describe "parents" $ do
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




data AlphaEquivalence = AlphaEquivalent | NotAlphaEquivalent String

instance Show AlphaEquivalence where
    show AlphaEquivalent = "AlphaEquivalent"
    show (NotAlphaEquivalent reason) = "Not alpha-equivalent because: " ++ reason

instance Eq AlphaEquivalence where
    AlphaEquivalent == AlphaEquivalent = True
    NotAlphaEquivalent _ == NotAlphaEquivalent _ = True
    _ == _ = False

alphaEquivalent :: Expr -> Expr -> Bool
alphaEquivalent e1 e2 = case alphaEquivalent' e1 e2 of
                          AlphaEquivalent -> True
                          NotAlphaEquivalent _ -> False

alphaEquivalent' :: Expr -> Expr -> AlphaEquivalence
alphaEquivalent' e1 e2 = case runWriter $ alphaEquivalentWriter (e1, e2) e1 e2 of
                           (True, _) -> AlphaEquivalent
                           (False, reason) -> NotAlphaEquivalent reason

alphaEquivalentWriter :: (Expr, Expr) -> Expr -> Expr -> Writer String Bool
alphaEquivalentWriter start (Expr (n1, Variable _) program1) (Expr (n2, Variable _) program2)
    | isFree program1 n1 = do
        tell $ "variable is not free in first expression: "
        tell $ showHighlighted (==n1) (fst start)
        tell $ " when compared to second expression: " 
        tell $ showHighlighted (==n2) (snd start)
        return False
    | isFree program2 n2 = do
        tell $ "variable is not free in second expression: "
        tell $ showHighlighted (==n2) (snd start)
        tell $ " when compared to first expression: " 
        tell $ showHighlighted (==n1) (fst start)
        return False
    | otherwise = return $ bindingHeight program1 n1 == bindingHeight program2 n2
        where
            bindingHeight expr n = length $ takeWhile (\(m, _) -> m /= bindingNode expr n) $ parents expr n
            bindingNode expr n = let [(_, ln, Binding)] = out expr n in ln

alphaEquivalentWriter start (Expr (n1, Lambda _) program1) (Expr (n2, Lambda _) program2) =
    alphaEquivalentWriter start (Expr (body program1 n1) program1) (Expr (body program2 n2) program2)

alphaEquivalentWriter start (Expr (n1, App) program1) (Expr (n2, App) program2) = do
    functionPart <- alphaEquivalentWriter start (Expr (function program1 n1) program1) (Expr (function program2 n2) program2)
    argumentPart <- alphaEquivalentWriter start (Expr (argument program1 n1) program1) (Expr (argument program2 n2) program2)
    return $ functionPart && argumentPart

alphaEquivalentWriter _  _ _ = return False

spec_alphaEquivalent :: SpecWith ()
spec_alphaEquivalent = describe "alphaEquivalent" $ do
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





substitute :: Monad m => ProgramNode -> (Name, ProgramNode) -> ProgramT m ProgramNode
substitute v@(_, Variable vn) (name, m)
    | vn == name = return m
    | otherwise = return v
substitute (an, App) (name, m) = do
    program <- get
    funSub <- function program an `substitute` (name `with` m)
    argSub <- argument program an `substitute` (name `with` m)
    app funSub argSub
substitute l@(ln, Lambda name1) (name2, m)
    | name1 == name2 = return l
    | otherwise = do
        program <- get
        newBody <- body program ln `substitute` (name2 `with` m)
        lambda name1 newBody


with :: a -> b -> (a, b)
a `with` b = (a,b)

spec_substitute :: SpecWith ()
spec_substitute = describe "substitute" $ do
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
    it "should substitute (x x)[x := n] = (n n)" $ runProgramT $ do
        x1 <- variable "x"
        x2 <- variable "x"
        a <- app x1 x2
        n <- variable "n"
        (sub, App) <- a `substitute` ("x" `with` n)
        program <- get
        lift $ function program sub `shouldBe` n
        lift $ argument program sub `shouldBe` n
    it "should substitute (x y)[x := n] = (n y)" $ runProgramT $ do
        x <- variable "x"
        y <- variable "y"
        a <- app x y
        n <- variable "n"
        (sub, App) <- a `substitute` ("x" `with` n)
        program <- get
        lift $ function program sub `shouldBe` n
        lift $ argument program sub `shouldBe` y
    it "should substitute (λy.x)[x := n] = λy.n" $ do
        lhs <- buildProgramT $ do
            x <- variable "x"
            n <- variable "n"
            l <- lambda "y" x
            l `substitute` ("x" `with` n)
        rhs <- buildProgramT $ do
            n <- variable "n"
            lambda "y" n
        lhs `shouldBe` rhs
    it "should substitute (λx.y)[y := x] alpha-equivalently to λz.x" $ do
        lhs <- buildProgramT $ do
            y <- variable "y"
            l <- lambda "x" y
            x <- variable "x"
            l `substitute` ("y" `with` x)
        rhs <- buildProgramT $ do
            x <- variable "x"
            lambda "z" x
        lhs `alphaEquivalent'` rhs `shouldBe` AlphaEquivalent

    it "should substitute (m1 m2)[x := n] = (m1[x := n] m2[x := n])" $ property $
        prop_substitute_app
    it "should substitute λx.M[x := n] = λx.M" $ property $
        prop_substitute_lambda_same_variable
    it "should substitute (λy.M)[x := n] = λy.(M[x := n])" $ property $
        prop_substitute_lambda_different_variable

instance Show (ProgramT Identity ProgramNode) where
    show = show . buildProgram

prop_substitute_app :: ProgramT Identity ProgramNode -> ProgramT Identity ProgramNode -> ProgramT Identity ProgramNode -> Bool
prop_substitute_app m1 m2 nM = (function' asub) == m1sub && (argument' asub) == m2sub
    where
        asub = buildProgram $ do
                fun <- m1
                arg <- m2
                n <- nM
                a <- app fun arg
                a `substitute` ("x" `with` n)

        m1sub = buildProgram $ do
                fun <- m1
                n <- nM
                fun `substitute` ("x" `with` n)
        m2sub = buildProgram $ do
                n <- nM
                arg <- m2
                arg `substitute` ("x" `with` n)

prop_substitute_lambda_same_variable :: ProgramT Identity ProgramNode -> ProgramT Identity ProgramNode -> Bool
prop_substitute_lambda_same_variable m1 nM = unsub == sub
    where
        unsub = buildProgram $ lambda "x" =<< m1
        sub = buildProgram $ do
            l <- lambda "x" =<< m1
            n <- nM
            l `substitute` ("x" `with` n)

prop_substitute_lambda_different_variable :: ProgramT Identity ProgramNode -> ProgramT Identity ProgramNode -> Bool
prop_substitute_lambda_different_variable m1M nM = lhs == rhs
    where
        lhs = buildProgram $ do
            l <- lambda "y" =<< m1M
            n <- nM
            l `substitute` ("x" `with` n)
        rhs = buildProgram $ do
            m1 <- m1M
            n <- nM
            m1sub <- m1 `substitute` ("x" `with` n)
            lambda "y" m1sub

main :: IO ()
main = hspec $ do
    spec_variable
    spec_lambda
    spec_app
    spec_parent
    spec_parents
    spec_free
    spec_alphaEquivalent
    spec_substitute
    spec_Expr_Show_instance
    spec_Expr_Eq_instance
