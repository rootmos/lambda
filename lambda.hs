{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances #-}
module Lamda where

import Test.Hspec hiding (context)
import Test.QuickCheck
import Data.Graph.Inductive
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Writer
import Debug.Trace
import Data.List (find)

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

instance Ord Expr where
    e1 `compare` e2 = measure e1 `compare` measure e2

instance Monad m => Arbitrary (ProgramT m ProgramNode) where
    arbitrary = sized genProgram

instance {-# OVERLAPPING #-} Arbitrary (ProgramT Identity ProgramNode) where
    arbitrary = sized genProgram
    shrink programM = runProgram $ do
        node <- programM
        program <- get
        case node of
          (_, Variable _) -> return []
          (ln, Lambda _) -> return [saveAndReturn . copy program $ body program ln]
          (an, App) -> return [ saveAndReturn . copy program $ function program an
                              , saveAndReturn . copy program $ argument program an]


saveAndReturn :: Monad m => Expr -> ProgramT m ProgramNode
saveAndReturn expr = put (exprProgram expr) >> return (exprNode expr)

newtype YIsFreeProgramNode m = YIsFreeProgramNode (ProgramT m ProgramNode)

instance Show (ProgramT Identity ProgramNode) where
    show = show . buildProgram

instance Show (YIsFreeProgramNode Identity) where
    show (YIsFreeProgramNode nM) = show . buildProgram $ nM

instance Arbitrary (YIsFreeProgramNode Identity)  where
    arbitrary = suchThat myGeneratedProgram yIsFree
        where
            myGeneratedProgram = liftM YIsFreeProgramNode $ sized genProgram
            yIsFree (YIsFreeProgramNode programNodeM) = runIdentity $ runProgramT $ do
                programNode <- programNodeM
                program <- get
                let freeVariables = map (\n -> variableName program n) $ filter (\n -> isFree program n) $ bfs (fst programNode) program
                return $ "y" `notElem` freeVariables

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
            str = "(" ++ showHighlighted p (Expr (function expr an) expr) ++ " " ++ showHighlighted p (Expr ( argument expr an) expr) ++ ")"

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
    (Expr n1 p1) == (Expr n2 p2) = (pathifier n1 p1) == (pathifier n2 p2)
        where
            pathifier (_, Variable name) _ = Variable name : []
            pathifier (n, Lambda name) p = Lambda name : pathifier (body p n) p
            pathifier (n, App) p = App : (pathifier (function p n) p ++ pathifier (function p n) p)

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
    it "claims no difference between bound and free variables: λx.<<x>> is equal to x" $ do
        p1 <- buildProgramT $ do
            x <- variable "x"
            _ <- lambda "x" x
            return x
        p2 <- buildProgramT $ variable "x"
        p1 `shouldBe` p2


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


copy :: Program -> ProgramNode -> Expr
copy p pn = buildProgram $ copy' p pn

copy' :: Monad m => Program -> ProgramNode -> ProgramT m ProgramNode
copy' _ (_, Variable name) = variable name
copy' p (ln, Lambda name) = lambda name =<< copy' p (body p ln)
copy' p (an, App) = do
    fun <- copy' p (function p an)
    arg <- copy' p (argument p an)
    app fun arg

spec_copy :: SpecWith ()
spec_copy = describe "copy" $ do
    it "returns only the relevant nodes" $ do
        original <- buildProgramT $ do
            _ <- variable "unnecessary"
            lambda "x" =<< variable "x"
        expected <- buildProgramT $ lambda "x" =<< variable "x"

        let got = copy (exprProgram original) (exprNode original)

        got `shouldBe` expected
        (length . free $ exprProgram got) `shouldBe` (length . free $ exprProgram expected)
        (length . nodes $ exprProgram got) `shouldBe` (length . nodes $ exprProgram expected)
        (length . edges $ exprProgram got) `shouldBe` (length . edges $ exprProgram expected)
    it "copies x in λx.x to a free variable x" $ do
        original <- buildProgramT $ do
           x <- variable "x"
           _ <- lambda "x" x
           return x
        expected <- buildProgramT $ variable "x"

        let got = copy (exprProgram original) (exprNode original)

        got `shouldBe` expected
        (length . free $ exprProgram got) `shouldBe` (length . free $ exprProgram expected)
        (length . nodes $ exprProgram got) `shouldBe` (length . nodes $ exprProgram expected)
        (length . edges $ exprProgram got) `shouldBe` (length . edges $ exprProgram expected)
    it "copies x in x y to a variable x" $ do
        original <- buildProgramT $ do
           x <- variable "x"
           y <- variable "y"
           _ <- app x y
           return x
        expected <- buildProgramT $ variable "x"

        let got = copy (exprProgram original) (exprNode original)

        got `shouldBe` expected
        (length . free $ exprProgram got) `shouldBe` (length . free $ exprProgram expected)
        (length . nodes $ exprProgram got) `shouldBe` (length . nodes $ exprProgram expected)
        (length . edges $ exprProgram got) `shouldBe` (length . edges $ exprProgram expected)
    it "copies (x y) in λx.(x y) to (x y) where both x and y are free" $ do
        original <- buildProgramT $ do
           x <- variable "x"
           y <- variable "y"
           a <- app x y
           _ <- lambda "x" a
           return a
        expected <- buildProgramT $ do
           x <- variable "x"
           y <- variable "y"
           app x y

        let got = copy (exprProgram original) (exprNode original)

        got `shouldBe` expected
        (length . free $ exprProgram got) `shouldBe` (length . free $ exprProgram expected)
        (length . nodes $ exprProgram got) `shouldBe` (length . nodes $ exprProgram expected)
        (length . edges $ exprProgram got) `shouldBe` (length . edges $ exprProgram expected)

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

free' :: Expr -> [ProgramNode]
free' (Expr { exprNode = node, exprProgram = program }) = freeWalker [] node
    where
        freeWalker binds v@(_, Variable name)
            | name `notElem` binds = [v] 
            | otherwise = []
        freeWalker binds (ln, Lambda name) = freeWalker (name:binds) (body program ln)
        freeWalker binds (an, App) = (freeWalker binds (function program an)) ++ (freeWalker binds (argument program an))

mkExpr :: Monad m => ProgramNode -> ProgramT m Expr
mkExpr node = do
    program <- get
    return $ Expr node program

spec_free' :: SpecWith ()
spec_free' = describe "free'" $ do
    it "claims x is free in: x" $ runProgramT $ do
        x <- variable "x"
        expr <- mkExpr x
        lift $ free' expr `shouldBe` [x]
    it "claims x is free in: λx.<<x>>" $ runProgramT $ do
        x <- variable "x"
        _ <- lambda "x" x
        expr <- mkExpr x
        lift $ free' expr `shouldBe` [x]
    it "claims y is free in: λx.y" $ runProgramT $ do
        y <- variable "y"
        expr <- mkExpr =<< lambda "x" y
        lift $ free' expr `shouldBe` [y]
    it "claims nothing is free in: λx.x" $ runProgramT $ do
        expr <- mkExpr =<< lambda "x" =<< variable "x"
        lift $ free' expr `shouldBe` []
    it "claims [x, y] are free in: (x y)" $ runProgramT $ do
        x <- variable "x"
        y <- variable "y"
        expr <- mkExpr =<< app x y
        lift $ free' expr `shouldMatchList` [x, y]
    it "claims both xs are free in: λy.((x y) x)" $ runProgramT $ do
        x1 <- variable "x"
        x2 <- variable "x"
        y <- variable "y"
        fun <- app x1 y
        expr <- mkExpr =<< lambda "y" =<< app fun x2
        lift $ free' expr `shouldMatchList` [x1, x2]

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
                     _ -> error $ "Invariant violated: more than one parent"
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
    show AlphaEquivalent = "Alpha-equivalent"
    show (NotAlphaEquivalent r) = "Not alpha-equivalent because: " ++ r

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
                           (False, r) -> NotAlphaEquivalent r

alphaEquivalentWriter :: (Expr, Expr) -> Expr -> Expr -> Writer String Bool
alphaEquivalentWriter start (Expr (n1, Variable name1) program1) (Expr (n2, Variable name2) program2)
    | isFree program1 n1 && isFree program2 n2 =
       case name1 == name2 of
         True -> return True
         False -> do
             tell $ "free variables with different names are not alpha-equivalent: "
             tell $ showHighlighted (==n1) (fst start)
             tell $ " and "
             tell $ showHighlighted (==n2) (snd start)
             return False
    | isFree program1 n1 && not (isFree program2 n2) = do
        tell $ "variable is not free in second expression: "
        tell $ showHighlighted (==n2) (snd start)
        tell $ " when compared to second expression where it's free: "
        tell $ showHighlighted (==n1) (fst start)
        return False
    | not (isFree program1 n1) && isFree program2 n2 = do
        tell $ "variable is not free in first expression: "
        tell $ showHighlighted (==n1) (fst start)
        tell $ " when compared to second expression where it's free: "
        tell $ showHighlighted (==n2) (snd start)
        return False
    | bindingHeight program1 n1 == bindingHeight program2 n2 = return True
    | otherwise = do
        tell $ "variables are bound by different abstractions: "
        tell $ showHighlighted (\n -> n == n1 || n == bindingNode program1 n1) (fst start)
        tell $ " and "
        tell $ showHighlighted (\n -> n == n2 || n == bindingNode program2 n2) (snd start)
        return False

        where
            bindingHeight expr n = length $ takeWhile (\(m, _) -> m /= bindingNode expr n) $ parents expr n
            bindingNode expr n = let [(_, ln, Binding)] = out expr n in ln

alphaEquivalentWriter start (Expr (n1, Lambda _) program1) (Expr (n2, Lambda _) program2) =
    alphaEquivalentWriter start (Expr (body program1 n1) program1) (Expr (body program2 n2) program2)

alphaEquivalentWriter start (Expr (n1, App) program1) (Expr (n2, App) program2) = do
    functionPart <- alphaEquivalentWriter start (Expr (function program1 n1) program1) (Expr (function program2 n2) program2)
    case functionPart of
      False -> return functionPart
      True -> alphaEquivalentWriter start (Expr (argument program1 n1) program1) (Expr (argument program2 n2) program2)

alphaEquivalentWriter start e1 e2 = do
    tell $ "comparing expressions with different structures: "
    tell $ showHighlighted (== (fst $ exprNode e1)) (fst start)
    tell $ " and "
    tell $ showHighlighted (== (fst $ exprNode e2)) (snd start)
    return False

spec_alphaEquivalent :: SpecWith ()
spec_alphaEquivalent = describe "alphaEquivalent" $ do
    it "claims x and x are alpha-equivalent" $ do
        expr1 <- buildProgramT $ variable "x"
        expr2 <- buildProgramT $ variable "x"
        (expr1 `alphaEquivalent'` expr2) `shouldBe` AlphaEquivalent
    it "claims x and y are not alpha-equivalent" $ do
        expr1 <- buildProgramT $ variable "x"
        expr2 <- buildProgramT $ variable "y"
        (expr1 `alphaEquivalent'` expr2) `shouldNotBe` AlphaEquivalent
    it "claims λx.x and y are not alpha-equivalent" $ do
        expr1 <- buildProgramT $ lambda "x" =<< variable "x"
        expr2 <- buildProgramT $ variable "y"
        (expr1 `alphaEquivalent'` expr2) `shouldNotBe` AlphaEquivalent
    it "claims x y and z are not alpha-equivalent" $ do
        expr1 <- buildProgramT $ do
           x <- variable "x"
           y <- variable "y"
           app x y
        expr2 <- buildProgramT $ variable "z"
        (expr1 `alphaEquivalent'` expr2) `shouldNotBe` AlphaEquivalent
    it "claims x y and u v are not alpha-equivalent" $ do
        expr1 <- buildProgramT $ do
           x <- variable "x"
           y <- variable "y"
           app x y
        expr2 <- buildProgramT $ do
           u <- variable "u"
           v <- variable "v"
           app u v
        (expr1 `alphaEquivalent'` expr2) `shouldNotBe` AlphaEquivalent
    it "claims x y and x y are alpha-equivalent" $ do
        expr1 <- buildProgramT $ do
           x <- variable "x"
           y <- variable "y"
           app x y
        expr2 <- buildProgramT $ do
           u <- variable "x"
           v <- variable "y"
           app u v
        (expr1 `alphaEquivalent'` expr2) `shouldBe` AlphaEquivalent
    it "claims λx.λy.x y and λu.λu.u u are not alpha-equivalent" $ do
        expr1 <- buildProgramT $ do
           x <- variable "x"
           y <- variable "y"
           lambda "x" =<< lambda "y" =<< app x y
        expr2 <- buildProgramT $ do
           u1 <- variable "u"
           u2 <- variable "u"
           lambda "u" =<< lambda "u" =<< app u1 u2
        (expr1 `alphaEquivalent'` expr2) `shouldNotBe` AlphaEquivalent
    it "claims λx.x and λy.y are alpha-equivalent" $ do
        expr1 <- buildProgramT $ lambda "x" =<< variable "x"
        expr2 <- buildProgramT $ lambda "y" =<< variable "y"
        (expr1 `alphaEquivalent'` expr2) `shouldBe` AlphaEquivalent
    it "claims λx.y and λz.y are alpha-equivalent" $ do
        expr1 <- buildProgramT $ lambda "x" =<< variable "y"
        expr2 <- buildProgramT $ lambda "z" =<< variable "y"
        (expr1 `alphaEquivalent'` expr2) `shouldBe` AlphaEquivalent
    it "claims λx.y and λz.z are not alpha-equivalent" $ do
        expr1 <- buildProgramT $ lambda "x" =<< variable "y"
        expr2 <- buildProgramT $ lambda "z" =<< variable "z"
        (expr1 `alphaEquivalent'` expr2) `shouldNotBe` AlphaEquivalent

    -- Examples from: https://en.wikipedia.org/wiki/Lambda_calculus#.CE.B1-conversion
    it "claims λx.λx.x and λy.λx.x are alpha-equivalent" $ do
        expr1 <- buildProgramT $ lambda "x" =<< lambda "x" =<< variable "x"
        expr2 <- buildProgramT $ lambda "y" =<< lambda "x" =<< variable "x"
        (expr1 `alphaEquivalent'` expr2) `shouldBe` AlphaEquivalent
    it "claims λx.λx.x and λy.λx.y are not alpha-equivalent" $ do
        expr1 <- buildProgramT $ lambda "x" =<< lambda "x" =<< variable "x"
        expr2 <- buildProgramT $ lambda "y" =<< lambda "x" =<< variable "y"
        (expr1 `alphaEquivalent'` expr2) `shouldNotBe` AlphaEquivalent
    it "claims λx.λy.x and λy.λy.y are not alpha-equivalent" $ do
        expr1 <- buildProgramT $ lambda "x" =<< lambda "y" =<< variable "x"
        expr2 <- buildProgramT $ lambda "y" =<< lambda "y" =<< variable "y"
        (expr1 `alphaEquivalent'` expr2) `shouldNotBe` AlphaEquivalent

    it "claims λx.y x and λx.x y are not alpha-equivalent" $ do
        expr1 <- buildProgramT $ do
           x <- variable "x"
           y <- variable "y"
           lambda "x" =<< app x y
        expr2 <- buildProgramT $ do
           x <- variable "x"
           y <- variable "y"
           lambda "x" =<< app y x
        (expr1 `alphaEquivalent'` expr2) `shouldNotBe` AlphaEquivalent

    it "claims λy.λx.y x and λy.λx.x y are not alpha-equivalent" $ do
        expr1 <- buildProgramT $ do
           x <- variable "x"
           y <- variable "y"
           lambda "y" =<< lambda "x" =<< app x y
        expr2 <- buildProgramT $ do
           x <- variable "x"
           y <- variable "y"
           lambda "y" =<< lambda "x" =<< app y x
        (expr1 `alphaEquivalent'` expr2) `shouldNotBe` AlphaEquivalent





substitute :: Monad m => ProgramNode -> (Name, ProgramT m ProgramNode) -> ProgramT m ProgramNode
substitute v@(vn, Variable name1) (name2, nM)
    | name1 == name2 = do
       modify $ delNode vn
       nM
    | otherwise = return v
substitute (an, App) (name, nM) = do
    program <- get
    modify $ delNode an

    fun <- function program an `substitute` (name `with` nM)
    arg <- argument program an `substitute` (name `with` nM)
    app fun arg
substitute l@(ln, Lambda name1) (name2, nM)
    | name1 == name2 = return l
    | otherwise = do
        newBody <- get >>= \p -> body p ln `substitute` (name2 `with` nM)
        program <- get
        let freeVariables = map (\n -> variableName program n) $ filter (\n -> isFree program n) $ bfs (fst newBody) program
        let newName = case find (==name1) freeVariables of
                        Just _ -> head $ dropWhile (\name -> name `elem` freeVariables) variableNames
                        Nothing -> name1
        modify $ delNode ln
        lambda newName newBody

variableNames :: [Name]
variableNames = postfixAlphas [""] ++ postfixAlphas variableNames
    where
        postfixAlphas strings = concat $ map (\str -> map (\c -> str ++ [c]) alphas) strings
        alphas = ['a'..'z']

with :: a -> b -> (a, b)
a `with` b = (a,b)

spec_substitute :: SpecWith ()
spec_substitute = describe "substitute" $ do
    it "should satisfy x[x := n] = n" $ do
        got <- buildProgramT $ do
            x <- variable "x"
            x `substitute` ("x" `with` variable "n")
        expected <- buildProgramT $ variable "n"

        got `shouldBe` expected
        (length . nodes $ exprProgram got) `shouldBe` (length . nodes $ exprProgram expected)
        (length . edges $ exprProgram got) `shouldBe` (length . edges $ exprProgram expected)
    it "should satisfy y[x := n] = y" $ runProgramT $ do
        y <- variable "y"
        m <- y `substitute` ("x" `with` variable "n")
        lift $ m `shouldBe` y
    it "should substitute (x x)[x := n] = (n n)" $ do
        got <- buildProgramT $ do
            x1 <- variable "x"
            x2 <- variable "x"
            a <- app x1 x2
            a `substitute` ("x" `with` variable "n")
        expected <- buildProgramT $ do
            n1 <- variable "n"
            n2 <- variable "n"
            app n1 n2
        got `shouldBe` expected
        (length . nodes $ exprProgram got) `shouldBe` (length . nodes $ exprProgram expected)
        (length . edges $ exprProgram got) `shouldBe` (length . edges $ exprProgram expected)
    it "should substitute (x y)[x := n] = (n y)" $ do
        got <- buildProgramT $ do
            x <- variable "x"
            y <- variable "y"
            a <- app x y
            a `substitute` ("x" `with` variable "n")
        expected <- buildProgramT $ do
            n <- variable "n"
            y <- variable "y"
            app n y
        got `shouldBe` expected
        (length . nodes $ exprProgram got) `shouldBe` (length . nodes $ exprProgram expected)
        (length . edges $ exprProgram got) `shouldBe` (length . edges $ exprProgram expected)
    it "should substitute (a b)[x := c] = (a b)" $ do
        lhs <- buildProgramT $ do
            fun <- variable "a"
            arg <- variable "b"
            a <- app fun arg
            a `substitute` ("x" `with` variable "c")
        rhs <- buildProgramT $ do
            fun <- variable "a"
            arg <- variable "b"
            app fun arg
        lhs `shouldBe` rhs
        lhs `alphaEquivalent'` rhs `shouldBe` AlphaEquivalent
        (length . nodes $ exprProgram lhs) `shouldBe` (length . nodes $ exprProgram rhs)
        (length . edges $ exprProgram lhs) `shouldBe` (length . edges $ exprProgram rhs)
    it "should substitute (λy.x)[x := n] = λy.n" $ do
        lhs <- buildProgramT $ do
            x <- variable "x"
            l <- lambda "y" x
            l `substitute` ("x" `with` variable "n")
        rhs <- buildProgramT $ do
            n <- variable "n"
            lambda "y" n
        lhs `shouldBe` rhs
        (length . nodes $ exprProgram lhs) `shouldBe` (length . nodes $ exprProgram rhs)
        (length . edges $ exprProgram lhs) `shouldBe` (length . edges $ exprProgram rhs)
    it "should substitute (λz.x x)[x := n] alpha-equivalently (λz.n n)" $ do
        lhs <- buildProgramT $ do
            x1 <- variable "x"
            x2 <- variable "x"
            l <- lambda "z" =<< app x1 x2
            l `substitute` ("x" `with` variable "n")
        rhs <- buildProgramT $ do
            n1 <- variable "n"
            n2 <- variable "n"
            lambda "z" =<< app n1 n2
        lhs `alphaEquivalent'` rhs `shouldBe` AlphaEquivalent
        (length . nodes $ exprProgram lhs) `shouldBe` (length . nodes $ exprProgram rhs)
        (length . edges $ exprProgram lhs) `shouldBe` (length . edges $ exprProgram rhs)
    it "should make (λy.y)[x := u] alpha-equivalent with (λy.y)" $ do
        lhs <- buildProgramT $ do
            l <- lambda "y" =<< variable "y"
            l `substitute` ("x" `with` variable "u")
        rhs <- buildProgramT $ do
            lambda "y" =<< variable "y"
        lhs `alphaEquivalent'` rhs `shouldBe` AlphaEquivalent
        (length . nodes $ exprProgram lhs) `shouldBe` (length . nodes $ exprProgram rhs)
        (length . edges $ exprProgram lhs) `shouldBe` (length . edges $ exprProgram rhs)
    it "should make ((λv.v) z)[x := u] alpha-equivalent with ((λv.v) z)" $ do
        lhs <- buildProgramT $ do
            fun <- lambda "v" =<< variable "v"
            arg <- variable "z"
            a <- app fun arg

            a `substitute` ("x" `with` variable "u")
        rhs <- buildProgramT $ do
            fun <- lambda "v" =<< variable "v"
            arg <- variable "z"
            app fun arg
        lhs `alphaEquivalent'` rhs `shouldBe` AlphaEquivalent
        (length . nodes $ exprProgram lhs) `shouldBe` (length . nodes $ exprProgram rhs)
        (length . edges $ exprProgram lhs) `shouldBe` (length . edges $ exprProgram rhs)
    it "should make (u (λy.(v y)))[x := (λx.(λv.v))] alpha-equivalently with itself" $ do
        lhs <- buildProgramT $ do
            fun <- variable "u"
            arg <- lambda "y" =<< do
                v <- variable "v"
                y <- variable "y"
                app v y
            a <- app fun arg
            a `substitute` ("x" `with` (lambda "x" =<< lambda "v" =<< variable "v"))
        rhs <- buildProgramT $ do
            fun <- variable "u"
            arg <- lambda "y" =<< do
                v <- variable "v"
                y <- variable "y"
                app v y
            app fun arg
        lhs `alphaEquivalent'` rhs `shouldBe` AlphaEquivalent
        (length . nodes $ exprProgram lhs) `shouldBe` (length . nodes $ exprProgram rhs)
        (length . edges $ exprProgram lhs) `shouldBe` (length . edges $ exprProgram rhs)
    it "should make (u (λy.v))[x := u] alpha-equivalently with itself" $ do
        lhs <- buildProgramT $ do
            fun <- variable "u"
            arg <- lambda "y" =<< do
                v <- variable "v"
                y <- variable "y"
                app v y
            a <- app fun arg

            a `substitute` ("x" `with` variable "u")
        rhs <- buildProgramT $ do
            fun <- variable "u"
            arg <- lambda "y" =<< do
                v <- variable "v"
                y <- variable "y"
                app v y
            app fun arg
        lhs `alphaEquivalent'` rhs `shouldBe` AlphaEquivalent
        (length . nodes $ exprProgram lhs) `shouldBe` (length . nodes $ exprProgram rhs)
        (length . edges $ exprProgram lhs) `shouldBe` (length . edges $ exprProgram rhs)
    it "should substitute (λx.y)[y := x] alpha-equivalently to λz.x" $ do
        lhs <- buildProgramT $ do
            y <- variable "y"
            l <- lambda "x" y
            l `substitute` ("y" `with` variable "x")
        rhs <- buildProgramT $ do
            x <- variable "x"
            lambda "z" x
        lhs `alphaEquivalent'` rhs `shouldBe` AlphaEquivalent
        (length . nodes $ exprProgram lhs) `shouldBe` (length . nodes $ exprProgram rhs)
        (length . edges $ exprProgram lhs) `shouldBe` (length . edges $ exprProgram rhs)
    it "should substitute (λy.x)[x := (u (w y))] alpha-equivalently to λz.(u (w y))" $ do
        lhs <- buildProgramT $ do
            l <- lambda "y" =<< variable "x"
            let nM = do
                fun <- variable "u"
                arg <- do
                    w <- variable "w"
                    y <- variable "y"
                    app w y
                app fun arg
            l `substitute` ("x" `with` nM)
        rhs <- buildProgramT $ do
            lambda "z" =<< do
                fun <- variable "u"
                arg <- do
                    w <- variable "w"
                    y <- variable "y"
                    app w y
                app fun arg
        lhs `alphaEquivalent'` rhs `shouldBe` AlphaEquivalent
        (length . nodes $ exprProgram lhs) `shouldBe` (length . nodes $ exprProgram rhs)
        (length . edges $ exprProgram lhs) `shouldBe` (length . edges $ exprProgram rhs)

    it "should substitute (m1 m2)[x := n] = (m1[x := n] m2[x := n]), where m1,m2,n are arbitrary lambda expressions" $ property $
        prop_substitute_app
    it "should substitute λx.m[x := n] = λx.m, where m,n are arbitrary lambda expressions" $ property $
        prop_substitute_lambda_same_variable
    it "should substitute (λy.m)[x := n] = λy.(m[x := n]), where m,n are arbitrary lambda expressions such that y not in FV(n)" $ property $
        prop_substitute_lambda_different_variable


prop_substitute_app :: ProgramT Identity ProgramNode -> ProgramT Identity ProgramNode -> ProgramT Identity ProgramNode -> Bool
prop_substitute_app m1 m2 nM = (function' asub) `alphaEquivalent` m1sub && (argument' asub) `alphaEquivalent` m2sub
    where
        asub = buildProgram $ do
                fun <- m1
                arg <- m2
                a <- app fun arg
                a `substitute` ("x" `with` nM)

        m1sub = buildProgram $ do
                fun <- m1
                fun `substitute` ("x" `with` nM)
        m2sub = buildProgram $ do
                arg <- m2
                arg `substitute` ("x" `with` nM)

prop_substitute_lambda_same_variable :: ProgramT Identity ProgramNode -> ProgramT Identity ProgramNode -> Bool
prop_substitute_lambda_same_variable m1 nM = unsub == sub
    where
        unsub = buildProgram $ lambda "x" =<< m1
        sub = buildProgram $ do
            l <- lambda "x" =<< m1
            l `substitute` ("x" `with` nM)

prop_substitute_lambda_different_variable :: ProgramT Identity ProgramNode -> YIsFreeProgramNode Identity -> Bool
prop_substitute_lambda_different_variable m1M (YIsFreeProgramNode nM) = lhs `alphaEquivalent` rhs
    where
        lhs = buildProgram $ do
            l <- lambda "y" =<< m1M
            l `substitute` ("x" `with` nM)
        rhs = buildProgram $ do
            m1 <- m1M
            m1sub <- m1 `substitute` ("x" `with` nM)
            lambda "y" m1sub

betaReduce :: Monad m => ProgramNode -> ProgramT m ProgramNode
betaReduce v@(_, Variable _) = return v
betaReduce l@(_, Lambda _) = return l
betaReduce a@(an, App) = do
   program <- get
   case function program an of
     (ln, Lambda name) -> do
        let arg = (argument program an)
        result <- (body program ln) `substitute` (name `with` copy' program arg)
        delete arg
        modify $ delNode ln
        modify $ delNode an
        return result
     _ -> return a

delete :: Monad m => ProgramNode -> ProgramT m ()
delete (vn, Variable _) = modify $ delNode vn
delete (ln, Lambda _) = do
    program <- get
    delete (body program ln)
    modify $ delNode ln
delete (an, App) = do
    program <- get
    delete (function program an)
    delete (argument program an)
    modify $ delNode an

spec_betaReduce :: SpecWith ()
spec_betaReduce = describe "betaReduce" $ do
    it "should not do anything to a variable" $ do
        got <- buildProgramT $ betaReduce =<< variable "x"
        expected <- buildProgramT $ variable "x"
        got `shouldBe` expected
    it "should not do anything to a lambda" $ do
        got <- buildProgramT $ betaReduce =<< lambda "x" =<< variable "x"
        expected <- buildProgramT $ lambda "x" =<< variable "x"
        got `shouldBe` expected
    it "should not reduce (x y)" $ do
        got <- buildProgramT $ betaReduce =<< do
            fun <- variable "x"
            arg <- variable "y"
            app fun arg
        expected <- buildProgramT $ do
            fun <- variable "x"
            arg <- variable "y"
            app fun arg
        (length . nodes $ exprProgram got) `shouldBe` (length . nodes $ exprProgram expected)
        (length . edges $ exprProgram got) `shouldBe` (length . edges $ exprProgram expected)
    it "should not reduce ((x y) z)" $ do
        got <- buildProgramT $ betaReduce =<< do
            fun <- do
                fun <- variable "x"
                arg <- variable "y"
                app fun arg
            arg <- variable "z"
            app fun arg
        expected <- buildProgramT $ do
            fun <- do
                fun <- variable "x"
                arg <- variable "y"
                app fun arg
            arg <- variable "z"
            app fun arg
        (length . nodes $ exprProgram got) `shouldBe` (length . nodes $ exprProgram expected)
        (length . edges $ exprProgram got) `shouldBe` (length . edges $ exprProgram expected)
    it "should reduce ((λx.x) y) to y" $ do
        got <- buildProgramT $ betaReduce =<< do
            fun <- lambda "x" =<< variable "x"
            arg <- variable "y"
            app fun arg
        expected <- buildProgramT $ variable "y"
        got `shouldBe` expected
        (length . nodes $ exprProgram got) `shouldBe` (length . nodes $ exprProgram expected)
        (length . edges $ exprProgram got) `shouldBe` (length . edges $ exprProgram expected)
    it "should reduce ((λx.x) (λy.y)) to (λy.y)" $ do
        got <- buildProgramT $ betaReduce =<< do
            fun <- lambda "x" =<< variable "x"
            arg <- lambda "y" =<< variable "y"
            app fun arg
        expected <- buildProgramT $ lambda "y" =<< variable "y"
        got `shouldBe` expected
        (length . nodes $ exprProgram got) `shouldBe` (length . nodes $ exprProgram expected)
        (length . edges $ exprProgram got) `shouldBe` (length . edges $ exprProgram expected)
    it "should reduce ((λz.x) y) to x" $ do
        got <- buildProgramT $ betaReduce =<< do
            fun <- lambda "z" =<< variable "x"
            arg <- variable "y"
            app fun arg
        expected <- buildProgramT $ variable "x"
        got `shouldBe` expected
        (length . nodes $ exprProgram got) `shouldBe` (length . nodes $ exprProgram expected)
        (length . edges $ exprProgram got) `shouldBe` (length . edges $ exprProgram expected)
    it "should satisfy: ((λx.M) N) beta-reduces alpha-equivalently to M[x := N], where M,N are arbitrary lambda expressions" $ property $ do
        prop_beta_reduce

prop_beta_reduce :: ProgramT Identity ProgramNode -> ProgramT Identity ProgramNode -> Bool
prop_beta_reduce mM nM = lhs `alphaEquivalent` rhs && nodeCountTest && edgeCountTest
    where
        lhs = buildProgram $ betaReduce =<< do
            fun <- lambda "x" =<< mM
            arg <- nM
            app fun arg
        rhs = buildProgram $ do
            m <- mM
            m `substitute` ("x" `with` nM)
        nodeCountTest = (length . nodes $ exprProgram lhs) == (length . nodes $ exprProgram rhs)
        edgeCountTest = (length . edges $ exprProgram lhs) == (length . edges $ exprProgram rhs)

etaReduce :: Monad m => ProgramNode -> ProgramT m ProgramNode
etaReduce v@(_, Variable _) = return v
etaReduce a@(_, App) = return a
etaReduce l@(ln, Lambda name) = do
    program <- get
    case theApp program >>= checkTheArgument program >>= checkThatVariableIsFree program of
      Just (an, App) -> do
         result <- copy' program (function program an)
         delete l
         return result
      _ -> return l
    where
        theApp :: Program -> Maybe ProgramNode
        theApp p = case body p ln of
                      a@(_, App) -> Just a
                      _ -> Nothing

        checkTheArgument :: Program -> ProgramNode -> Maybe ProgramNode
        checkTheArgument p a@(an, App) = case argument p an of
                                           (_, Variable name2) -> if name == name2 then Just a
                                                                                   else Nothing
                                           _ -> Nothing
        checkTheArgument _ _ = error "Programming error!"

        checkThatVariableIsFree :: Program -> ProgramNode -> Maybe ProgramNode
        checkThatVariableIsFree p a@(an, App) =
            if name `notElem` freeVariablesInFunction then Just a
                                                      else Nothing
                where
                    freeVariablesInFunction = map (\(n, _) -> variableName p n) $ free' (Expr (function p an) p)
        checkThatVariableIsFree _ _ = error "Programming error!"

spec_etaReduce :: SpecWith ()
spec_etaReduce = describe "etaReduce" $ do
    it "should not do anything to a variable" $ do
        got <- buildProgramT $ etaReduce =<< variable "x"
        expected <- buildProgramT $ variable "x"
        got `shouldBe` expected
    it "should not do anything to an application" $ do
        got <- buildProgramT $ etaReduce =<< do
            fun <- variable "x"
            arg <- variable "y"
            app fun arg
        expected <- buildProgramT $ do
            fun <- variable "x"
            arg <- variable "y"
            app fun arg
        got `shouldBe` expected
    it "should not reduce λx.y" $ do
        got <- buildProgramT $ etaReduce =<< lambda "x" =<< variable "y"
        expected <- buildProgramT $ lambda "x" =<< variable "y"
        got `shouldBe` expected
    it "should not reduce λx.λy.z" $ do
        got <- buildProgramT $ etaReduce =<< lambda "x" =<< lambda "y" =<< variable "z"
        expected <- buildProgramT $ lambda "x" =<< lambda "y" =<< variable "z"
        got `shouldBe` expected
    it "should not reduce λx.(y z)" $ do
        got <- buildProgramT $ etaReduce =<< lambda "x" =<< do
            fun <- variable "y"
            arg <- variable "z"
            app fun arg
        expected <- buildProgramT $ lambda "x" =<< do
            fun <- variable "y"
            arg <- variable "z"
            app fun arg
        got `shouldBe` expected
    it "should not reduce λx.(x x)" $ do
        got <- buildProgramT $ etaReduce =<< lambda "x" =<< do
            fun <- variable "x"
            arg <- variable "x"
            app fun arg
        expected <- buildProgramT $ lambda "x" =<< do
            fun <- variable "x"
            arg <- variable "x"
            app fun arg
        got `shouldBe` expected
    it "should reduce λx.(y x) to y" $ do
        got <- buildProgramT $ etaReduce =<< lambda "x" =<< do
            fun <- variable "y"
            arg <- variable "x"
            app fun arg
        expected <- buildProgramT $ variable "y"
        got `shouldBe` expected
        (length . nodes $ exprProgram got) `shouldBe` (length . nodes $ exprProgram expected)
        (length . edges $ exprProgram got) `shouldBe` (length . edges $ exprProgram expected)
    it "should reduce λy.(M y) to M when M is an arbitrary lambda expression in which y is free" $ property $
        prop_eta_reduce

prop_eta_reduce :: YIsFreeProgramNode Identity -> Bool
prop_eta_reduce (YIsFreeProgramNode mM) = lhs `alphaEquivalent` rhs && nodeCountTest && edgeCountTest
    where
        lhs = buildProgram $ etaReduce =<< lambda "y" =<< do
            fun <- mM
            arg <- variable "y"
            app fun arg
        rhs = buildProgram mM
        nodeCountTest = (length . nodes $ exprProgram lhs) == (length . nodes $ exprProgram rhs)
        edgeCountTest = (length . edges $ exprProgram lhs) == (length . edges $ exprProgram rhs)

data Complexity = Complexity { complexityNodes :: Int, complexityDegreesOfFreedom :: Int }
    deriving (Eq, Ord, Show)

instance Monoid Complexity where
    mempty = Complexity 0 0
    mappend (Complexity { complexityNodes = n1, complexityDegreesOfFreedom = d1 })
            (Complexity { complexityNodes = n2, complexityDegreesOfFreedom = d2 })
            = Complexity (n1 + n2) (d1 + d2)

measure :: Expr -> Complexity
measure Expr { exprNode = (_, Variable _) } = Complexity 1 1
measure expr @ Expr { exprNode = (ln, Lambda _) } = Complexity 1 (length $ free' expr) <> measure bodyExpr
    where
        bodyExpr = expr { exprNode = body (exprProgram expr) ln }
measure expr @ Expr { exprNode = (an, App) } = Complexity 1 (length $ free' expr) <> measure funExpr <> measure argExpr
    where
        funExpr = expr { exprNode = function (exprProgram expr) an }
        argExpr = expr { exprNode = argument (exprProgram expr) an }

spec_measure :: SpecWith ()
spec_measure = describe "measure" $ do
    it "should consider x to be equally complex compared to y" $ do
        lhs <- buildProgramT $ variable "x"
        rhs <- buildProgramT $ variable "y"
        measure lhs `compare` measure rhs `shouldBe` EQ
    it "should consider λx.x to be more complex than x" $ do
        lhs <- buildProgramT $ lambda "x" =<< variable "x"
        rhs <- buildProgramT $ variable "x"
        measure lhs `compare` measure rhs `shouldBe` GT
    it "should consider (x y) to be more complex than λx.x" $ do
        lhs <- buildProgramT $ do
            x <- variable "x"
            y <- variable "y"
            app x y
        rhs <- buildProgramT $ lambda "x" =<< variable "x"
        measure lhs `compare` measure rhs `shouldBe` GT
    it "should consider λx.y to be more complex than λx.x" $ do
        lhs <- buildProgramT $ lambda "x" =<< variable "y"
        rhs <- buildProgramT $ lambda "x" =<< variable "x"
        measure lhs `compare` measure rhs `shouldBe` GT
    it "should consider (x y) to be more complex than λx.λy.z" $ do
        lhs <- buildProgramT $ do
            x <- variable "x"
            y <- variable "y"
            app x y
        rhs <- buildProgramT $ lambda "x" =<< lambda "y" =<< variable "z"
        measure lhs `compare` measure rhs `shouldBe` GT

main :: IO ()
main = hspec $ do
    spec_variable
    spec_lambda
    spec_app
    spec_parent
    spec_parents
    spec_free
    spec_free'
    spec_alphaEquivalent
    spec_substitute
    spec_Expr_Show_instance
    spec_Expr_Eq_instance
    spec_copy
    spec_betaReduce
    spec_etaReduce
    spec_measure
