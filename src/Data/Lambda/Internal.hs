{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances #-}
module Data.Lambda.Internal where

import Data.Graph.Inductive
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Writer
import Data.List (find)
import Data.Lambda.Parser
import Test.QuickCheck

data NodeLabel = Variable Name | Lambda Name | App | Root
    deriving (Show, Eq)
data EdgeLabel = Binding | Body | Function | Argument | Def Name
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
          (ln, Lambda _) -> return [saveAndReturn . copy program $ body program ln]
          (an, App) -> return [ saveAndReturn . copy program $ function program an
                              , saveAndReturn . copy program $ argument program an]
          _ -> return []
         


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
    show Expr { exprNode = (_, Root) } = error "Not implemented!"


showHighlighted :: (Node -> Bool) -> Expr -> String
showHighlighted p Expr { exprNode = (vn, Variable name) }
    | p vn = highlight name
    | otherwise = name
showHighlighted p Expr { exprNode = (ln, Lambda name), exprProgram = expr }
    | p ln = highlight $ str
    | otherwise = str
        where
            str = "(λ" ++ name ++ "." ++ showHighlighted p (Expr (body expr ln) expr) ++ ")"
showHighlighted p Expr { exprNode = (an, App), exprProgram = expr }
    | p an = highlight $ str
    | otherwise = str
        where
            str = "(" ++ showHighlighted p (Expr (function expr an) expr) ++ " " ++ showHighlighted p (Expr ( argument expr an) expr) ++ ")"
showHighlighted _ Expr { exprNode = (_, Root) } = error "Not implemented!"

highlight :: String -> String
highlight s = "<<" ++ s ++ ">>"


instance Eq Expr where
    (Expr n1 p1) == (Expr n2 p2) = (pathifier n1 p1) == (pathifier n2 p2)
        where
            pathifier (_, Variable name) _ = Variable name : []
            pathifier (n, Lambda name) p = Lambda name : pathifier (body p n) p
            pathifier (n, App) p = App : (pathifier (function p n) p ++ pathifier (function p n) p)
            pathifier (_, Root) _ = error "Not implemented!"


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

def :: Monad m => Name -> ProgramNode -> ProgramT m ProgramNode
def name1 target@(targetNode, _) = findRoot >>= \(root, _) -> ProgramT $ do
    program <- get
    case find nameMatcher (out program root) of
      Just (_, n, _) -> modify $ delEdge (root, n)
      Nothing -> return ()
    modify $ insEdge (root, targetNode, Def name1)
    return target
        where
            nameMatcher (_, _, Def name2) = name1 == name2
            nameMatcher _ = False

maybeRoot :: Program -> Maybe ProgramNode
maybeRoot program = case filter (\(_, t) -> t == Root) (labNodes program) of
                      [] -> Nothing
                      [r@(_, Root)] -> Just r
                      _ -> error "Invariant broken: more than one Root node!"

findRoot :: Monad m => ProgramT m ProgramNode
findRoot = get >>= return . maybeRoot >>= rootMaker
    where
        rootMaker (Just r) = return r
        rootMaker Nothing = do
            root <- newNode
            let rootNode = (root, Root)
            modify $ insNode rootNode
            return rootNode

resolve :: Program -> Name -> Maybe ProgramNode
resolve program name1 = do
    (root, _) <- maybeRoot program
    (_, n, _) <- find nameMatcher (out program root)
    return $ labNode' (context program n)
        where
            nameMatcher (_, _, Def name2) = name1 == name2
            nameMatcher _ = False

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
copy' _ (_, Root) = error "Not implemented!"

free :: Program -> [ProgramNode]
free expr = labNodes $ labnfilter labledIsFreeVariable expr
    where
        labledIsFreeVariable ln @ (n, _)
            | labledIsVariable ln = Binding `notElem` map edgeLabel (out expr n)
            | otherwise = False
        labledIsVariable (_, Variable _) = True
        labledIsVariable _ = False


free' :: Expr -> [ProgramNode]
free' (Expr { exprNode = node, exprProgram = program }) = freeWalker [] node
    where
        freeWalker binds v@(_, Variable name)
            | name `notElem` binds = [v]
            | otherwise = []
        freeWalker binds (ln, Lambda name) = freeWalker (name:binds) (body program ln)
        freeWalker binds (an, App) = (freeWalker binds (function program an)) ++ (freeWalker binds (argument program an))
        freeWalker _ (_, Root) = error "Not implemented!"

mkExpr :: Monad m => ProgramNode -> ProgramT m Expr
mkExpr node = do
    program <- get
    return $ Expr node program


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

body' :: Expr -> Expr
body' (Expr (n, _) expr) = Expr (body expr n) expr

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





parents :: Program -> Node -> [(Node, EdgeLabel)]
parents expr node = case parent expr node of
                      Just p@(parentNode, _) -> p : parents expr parentNode
                      Nothing -> []



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
substitute (_, Root) _ = error "Not implemented!"

variableNames :: [Name]
variableNames = postfixAlphas [""] ++ postfixAlphas variableNames
    where
        postfixAlphas strings = concat $ map (\str -> map (\c -> str ++ [c]) alphas) strings
        alphas = ['a'..'z']

with :: a -> b -> (a, b)
a `with` b = (a,b)


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
betaReduce (_, Root) = error "Not implemented!"

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
delete (_, Root) = error "Not implemented!"


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
etaReduce (_, Root) = error "Not implemented!"


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
measure Expr { exprNode = (_, Root) } = error "Not implemented!"


simplify :: Expr -> Expr
simplify expr = case find simpler candidates of
                  Just reduced -> simplify reduced
                  Nothing -> case exprNode expr of
                               (_, Variable _) -> expr
                               (ln, Lambda name) -> buildProgram $ do
                                   newBody <- let newBodyExpr =  simplify $ body' expr
                                               in copy' (exprProgram newBodyExpr) (exprNode newBodyExpr)
                                   modify $ delNode ln
                                   lambda name newBody
                               (_, App) -> buildProgram $ do
                                   newFun <- let newFunExpr = simplify $ function' expr
                                              in copy' (exprProgram newFunExpr) (exprNode newFunExpr)
                                   newArg <- let newArgExpr = simplify $ argument' expr
                                               in copy' (exprProgram newArgExpr) (exprNode newArgExpr)
                                   app newFun newArg
                               (_, Root) -> error "Not implemented!"

    where
        simpler candidate = measure candidate < originalComplexity
        originalComplexity = measure expr
        candidates = [tryEtaReduction, tryBetaReduction]
        tryBetaReduction = buildProgram $ saveAndReturn expr >>= betaReduce
        tryEtaReduction  = buildProgram $ saveAndReturn expr >>= etaReduce


fromAST :: AST -> Expr
fromAST = buildProgram . fromAST'

fromAST' :: Monad m => AST -> ProgramT m ProgramNode
fromAST' (V name) = variable name
fromAST' (L name bodyAST) = fromAST' bodyAST >>= lambda name
fromAST' (A funAST argAST) = do
         fun <- fromAST' funAST
         arg <- fromAST' argAST
         app fun arg
fromAST' (D name ast) = def name =<< fromAST' ast


toAST :: Expr -> AST
toAST Expr { exprNode = (_, Variable name) } = V name
toAST expr @ Expr { exprNode = (_, Lambda name) } = L name (toAST $ body' expr)
toAST expr @ Expr { exprNode = (_, App) } = A (toAST $ function' expr) (toAST $ argument' expr)
toAST Expr { exprNode = (_, Root) } = error "Not implemented!"


