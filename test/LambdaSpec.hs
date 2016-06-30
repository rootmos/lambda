module LambdaSpec (spec) where

import Data.Graph.Inductive
import Control.Monad.Identity
import Control.Monad.State
import Data.Lambda.Internal
import Data.Lambda.Parser
import Test.Hspec hiding (context)
import Test.QuickCheck

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
    it "shows x y z correctly" $ do
        p <- buildProgramT $ do
            fun <- do
                fun <- variable "x"
                arg <- variable "y"
                app fun arg
            arg <- variable "z"
            app fun arg
        show p `shouldBe` "(x y z)"
    it "shows x y z u correctly" $ do
        p <- buildProgramT $ do
            fun <- do
                fun <- do
                   fun <- variable "x"
                   arg <- variable "y"
                   app fun arg
                arg <- variable "z"
                app fun arg
            arg <- variable "u"
            app fun arg
        show p `shouldBe` "(x y z u)"

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

spec_Program_Show_instance :: SpecWith ()
spec_Program_Show_instance = describe "Program's show instance" $ do
    it "should print \"program is empty\" for the empty program" $ do
        show (empty :: Program) `shouldBe` "program is empty"
    it "should print all defined expressions in a simple non-empty program" $ do
        let program = exprProgram . buildProgram $ def "foo" =<< variable "x"
        show program `shouldBe` "foo := x"
    it "should print all defined expressions in a more complex non-empty program" $ do
        let program = exprProgram . buildProgram $ do
             _ <- def "foo" =<< lambda "y" =<< variable "x"
             def "bar" =<< variable "z"
        show program `shouldBe` "foo := (λy.x)\nbar := z"

spec_variable :: SpecWith ()
spec_variable = describe "variable" $ do
    it "should create a lone node" $ runProgramT $ do
        (n, Variable "x") <- variable "x"
        expr <- get
        lift $ out expr n `shouldBe` []
        lift $ inn expr n `shouldBe` []


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


spec_app :: SpecWith ()
spec_app = describe "app" $ do
    it "should connect the function and argument in: x y" $ runProgramT $ do
        x@(xn, Variable _) <- variable "x"
        y@(yn, Variable _) <- variable "y"
        (a, App) <- app x y
        expr <- get
        lift $ out expr a `shouldBe` [(a, xn, Function), (a, yn, Argument)]
        lift $ inn expr a `shouldBe` []


spec_def :: SpecWith ()
spec_def = describe "def" $ do
    it "should add a Root node and a Def edge" $ runProgramT $ do
        x@(xn, _) <- variable "x"
        result <- def "foo" x
        lift $ result `shouldBe` x

        program <- get
        let (root, Root) = head $ filter (\(_, t) -> t == Root) (labNodes program)
        lift $ out program root `shouldBe` [(root, xn, Def "foo")]
    it "should be able to define more than one thing" $ runProgramT $ do
        (xn, _) <- def "foo" =<< variable "x"
        (yn, _) <- def "bar" =<< variable "y"

        program <- get
        let Just (root, Root) = maybeRoot program
        lift $ out program root `shouldMatchList` [(root, xn, Def "foo"), (root, yn, Def "bar")]

spec_resolve :: SpecWith ()
spec_resolve = describe "reslove" $ do
    it "should fail to resolve when nothing has been defined" $ do
        expr <- buildProgramT $ variable "x"
        (resolve (exprProgram expr) "foo") `shouldBe` Nothing
    it "should fail to resolve when the wrong thing has been defined" $ do
        expr <- buildProgramT $ def "foo" =<< variable "x"
        (resolve (exprProgram expr) "bar") `shouldBe` Nothing
    it "should resolve a previously defined expression" $ do
        expr <- buildProgramT $ def "foo" =<< variable "x"
        (resolve (exprProgram expr) "foo") `shouldBe` Just (exprNode expr)
    it "should resolve to the latest defined expression" $ do
        expr <- buildProgramT $ do
            _ <- def "foo" =<< variable "y"
            def "foo" =<< variable "x"
        (resolve (exprProgram expr) "foo") `shouldBe` Just (exprNode expr)
    it "should resolve numbers to Church numerals" $ property $ prop_resolve_numerals
        where
            prop_resolve_numerals (NonNegative n) = (Just . buildProgram $ churchNumeral n) == (resolve' emptyProgram $ show n)

spec_resolveAll :: SpecWith ()
spec_resolveAll = describe "resolveAll" $ do
    it "should resolve a free variable with a defined one" $ do
        expr <- buildProgramT $ (def "foo" =<< variable "x") >> variable "foo"
        expected <- buildProgramT $ (def "foo" =<< variable "x") >> variable "x"
        (resolveAll (exprProgram expr) expr) `shouldBe` expected

spec_isEquivalentToDefinition :: SpecWith ()
spec_isEquivalentToDefinition = describe "isEquivalentToDefinition" $ do
    it "should find defined expression if equivalent" $ do
        expr <- buildProgramT $ def "foo" =<< lambda "x" =<< variable "x"
        x <- buildProgramT $ lambda "y" =<< variable "y"
        (isEquivalentToDefinition (exprProgram expr) x) `shouldBe` Just "foo"
    it "should find nothing for non-defined expressions" $ do
        expr <- buildProgramT $ def "foo" =<< lambda "x" =<< variable "x"
        x <- buildProgramT $ lambda "y" =<< variable "z"
        (isEquivalentToDefinition (exprProgram expr) x) `shouldBe` Nothing

spec_definedAs :: SpecWith ()
spec_definedAs = describe "definedAs" $ do
    it "should find name of defined node" $ do
        expr <- buildProgramT $ def "foo" =<< variable "x"
        (definedAs (exprProgram expr) (exprNode expr)) `shouldBe` Just "foo"
    it "should not find name of un-defined node" $ do
        expr <- buildProgramT $ variable "x"
        (definedAs (exprProgram expr) (exprNode expr)) `shouldBe` Nothing
    it "should not find name of un-defined node (even when there are other defined nodes)" $ do
        expr <- buildProgramT $ do
            _ <- def "foo" =<< variable "x"
            variable "y"
        (definedAs (exprProgram expr) (exprNode expr)) `shouldBe` Nothing

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

spec_append :: SpecWith ()
spec_append = describe "append" $ do
    it "should ignore an un-defined expression" $ do
        let got = empty `append` (buildProgram $ variable "x")
        let expected = emptyProgram

        got `shouldBe` expected
        (length . nodes $ got) `shouldBe` (length . nodes $ expected)
        (length . edges $ got) `shouldBe` (length . edges $ expected)
    it "should append a defined expression to an empty program" $ do
        let expr = buildProgram $ def "foo" =<< variable "x"
        let got = empty `append` expr
        let expected = exprProgram expr

        got `shouldBe` expected
        (length . nodes $ got) `shouldBe` (length . nodes $ expected)
        (length . edges $ got) `shouldBe` (length . edges $ expected)
    it "should append into a non-empty program" $ do
        let expr1 = buildProgram $ def "foo" =<< variable "x"
        let expr2 = buildProgram $ def "bar" =<< variable "y"
        let got = (empty `append` expr1) `append` expr2
        let expected = exprProgram . buildProgram $ (def "foo" =<< variable "x") >> (def "bar" =<< variable "y")

        got `shouldBe` expected
        (length . nodes $ got) `shouldBe` (length . nodes $ expected)
        (length . edges $ got) `shouldBe` (length . edges $ expected)

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

spec_simplify :: SpecWith ()
spec_simplify = describe "simplify" $ do
    it "should remain the same: λx.y" $ do
        original <- buildProgramT $ lambda "x" =<< variable "y"
        let simplified = simplify original
        original `shouldBe` simplified
        (length . nodes $ exprProgram original) `shouldBe` (length . nodes $ exprProgram simplified)
        (length . edges $ exprProgram original) `shouldBe` (length . edges $ exprProgram simplified)
    it "should remain the same: (x y)" $ do
        original <- buildProgramT $ do
            fun <- variable "x"
            arg <- variable "y"
            app fun arg
        let simplified = simplify original
        original `shouldBe` simplified
        (length . nodes $ exprProgram original) `shouldBe` (length . nodes $ exprProgram simplified)
        (length . edges $ exprProgram original) `shouldBe` (length . edges $ exprProgram simplified)
    it "should beta reduce when it can: ((λx.x) y) to y" $ do
        got <- liftM simplify . buildProgramT $ do
            fun <- lambda "x" =<< variable "x"
            arg <- variable "y"
            app fun arg
        expected <- buildProgramT $ variable "y"
        got `shouldBe` expected
        (length . nodes $ exprProgram got) `shouldBe` (length . nodes $ exprProgram expected)
        (length . edges $ exprProgram got) `shouldBe` (length . edges $ exprProgram expected)
    it "should eta reduce when it can: λx.(y x) to y" $ do
        got <- liftM simplify . buildProgramT $ lambda "x" =<< do
            fun <- variable "y"
            arg <- variable "x"
            app fun arg
        expected <- buildProgramT $ variable "y"
        got `shouldBe` expected
        (length . nodes $ exprProgram got) `shouldBe` (length . nodes $ exprProgram expected)
        (length . edges $ exprProgram got) `shouldBe` (length . edges $ exprProgram expected)
    it "should do first beta reduction and then eta reduction: ((λx.x) (λx.(y x))) to y" $ do
        got <- liftM simplify . buildProgramT $ do
            fun1 <- lambda "x" =<< variable "x"
            arg1 <- lambda "x" =<< do
                fun2 <- variable "y"
                arg2 <- variable "x"
                app fun2 arg2
            app fun1 arg1
        expected <- buildProgramT $ variable "y"
        got `shouldBe` expected
        (length . nodes $ exprProgram got) `shouldBe` (length . nodes $ exprProgram expected)
        (length . edges $ exprProgram got) `shouldBe` (length . edges $ exprProgram expected)
    it "should do first eta reduction and then beta reduction: λx.(((λx.x) y) x) to y" $ do
        got <- liftM simplify . buildProgramT $ lambda "x" =<< do
            fun <- do
                fun <- lambda "x" =<< variable "x"
                arg <- variable "y"
                app fun arg
            arg <- variable "x"
            app fun arg
        expected <- buildProgramT $ variable "y"
        got `shouldBe` expected
        (length . nodes $ exprProgram got) `shouldBe` (length . nodes $ exprProgram expected)
        (length . edges $ exprProgram got) `shouldBe` (length . edges $ exprProgram expected)

    -- https://en.wikipedia.org/wiki/Normalization_property_(abstract_rewriting)#Untyped_lambda_calculus
    it "should not apply beta reduce when it becomes more complex: ((λx.(x x) x) (λx.(x x) x)) should not be simplified" $ do
        complexExpression <- buildProgramT $ do
            let innerExpressionM = lambda "x" =<< do
                fun1 <- do
                    fun2 <- variable "x"
                    arg2 <- variable "x"
                    app fun2 arg2
                arg1 <- variable "x"
                app fun1 arg1

            innerExpression1 <- innerExpressionM
            innerExpression2 <- innerExpressionM
            app innerExpression1 innerExpression2

        simplify complexExpression `shouldBe` complexExpression

    it "should recurse when not possible to simplify top-level expression: λz.((λx.x) y) to λz.y" $ do
        got <- liftM simplify . buildProgramT $ lambda "z" =<< do
            fun <- lambda "x" =<< variable "x"
            arg <- variable "y"
            app fun arg
        expected <- buildProgramT $ lambda "z" =<< variable "y"
        got `shouldBe` expected
        (length . nodes $ exprProgram got) `shouldBe` (length . nodes $ exprProgram expected)
        (length . edges $ exprProgram got) `shouldBe` (length . edges $ exprProgram expected)
    it "should recurse when not possible to simplify top-level expression: (((λx.x) y) x) to (y x)" $ do
        got <- liftM simplify . buildProgramT $ do
            fun1 <- do
                fun2 <- lambda "x" =<< variable "x"
                arg2 <- variable "y"
                app fun2 arg2
            arg1 <- variable "x"
            app fun1 arg1
        expected <- buildProgramT $ do
            fun <- variable "y"
            arg <- variable "x"
            app fun arg
        got `shouldBe` expected
        (length . nodes $ exprProgram got) `shouldBe` (length . nodes $ exprProgram expected)
        (length . edges $ exprProgram got) `shouldBe` (length . edges $ exprProgram expected)
    it "should not break definitions: foo := (x y) should remain the same" $ do
        original <- buildProgramT $ def "foo" =<< do
            fun <- variable "x"
            arg <- variable "y"
            app fun arg
        let simplified = simplify original
        original `shouldBe` simplified
        (length . nodes $ exprProgram original) `shouldBe` (length . nodes $ exprProgram simplified)
        (length . edges $ exprProgram original) `shouldBe` (length . edges $ exprProgram simplified)
    it "should not break definitions: foo := (λx.y) should remain the same" $ do
        original <- buildProgramT $ def "foo" =<< lambda "x" =<< variable "y"
        let simplified = simplify original
        original `shouldBe` simplified
        (length . nodes $ exprProgram original) `shouldBe` (length . nodes $ exprProgram simplified)
        (length . edges $ exprProgram original) `shouldBe` (length . edges $ exprProgram simplified)

spec_fromAST :: SpecWith ()
spec_fromAST = describe "fromAST" $ do
    it "should convert V x" $ do
        fromAST (V "x") `shouldBe` buildProgram (variable "x")
    it "should convert L x (V x)" $ do
        fromAST (L "x" (V "x")) `shouldBe` buildProgram (lambda "x" =<< variable "x")
    it "should convert L x (V y)" $ do
        fromAST (L "x" (V "y")) `shouldBe` buildProgram (lambda "x" =<< variable "y")
    it "should convert (A (V x) (V y))" $ do
        fromAST (A (V "x") (V "y")) `shouldBe` (buildProgram $ do
                x <- variable "x"
                y <- variable "y"
                app x y)
    it "should convert (D foo (V x))" $ do
        fromAST (D "foo" (V "x")) `shouldBe` buildProgram (def "foo" =<< variable "x")
    it "should convert (D foo (A (V x) (V y)))" $ do
        fromAST (D "foo" (A (V "x") (V "y"))) `shouldBe` (buildProgram $ def "foo" =<< do
            x <- variable "x"
            y <- variable "y"
            app x y)

spec_toAST :: SpecWith ()
spec_toAST = describe "toAST" $ do
    it "should satisify fromAST . toAST = id" $ property $
        \e -> (fromAST . toAST $ e) == e

prop_shown_expression_is_parseable :: ProgramT Identity ProgramNode -> Bool
prop_shown_expression_is_parseable exprM = original == got
    where
        original = buildProgram exprM
        got = fromAST . fromRight . parseLambda . show $ original

        fromRight (Right x) = x
        fromRight _ = error "Oh noes!"


spec :: SpecWith ()
spec = do
    spec_variable
    spec_lambda
    spec_app
    spec_def
    spec_resolve
    spec_resolveAll
    spec_isEquivalentToDefinition 
    spec_definedAs
    spec_parent
    spec_parents
    spec_append
    spec_free
    spec_free'
    spec_alphaEquivalent
    spec_substitute
    spec_Expr_Show_instance
    spec_Expr_Eq_instance
    spec_Program_Show_instance
    spec_copy
    spec_betaReduce
    spec_etaReduce
    spec_measure
    spec_simplify
    spec_fromAST
    spec_toAST
    describe "a shown expression should be parseable" $ do
       it "shows and parses the thing" $ property prop_shown_expression_is_parseable
