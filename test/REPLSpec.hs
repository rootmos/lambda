module REPLSpec (spec) where

import Control.Monad.State
import Data.Lambda
import Data.Lambda.REPL
import Test.Hspec

spec_doREPL :: SpecWith ()
spec_doREPL = describe "doREPL" $ do
    it "should parse (\\x.y) and output the same" $ do
        output <- flip evalStateT empty $ doREPL "(\\x.y)"
        output `shouldBe` Just "(λx.y)"
    it "should be able to define foo := x and retrieve it with :d foo" $ do
        output <- flip evalStateT empty $ doREPL "foo := x" >> doREPL ":d foo"
        output `shouldBe` Just "x"
    it "should be able to define foo := (x y) and retrieve it with :d foo" $ do
        output <- flip evalStateT empty $ doREPL "foo := (x y)" >> doREPL ":d foo"
        output `shouldBe` Just "(x y)"
    it "should complain when trying to find undefined expression" $ do
        output <- flip evalStateT empty $ doREPL ":d bar"
        output `shouldBe` Just "bar is not defined"
    it "should be able to define foo := x and retrieve it at a later time" $ do
        output <- flip evalStateT empty $ do
            _ <- doREPL "foo := x"
            _ <- doREPL "y"
            _ <- doREPL ":d foo"
            doREPL ":d foo"
        output `shouldBe` Just "x"
    it ":p should print the current program" $ do
        output <- flip evalStateT empty $ do
            _ <- doREPL "foo := x"
            doREPL ":p"
        output `shouldBe` Just "foo := x"
    it "should return Nothing when nothing is inputed" $ do
        output <- flip evalStateT empty $ doREPL ""
        output `shouldBe` Nothing

    describe "basic programs" $ do
        it "(id x) should return x" $ do
            output <- flip evalStateT baseProgram $ doREPL "(id x)"
            output `shouldBe` Just "x"
        it "(true 1 2) should return 1" $ do
            output <- flip evalStateT baseProgram $ doREPL "(true 1 2)"
            output `shouldBe` Just "1"
        it "(false 1 2) should return 2" $ do
            output <- flip evalStateT baseProgram $ doREPL "(false 1 2)"
            output `shouldBe` Just "2"
        it "(if true 1 2) should return 1" $ do
            output <- flip evalStateT baseProgram $ doREPL "(if true 1 2)"
            output `shouldBe` Just "1"
        it "(if false 1 2) should return 1" $ do
            output <- flip evalStateT baseProgram $ doREPL "(if false 1 2)"
            output `shouldBe` Just "2"

spec :: SpecWith ()
spec = do
    spec_doREPL
