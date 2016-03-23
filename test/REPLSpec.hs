module REPLSpec (spec) where

import Control.Monad.State
import Data.Lambda
import Data.Lambda.REPL
import Test.Hspec

spec_doREPL :: SpecWith ()
spec_doREPL = describe "doREPL" $ do
    it "should parse (\\x.y) and output the same" $ do
        output <- flip evalStateT empty $ doREPL "(\\x.y)"
        output `shouldBe` "(λx.y)"
    it "should be able to define foo := x and retrieve it with :d foo" $ do
        output <- flip evalStateT empty $ doREPL "foo := x" >> doREPL ":d foo"
        output `shouldBe` "x"
    it "should complain when trying to find undefined expression" $ do
        output <- flip evalStateT empty $ doREPL ":d bar"
        output `shouldBe` "bar is not defined"

spec :: SpecWith ()
spec = do
    spec_doREPL