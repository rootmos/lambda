module Data.Lambda ( Expr
                   , exprProgram
                   , Program
                   , toAST
                   , fromAST
                   , simplify
                   , resolve'
                   , resolveAll
                   , empty
                   , baseProgram
                   , append
                   , isEquivalentToDefinition
                   ) where

import Data.Lambda.Internal

empty :: Program
empty = emptyProgram
