module Data.Lambda ( Expr
                   , exprProgram
                   , Program
                   , toAST
                   , fromAST
                   , simplify
                   , resolve'
                   , empty
                   , baseProgram
                   , append
                   ) where

import Data.Lambda.Internal

empty :: Program
empty = emptyProgram
