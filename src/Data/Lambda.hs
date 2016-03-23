module Data.Lambda ( Expr
                   , exprProgram
                   , Program
                   , toAST
                   , fromAST
                   , simplify
                   , resolve'
                   , empty
                   ) where

import Data.Lambda.Internal

empty :: Program
empty = emptyProgram
