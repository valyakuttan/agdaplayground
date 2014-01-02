-- BinTree.agda

module BinTree where

data BinTree : Set where
    leaf : BinTree
    node : BinTree → BinTree → BinTree
