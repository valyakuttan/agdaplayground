-- Binary tree with finite number of children

module BinTreeFinite where
open import Sets.Enumerated using (Bool; true; false)
open import Syntax.Decimal_Naturals using (ℕ; zero; suc)

data BinTree : Set
data Node : Set

data BinTree where
    leaf : BinTree
    _+_  : ℕ → Node → BinTree

data Node where
    _+_ : BinTree → BinTree → Node
