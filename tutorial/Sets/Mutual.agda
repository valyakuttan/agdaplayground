-- Mutually Recursive Sets

module Sets.Mutual where

open import Sets.Enumerated using (Bool; true; false)
open import Syntax.Decimal_Naturals using (ℕ; zero; suc)

data L : Set
data M : Set

data L where
    nil  : L
    _::_ : ℕ → M → L

data M where
   _::_ : Bool → L → M

m0 : M
m0 = false :: nil

l1 : L
l1 = 1 :: m0

m1 : M
m1 = true :: l1

l2 : L
l2 = 2 :: m1

m2 : M
m2 = true :: l2

l3 : L
l3 = 3 :: m2
