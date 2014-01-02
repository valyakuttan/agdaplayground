-- List.agda

module List where

open import Recursive using (ℕ; zero; succ)

data List : Set where
     empty : List
     cons  : ℕ → List → List

data List⁺ : Set where
    singleton : ℕ → List⁺
    cons      : ℕ → List⁺ -> List⁺
