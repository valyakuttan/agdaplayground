-- Indexed Sets

module Sets.Indexed where

open import Data.Empty    using (⊥)
open import Data.Unit     using (⊤; tt)
open import Data.Sum      using (_⊎_; inj₁; inj₂)
open import Data.Bool     using (Bool; true; false)
open import Data.Nat      using (ℕ; zero; suc)

-- Fin is a set indexed with a natural number
--  Fin n has exactly n elements.
data Fin : ℕ → Set where
  zero : (n : ℕ) → Fin (suc n)
  suc  : (n : ℕ) → Fin n → Fin (suc n)

-- Define a Bool indexed family of sets such that
-- the set indexed by false contains no elements and 
-- the set indexed by true contains one element.
data Bin : Bool → Set where
  tin : (t : ⊤) → Bin true

-- Vec A n is an n-tuple of elements of A
data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  cons : (n : ℕ) → A → Vec A n → Vec A (suc n)

-- Define a Bool indexed family of sets with two
-- parameters, A and B, such that the set indexed by false
-- contains an A element and the set indexed by true contains a B
-- element.

data X (A B : Set) : Bool → Set where
  fa : A → X A B false
  tb : B → X A B true
