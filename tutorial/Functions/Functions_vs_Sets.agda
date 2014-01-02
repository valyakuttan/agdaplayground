--
-- Functions vs. Sets
--

module Functions.Functions_vs_Sets where

open import Sets.Enumerated using (Bool; true; false)

-- Negation as a relation
--
-- Representation of negation as a relation between Bool and Bool:

data Not : Bool → Bool → Set where
  n₁ : Not true false
  n₂ : Not false true

-- This creates four new sets of which two are non-empty.
-- Not a b is non-empty iff b is the negated value of a.

-- Negation as a function
--
--consider the representation of negation as a function:

not : Bool → Bool
not true  = false
not false = true

