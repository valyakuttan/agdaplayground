--
-- Functions with Sets Result
--

module Functions.Large where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)

-- Inductive _≤_ definition
--
-- The inductive definition of _≤_:

data  _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} →               zero  ≤ n
  s≤s : ∀ {m n} →   m ≤ n  →  suc m ≤ suc n

-- Recursive _≤_ definition
--
-- The recursive definition of less-than-or-equal:

_≤′_ : ℕ → ℕ → Set
zero  ≤′ n     = ⊤
suc m ≤′ zero  = ⊥
suc m ≤′ suc n = m ≤′ n

-- Macro-like Set definitions
--
-- Macro-like functions don't pattern match on their argument:

_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m

¬ : Set → Set
¬ A = A → ⊥

Fin₀ : ℕ → Set
Fin₀ zero    = ⊥
Fin₀ (suc n) = ⊤ ⊎ Fin₀ n
