-- Term Inference and Implicit Arguments

module Term_Inference where

open import Data.Empty    using (⊥)
open import Data.Unit     using (⊤; tt)
open import Data.Sum      using (_⊎_; inj₁; inj₂)
open import Data.Nat      using (ℕ; zero; suc)

data Fin′ : ℕ → Set where
  zero : (n : _) → Fin′ (suc n)   -- ℕ is inferred
  suc  : (n : _) → Fin′ n → Fin′ (suc n)   -- ℕ is inferred

x : Fin′ 3
x = suc _ (zero _)   -- 2 and 1 are inferred

y : Fin′ 3
y = suc _ (suc _ (zero _)) -- 2, 1, 0 are inferred


-- Implicit arguments
--
data Fin : ℕ → Set where
  zero : {n : _} → Fin (suc n)
  suc  : {n : _} → Fin n → Fin (suc n)

y″ : Fin 3
y″ = suc {_} (zero {_})

x″ : Fin 3
x″ = suc zero


-- Variables with inferred types can be introduced by ∀:
--
data FFin′ : ℕ → Set where
  zero : ∀ n → FFin′ (suc n)
  suc  : ∀ n → FFin′ n → FFin′ (suc n)

data FFin : ℕ → Set where
  zero : ∀ {n} → FFin (suc n)
  suc  : ∀ {n} → FFin n → FFin (suc n)

z : FFin′ 3
z = suc _ (zero _)

z′ : FFin 3
z′ = suc zero
