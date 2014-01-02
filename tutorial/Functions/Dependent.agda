--
-- Dependently Typed Functions
--

module Functions.Dependent where

open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s; _<_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; _,_)

-- Dependently typed function:
--
-- f : (x : A) → B, where B may depend on x

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ zero = zero  -- Note: different zeros
fromℕ (suc n) = suc (fromℕ n)

-- Exercises
--

_-_ : (n : ℕ) → Fin (suc n) → ℕ
n - zero  = n
n - suc m = {!!}

