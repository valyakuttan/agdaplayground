--
-- Recursive Functions
--

module Functions.Recursive where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; suc; zero)

open import Sets.Recursive using (ℕ⁺; one; double;
                                  double+1; ℕ₂; zero; id)
_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

infixl 6 _+_

_-_ : ℕ → ℕ → ℕ
zero - _ = zero
n - zero = n
n - suc m = suc (n - m)


_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = (m * n) + n

infixl 7 _*_

fib : ℕ → ℕ
fib 0 = 0
fib 1 = 1
fib (suc (suc n)) = fib (suc n) + fib n

--
-- Exercises: pred, _*_, _⊔_, _⊓_ and ⌊_/2⌋
--
-- Define the following functions:

pred  : ℕ → ℕ      -- predecessor (pred 0 = 0)
pred 0       = 0
pred (suc m) = m

infixl 6 _∸_
_∸_   : ℕ → ℕ → ℕ  -- subtraction (0 ∸ n = n)
0 ∸ n = n
suc m ∸ n = suc (m ∸ n)


infixl 6 _⊔_
_⊔_   : ℕ → ℕ → ℕ  -- maximum
0 ⊔ n         = n
n ⊔ 0         = n
suc n ⊔ suc m = suc (n ⊔ m)

infixl 7 _⊓_
_⊓_   : ℕ → ℕ → ℕ  -- minimum
0 ⊓ n = 0
n ⊓ 0 = 0
suc n ⊓ suc m = suc (n ⊓ m)


⌊_/2⌋ : ℕ → ℕ      -- half (⌊ 1 /2⌋ = 0)
⌊ 0 /2⌋ = 0
⌊ 1 /2⌋ = 0
⌊ (suc (suc m)) /2⌋ = suc (⌊ m /2⌋)

not : Bool → Bool
not true = false
not false = true

odd   : ℕ → Bool   -- is odd
odd zero = false
odd (suc n) = not (odd n)

even  : ℕ → Bool   -- is even
even n = not (odd n)

_≡?_  : ℕ → ℕ → Bool  -- is equal
0 ≡? 0         = true
0 ≡? _         = false
_ ≡? 0         = false
suc m ≡? suc n = m ≡? n

_≤?_  : ℕ → ℕ → Bool  -- is less than or equa
0 ≤? _         = true
m ≤? 0         = false
suc m ≤? suc n = m ≤? n

from : ℕ₂ → ℕ
from zero = zero
from (id one) = 1
from (id (double x)) = 2 * from (id x)
from (id (double+1 x)) = 2 * from (id x) + 1

data BinTree : Set where
  leaf : BinTree
  node : BinTree → BinTree → BinTree

mirror : BinTree → BinTree
mirror leaf = leaf
mirror (node t₁ t₂) = node (mirror t₁) (mirror t₂)

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)
