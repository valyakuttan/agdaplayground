--
-- Parameters vs. Indices
--

module Sets.Parameters_vs_Indices where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_)

data _+_≡_ : ℕ → ℕ → ℕ → Set where
  znn   : ∀ {n} → zero + n ≡ n
  sns : ∀ {m n k} → m + n ≡ k → suc m + n ≡ suc k

data _≤″_ : ℕ → ℕ → Set where
  ≤+ : ∀ {m n k} → m + n ≡ k → m ≤″ k

-- is similar to

data _≤″′_ (m : ℕ) (k : ℕ) : Set where
  ≤+ : ∀ {n} → m + n ≡ k → m ≤″′ k

--
-- The parameters of the set are present as
-- implicit arguments in the constructors.
--
data  _≡_ {A : Set} (x : A) : A → Set  where
  refl : x ≡ x

infix 4 _≡_


data _∈_ {A : Set}(x : A) : List A → Set where
  first : ∀ {xs} → x ∈ x ∷ xs
  later : ∀ {y xs} → x ∈ xs → x ∈ y ∷ xs

infix 4 _∈_

--
-- compare this 
data tt (A : Set) : A → Set where
    t : ∀ {a} → tt A a

-- with

data ttt {A : Set} : A → Set where
    t : ∀ {a} → ttt a

-- which can elegently written as 

data tttt {A : Set} (a : A) : Set where
    t : tttt a

