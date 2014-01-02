-- Propositions

module Sets.Propositions where

open import Data.Nat using (ℕ; zero; suc)
open import Sets.Recursive using (ℕ⁺; one; double; double+1)

data ⊤ : Set where
    tt : ⊤

data ⊥ : Set where

data _×_ (A B : Set) : Set where
    _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_

data _⊎_ (A B : Set) : Set where
    inj₁ : A → A ⊎ B
    inj₂ : B → A ⊎ B

infixr 1 _⊎_

-- proofs for some propositions
--
⊤×⊤ : ⊤ × ⊤
⊤×⊤ = tt , tt

-- ⊤×⊥ : ⊤ × ⊥
-- ⊥×⊤ = ⊥ × ⊤

⊤⊎⊤ : ⊤ ⊎ ⊤
⊤⊎⊤ = inj₁ tt

⊤⊎⊥ : ⊤ ⊎ ⊥
⊤⊎⊥ = inj₁ tt

⊥⊎⊤ : ⊥ ⊎ ⊤
⊥⊎⊤ = inj₂ tt

-- ⊥⊎⊥ = ⊥ ⊎ ⊥

⊥⊎⊤⊎⊤×[⊥⊎⊥]⊎⊤ : ⊥ ⊎ ⊤ ⊎ ⊤ × (⊥ ⊎ ⊥) ⊎ ⊤
⊥⊎⊤⊎⊤×[⊥⊎⊥]⊎⊤ = inj₂ (inj₁ tt)

-- We wish to represent proofs of propositions n ≤ m (n, m = 0, 1, ...).
-- For this we define a set indexed with two natural numbers:
--
data _≤_ : ℕ → ℕ → Set where
    z≤n : {n : ℕ} → zero ≤ n
    s≤s : {m : ℕ} → {n : ℕ} → m ≤ n → suc m ≤ suc n

-- some proofs
--
0≤5 : 0 ≤ 5
0≤5 = z≤n

1≤2 : 1 ≤ 2
1≤2 = s≤s {0} {1} (z≤n {1})

3≤5 : 3 ≤ 5
3≤5 = s≤s (s≤s (s≤s z≤n))

7≰3 : 7 ≤ 3 → ⊥
7≰3 (s≤s (s≤s (s≤s ())))

4≰2 : 4 ≤ 2 → ⊥
4≰2 (s≤s (s≤s ()))

8≰4 : 8 ≤ 4 → ⊥
8≰4 (s≤s x) = 7≰3 x

----------------------------
-------- Exercises ---------
----------------------------

-- Define an indexed set _isDoubleOf_ : ℕ → ℕ → Set such
-- that m isDoubleOf n is non-empty iff m is the double of n!
--
--    Prove that 8 isDoubleOf 4 is non-empty!
--    Prove that 9 isDoubleOf 4 is empty!

data  _isDoubleOf_ : ℕ → ℕ → Set where
     z_ido_z : zero isDoubleOf zero
     n_ido_m : {n : ℕ} → {m : ℕ} → 
               n isDoubleOf m → suc (suc n) isDoubleOf suc m

8isDoubleOf4 : 8 isDoubleOf 4
8isDoubleOf4 = (n_ido_m (n_ido_m (n_ido_m (n_ido_m z_ido_z))))

9isDoubleOf4 : 9 isDoubleOf 4 → ⊥
9isDoubleOf4 (n_ido_m (n_ido_m (n_ido_m (n_ido_m ()))))

-- Define an indexed set Odd : ℕ → Set such that 
-- odd n is non-empty iff n is odd!
--
--    Prove that Odd 9 is non-empty!
--    Prove that Odd 8 is empty!

--data Odd : ℕ → Set where
--       one   : Odd (suc zero)
--       odd : {n : ℕ} → Odd n → Odd (suc (suc n))
--

-- Define Even : ℕ → Set and Odd : ℕ → Set mutually!
--

data Even : ℕ → Set
data Odd  : ℕ → Set

data Even where
    zero : Even zero
    even : {n : ℕ} → Odd n → Even (suc n)

data Odd where
    odd : {n : ℕ} → Even n → Odd (suc n)

Odd9 : Odd 9
Odd9 = odd (even (odd (even (odd (even (odd (even (odd zero))))))))

Odd8 : Odd 8 → ⊥
Odd8 (odd (even (odd (even (odd (even (odd (even ()))))))))

data _≤′_ : ℕ → ℕ → Set where
  ≤′-refl : ∀ {m}   →                  m ≤′ m
  ≤′-step : ∀ {m n} →  m ≤′ n  →  m ≤′ suc n

infix 4 _≤′_

-- Define equality _≡_ : ℕ → ℕ → Set!
-- Define non-equality _≠_ : ℕ → ℕ → Set!

data _≡_ : ℕ → ℕ → Set where
     zero : zero ≡ zero
     m≡n  : ∀ {m n} → m ≡ n → suc m ≡ suc n

data _≢_ : ℕ → ℕ → Set where
     z≢n : ∀ {n} → zero ≢ suc n
     n≢z : ∀ {n} → suc n ≢ zero
     m≢n : ∀ {m n} → m ≢ n → suc m ≢ suc n

5≢3 : 5 ≢ 3
5≢3 = m≢n (m≢n (m≢n n≢z))

--
-- _+_≡_: Addition predicate
--

data _+_≡_ : ℕ → ℕ → ℕ → Set where
  znn   : ∀ {n} → zero + n ≡ n
  sns : ∀ {m n k} → m + n ≡ k → suc m + n ≡ suc k

5+5=10 : 5 + 5 ≡ 10
5+5=10 = sns (sns (sns (sns (sns znn))))

2+2≠5 : 2 + 2 ≡ 5 → ⊥
2+2≠5 (sns (sns ()))

-- Define _*_≡_ : ℕ → ℕ → Set with the help of _+_≡_!
--
--    Prove that 3 * 3 ≡ 9 is non-empty!
--    Prove that 3 * 3 ≡ 8 is empty!

data _*_≡_ : ℕ → ℕ → ℕ → Set where
    znz : ∀ {n} → zero * n ≡ zero
    sns : ∀ {m n k l} → m * n ≡ k → k + n ≡ l → suc m * n ≡ l

1*3=3 : 1 * 3 ≡ 3
1*3=3 = sns znz znn

3+3=6 : 3 + 3 ≡ 6
3+3=6 = sns (sns (sns znn))

2*3=6 : 2 * 3 ≡ 6
2*3=6 = sns 1*3=3 3+3=6

6+3=9 : 6 + 3 ≡ 9
6+3=9 = sns (sns (sns 3+3=6))

3*3=9 : 3 * 3 ≡ 9
3*3=9 = sns 2*3=6 6+3=9

6+3≠8 : 6 + 3 ≡ 8 → ⊥
6+3≠8 (sns (sns (sns (sns (sns (sns ()))))))

1*2≠1 : 1 * 2 ≡ 1 → ⊥
1*2≠1 (sns znz ())

2+2≠3 : 2 + 2 ≡ 3 → ⊥
2+2≠3 (sns (sns ()))

0+3≠2 : 0 + 3 ≡ 2 → ⊥
0+3≠2 ()

1*2=2 : 1 * 2 ≡ 2
1*2=2 = sns znz znn

2*2≠3 : 2 * 2 ≡ 3 → ⊥
2*2≠3 (sns (sns znz znn) x) = 2+2≠3 x

3*3≠8 : 3 * 3 ≡ 8 → ⊥
3*3≠8 (sns (sns (sns znz znn) (sns (sns (sns znn)))) x) = 6+3≠8 x

data _||_ : ℕ → ℕ → Set where
    zn : ∀ {n} → n || zero
    mn : ∀ {m n k} → m * k ≡ n → m || n
    as : ∀ {m n k} → m || k → k || n → m || n

2||6 : 2 || 6
2||6 = mn 2*3=6

1||2 : 1 || 2
1||2 = mn 1*2=2

1||6 : 1 || 6
1||6 = as 1||2 2||6

data _≈_ : ℕ → ℕ⁺ → Set where
    zz   : zero ≈ one
    even : ∀ {m n k} → suc m + suc m ≡ n → m ≈ k → n ≈ double+1 k
    odd  : ∀ {m n k} → m     + suc m ≡ n → m ≈ k → n ≈ double k

1≈1' : 1 ≈ double one
1≈1' = odd znn zz

2≈2' : 2 ≈ double+1 one
2≈2' = even (sns znn) zz

3≈3' : 3 ≈ double (double one)
3≈3' = odd (sns znn) 1≈1'

4≈4' : 4 ≈ double+1 (double one)
4≈4' = even (sns (sns znn)) 1≈1'

5≈5' : 5 ≈ double (double+1 one)
5≈5' = odd  (sns (sns znn)) 2≈2'

0≉1' : 0 ≈ double one → ⊥
0≉1' (odd () zz)

1≉2' : 1 ≈ double+1 one → ⊥
1≉2' (even (sns ()) zz)

2≉3' : 2 ≈ double (double one) → ⊥
2≉3' (odd (sns ()) (odd znn zz))

3≉4' : 3 ≈ double+1 (double one) → ⊥
3≉4' (even (sns (sns ())) (odd znn zz))

4≉5' : 4 ≈ double (double+1 one) → ⊥
4≉5' (odd (sns (sns ())) (even (sns znn) zz))

