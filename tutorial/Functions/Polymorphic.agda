--
-- Polymorphic Functions
--

module Functions.Polymorphic where

open import Data.Nat
open import Data.Unit using (⊤; tt)

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixr 5 _++_

id : {A : Set} → A → A
id a = a


map  : {A B : Set} → (A → B) → List A → List B 
map _ []       = []
map f (x ∷ xs) = f x ∷ map f xs

xs : List ℕ
xs = map id (1 ∷ [])

--
-- Define two functions which define the isomorphism
--  between List ⊤ and ℕ!
--

fromList : List ⊤ → ℕ
fromList [] = 0
fromList (x ∷ l) = suc (fromList l)

toList   : ℕ → List ⊤
toList zero = []
toList (suc n) = tt ∷ (toList n)

-- Define a Maybe set (lists with 0 or 1 elements) and head
-- and tail functions for the polymorphic List
-- type with the help of Maybe.
data Maybe(A : Set) : Set where
    none : Maybe A
    just : A → Maybe A

head : {A : Set} → List A → Maybe A
head [] = none
head (x ∷ l) = just x

tail : {A : Set} → List A → List A
tail [] = []
tail (x ∷ xs) = xs

-- Define const : {A B : Set} → A → B → A!
const : {A B : Set} → A → B → A
const a _ = a

-- Define flip : {A B C : Set} → (A → B → C) → B → A → C!
flip : {A B C : Set} → (A → B → C) → B → A → C
flip f b a = f a b
