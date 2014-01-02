-- Parametric Sets

module Sets.Parametric where

open import Data.Nat
open import Sets.Enumerated

data List (A : Set) : Set where
    []   : List A
    _::_ : A → List A -> List A

infixr 5 _::_

data _×_ (A B : Set) : Set where
    _,_ : A → B -> A × B

infixr 4 _,_
infixr 2 _×_

data _⊎_ (A B : Set) : Set where
    inj₁ : A → A ⊎ B
    inj₂ : B → A ⊎ B

infixr 1 _⊎_
