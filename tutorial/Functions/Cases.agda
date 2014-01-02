--
-- Functions Defined by Cases
--

module Functions.Cases where

open import Sets.Enumerated using (Bool; true; false)

not : Bool → Bool
not true  = false
not false = true

_∧_   : Bool → Bool → Bool
true  ∧ x = x
false ∧ _ = false

infixr 6 _∧_

infixr 5 _∨_
 
_∨_   : Bool → Bool → Bool
false ∨ x = x
true  ∨ _ = true

--
-- Exercises 
--

-- Define a set named Quarter with four elements, east, west, north and south.
-- Define a function turnLeft : Quarter → Quarter.
--
-- Define the functions turnBack and turnRight with the help of
-- turnLeft! (By either pattern matching or defining a specific
-- function composition function.)
--

data Quarter : Set where
    east  : Quarter
    west  : Quarter
    north : Quarter
    south : Quarter

turnLeft : Quarter → Quarter
turnLeft east  = north
turnLeft west  = south
turnLeft north = west
turnLeft south = east

compose : {A B C : Set} → (B → C) → (A → B) → A → C
compose f g x = f (g x)

turnBack : Quarter → Quarter
turnBack q = compose turnLeft turnLeft q

turnRight : Quarter → Quarter
turnRight q = compose turnLeft turnBack q
