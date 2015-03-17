module Expression.Blocks where

open import Data.Bool renaming (Bool to 𝔹)
open import Data.Nat using (ℕ)
open import Data.String using (String)

{- The recursive type of arithmetic expressions. -}
data Exp : (A : Set) → Set where
  -- primitives
  B   : 𝔹 → Exp 𝔹     -- boolean (used for conditions)
  N   : ℕ → Exp ℕ      -- natural number (linked to Val)

  V   : String → Exp ℕ -- variable (linked to Var)

  -- boolean operators
  ¬_  : Exp 𝔹 → Exp 𝔹          -- NOT
  _&_ : Exp 𝔹 → Exp 𝔹 → Exp 𝔹 -- AND
  _∥_ : Exp 𝔹 → Exp 𝔹 → Exp 𝔹 -- OR

  -- arithmetic operators
  _⊕_ : Exp ℕ → Exp ℕ → Exp ℕ                   -- addition (linked to Add)
  _⊝_ : Exp ℕ → Exp ℕ → Exp ℕ                   -- subtraction (linked to Sub)

  -- control statements
  if_then_else : Exp 𝔹 → Exp ℕ → Exp ℕ → Exp ℕ -- if/else flow control

-- fixities (higher precedence means stronger binding)
infixl 7 _&_
infixl 6 _∥_
infixl 5 _⊕_ _⊝_
