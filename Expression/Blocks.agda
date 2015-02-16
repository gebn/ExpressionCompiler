module Expression.Blocks where

open import Data.Bool
open import Data.Nat
open import Data.String

{- The recursive type of arithmetic expressions. -}
data Exp : (A : Set) → Set where
  B   : Bool → Exp Bool                           -- boolean (used for conditions)
  N   : ℕ → Exp ℕ                                 -- natural number (linked to Val)
  V   : String → Exp ℕ                            -- variable (linked to Var)
  _⊕_ : Exp ℕ → Exp ℕ → Exp ℕ                     -- addition (linked to Add)
  if_then_else : Exp Bool → Exp ℕ → Exp ℕ → Exp ℕ -- if/else flow control statement
infixl 5 _⊕_
