module Interpreter.Executor where

open import Data.List
open import Data.Maybe
open import Data.Nat
open import Interpreter.Runtime public

{- Executes a Program, returning the final State of its Stack, or nothing if an error occurred. -}
⟨⟨_⟩⟩_,_,_ : Program → Stack → State → ℕ → Maybe Stack

aux : Program → Stack → State → ℕ → Maybe ℕ → Maybe Stack

-- if there are no (more) instructions to execute, return the Stack
⟨⟨ [] ⟩⟩ s , _ , _ = just s

-- if the counter has reached zero, ignore any further instructions and return the Stack
⟨⟨ _ ⟩⟩ s , _ , zero = just s

-- if we're given a constant, just push it onto the Stack and decrement the counter
⟨⟨ Val x ∷ p ⟩⟩ s , σ , suc k = ⟨⟨ p ⟩⟩ (x ∷ s) , σ , k

-- if we're provided with a variable, retrieve its value from the State using aux
⟨⟨ Var x ∷ p ⟩⟩ s , σ , suc k = aux p s σ (suc k) (σ x)

-- addition sums the first two elements in the Stack, and pushes the result back onto the Stack
⟨⟨ Add ∷ p ⟩⟩ (m ∷ n ∷ s) , σ , suc k = ⟨⟨ p ⟩⟩ (m + n ∷ s) , σ , k

-- subtraction reduces the head of the Stack by the second element, and pushes back the result
⟨⟨ Sub ∷ p ⟩⟩ (m ∷ n ∷ s) , σ , suc k = ⟨⟨ p ⟩⟩ (m ∸ n ∷ s) , σ , k

-- jump on zero and the head of the Stack is zero, so skip forward n instructions
⟨⟨ Joz n ∷ p ⟩⟩ (zero ∷ s) , σ , suc k = ⟨⟨ drop n p ⟩⟩ s , σ , k

-- jump on zero, but the head of the Stack is not zero, so just ignore the instruction and continue
⟨⟨ Joz _ ∷ p ⟩⟩ (suc _ ∷ s) , σ , suc k = ⟨⟨ p ⟩⟩ s , σ , k

-- any other scenario is an error (e.g. an empty Stack when asked to do addition)
⟨⟨ _ ⟩⟩ _ , _ , _ = nothing

-- given a Maybe ℕ add it to the Stack or nothing
aux p s σ k (just v) = ⟨⟨ p ⟩⟩ (v ∷ s) , σ , k
aux p s σ k nothing = nothing
