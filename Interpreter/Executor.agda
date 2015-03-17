module Interpreter.Executor where

open import Data.Bool
open import Data.List
open import Data.Maybe
open import Data.Nat

open import Util.Convert
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

-- not inverts the head of the stack
⟨⟨ Not ∷ p ⟩⟩ (n ∷ s) , σ , suc k = ⟨⟨ p ⟩⟩ (𝔹→ℕ (not (ℕ→𝔹 n)) ∷ s) , σ , k

-- and tests whether the first two elements of the stack are true-y
⟨⟨ And ∷ p ⟩⟩ (m ∷ n ∷ s) , σ , suc k = ⟨⟨ p ⟩⟩ (𝔹→ℕ ((ℕ→𝔹 m) ∧ (ℕ→𝔹 n)) ∷ s) , σ , k

-- or tests whether either of the first two elements of the stack are true-y
⟨⟨ Or  ∷ p ⟩⟩ (m ∷ n ∷ s) , σ , suc k = ⟨⟨ p ⟩⟩ (𝔹→ℕ ((ℕ→𝔹 m) ∨ (ℕ→𝔹 n)) ∷ s) , σ , k 

-- addition sums the first two elements in the Stack, and pushes the result back onto the Stack
⟨⟨ Add ∷ p ⟩⟩ (m ∷ n ∷ s) , σ , suc k = ⟨⟨ p ⟩⟩ (m + n ∷ s) , σ , k

-- subtraction reduces the head of the Stack by the second element, and pushes back the result
⟨⟨ Sub ∷ p ⟩⟩ (m ∷ n ∷ s) , σ , suc k = ⟨⟨ p ⟩⟩ (m ∸ n ∷ s) , σ , k

-- jump skips the next n instructions
⟨⟨ Jmp n ∷ p ⟩⟩ s , σ , suc k = ⟨⟨ drop n p ⟩⟩ s , σ , k

-- jump on zero and the head of the Stack is zero, so skip forward n instructions
⟨⟨ Joz n ∷ p ⟩⟩ (zero ∷ s) , σ , suc k = ⟨⟨ drop n p ⟩⟩ s , σ , k

-- jump on zero, but the head of the Stack is not zero, so just ignore the instruction and continue
⟨⟨ Joz _ ∷ p ⟩⟩ (suc _ ∷ s) , σ , suc k = ⟨⟨ p ⟩⟩ s , σ , k

-- any other scenario is an error (e.g. an empty Stack when asked to do addition)
⟨⟨ _ ⟩⟩ _ , _ , _ = nothing

-- given a Maybe ℕ add it to the Stack or nothing
aux p s σ k (just v) = ⟨⟨ p ⟩⟩ (v ∷ s) , σ , k
aux p s σ k nothing = nothing
