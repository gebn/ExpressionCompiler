module Interpreter.Executor where

open import Data.List
open import Data.Maybe
open import Data.Nat

open import Interpreter.Runtime public

{- Executes a program, returning the final state of its stack, or nothing if an error occurred. -}
⟨⟨_⟩⟩_,_,_ : Program → Stack → State → ℕ → Maybe Stack

-- if there are no (more) instructions to execute, return the stack
⟨⟨ [] ⟩⟩ s , _ , _  = just s

-- if the counter has reached zero, ignore any further instructions and return the stack
⟨⟨ _ ⟩⟩ s , _ , zero = just s

-- if we're given a constant, just push it onto the stack and decrement the counter
⟨⟨ Val x ∷ p ⟩⟩ s , σ , suc k = ⟨⟨ p ⟩⟩ (x ∷ s) , σ , k

-- if we're provided with a variable, retrieve its value from the state
⟨⟨ Var x ∷ p ⟩⟩ s , σ , suc k with σ x

      -- success - push it onto the stack in the same way as if we'd just received a Val
...   | just v  = ⟨⟨ p ⟩⟩ (v ∷ s) , σ , k

      -- error (e.g. it is undefined) - fail
...   | nothing = nothing

-- addition sums the first two elements in the stack, and pushes the result back onto the stack
⟨⟨ Add ∷ p ⟩⟩ (m ∷ n ∷ s) , σ , suc k      = ⟨⟨ p ⟩⟩ (m + n ∷ s) , σ , k

-- subtraction reduces the head of the stack by the second element, and pushes back the result
⟨⟨ Sub ∷ p ⟩⟩ (m ∷ n ∷ s) , σ , suc k      = ⟨⟨ p ⟩⟩ (m ∸ n ∷ s) , σ , k

-- jump on zero and the head of the stack is zero, so skip forward n instructions
⟨⟨ Joz n ∷ p ⟩⟩ (zero  ∷ s) , σ , suc k    = ⟨⟨ drop n p ⟩⟩ s , σ , k

-- jump on zero, but the head of the stack is not zero, so just ignore the instruction and continue
⟨⟨ Joz _ ∷ p ⟩⟩ (suc _ ∷ s) , σ , suc k    = ⟨⟨ p ⟩⟩ s , σ , k

-- any other scenario is an error (e.g. an empty stack when asked to do addition)
⟨⟨ _ ⟩⟩ _ , _ , _ = nothing
