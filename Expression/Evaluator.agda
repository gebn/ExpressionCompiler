module Expression.Evaluator where

open import Data.Maybe
open import Data.Nat

open import Expression.Blocks public
open import Interpreter.Runtime public

{- Evaluates an expression and returns the result, or nothing if an error occured. -}
⟦_⟧ : ∀ {T} → Exp T → State → Maybe ℕ

-- a literal value trivially evaluates to itself
⟦ N(v) ⟧ _ = just v

-- a variable name - look up its value in the state
⟦ V(s) ⟧ σ = σ s

-- recursively evaluate each side of the operator (N.B. states are identical)
⟦ E ⊕ E' ⟧ σ = ⟦ E ⟧ σ +' ⟦ E' ⟧ σ where

  _+'_ : Maybe ℕ → Maybe ℕ → Maybe ℕ

  -- if both sides returned a value, the result is simply the sum of them
  just m +' just n = just (m + n)

  -- otherwise halt evaluation and return an error
  _      +' _      = nothing

-- evaluate the condition
⟦ if E then E′ else E″ ⟧ σ with ⟦ E ⟧ σ

      -- zero is equivalent to false - return the evaluation of the 'else' block
...   | just zero = ⟦ E″ ⟧ σ

      -- all other non-error values evaluate to true - evaluate and return the 'if' block
...   | just _    = ⟦ E′ ⟧ σ

      -- evaluation of the condition failed - fail ourselves
...   | nothing   = nothing

-- any other scenario is an error (e.g. a boolean expression on its own)
⟦ _ ⟧ _ = nothing
