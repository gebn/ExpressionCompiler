module Expression.Evaluator where

open import Data.Bool
open import Data.Nat
open import Data.Maybe

open import Util.Convert
open import Expression.Blocks public
open import Interpreter.Runtime public

{- Applies an operation to two 'maybe' operands if and only if neither are 'nothing'. -}
private ≻ : ∀ {a} {A : Set a} → Maybe A → Maybe A → (A → A → A) → Maybe A

-- both operands are just a value - apply the operation and return the result
≻ (just m) (just n) op = just (op m n)

-- one or both of the operands are nothing - return nothing
≻ _ _ _ = nothing


{- Evaluates an expression and returns the result, or nothing if an error occured. -}
⟦_⟧ : ∀ {T} → Exp T → State → Maybe ℕ

-- booleans are simply converted into their natural equivalent
⟦ B(b) ⟧ _ = just (𝔹→ℕ b)

-- a literal value trivially evaluates to itself
⟦ N(v) ⟧ _ = just v

-- a variable name - look up its value in the state
⟦ V(s) ⟧ σ = σ s


-- not requires some fiddling from and to naturals
⟦ ¬ E ⟧ σ with ⟦ E ⟧ σ
... | nothing = nothing
... | just n  = just (𝔹→ℕ (not (ℕ→𝔹 n)))

-- as does AND
⟦ E & E' ⟧ σ = ≻ (⟦ E ⟧ σ) (⟦ E' ⟧ σ) (λ m n → (𝔹→ℕ ((ℕ→𝔹 m) ∧ (ℕ→𝔹 n))))

-- and OR
⟦ E ∥ E' ⟧ σ = ≻ (⟦ E ⟧ σ) (⟦ E' ⟧ σ) (λ m n → (𝔹→ℕ ((ℕ→𝔹 m) ∨ (ℕ→𝔹 n))))


-- recursively evaluate each side of the operator and add the result it both produce a value (N.B. states are identical)
⟦ E ⊕ E' ⟧ σ = ≻ (⟦ E ⟧ σ) (⟦ E' ⟧ σ) _+_

-- same as the addition case above, only using subtraction
⟦ E ⊝ E' ⟧ σ = ≻ (⟦ E ⟧ σ) (⟦ E' ⟧ σ) _∸_


-- evaluate the condition
⟦ if E then E′ else E″ ⟧ σ with ⟦ E ⟧ σ

      -- zero is equivalent to false - return the evaluation of the 'else' block
...   | just zero = ⟦ E″ ⟧ σ

      -- all other non-error values evaluate to true - evaluate and return the 'if' block
...   | just _    = ⟦ E′ ⟧ σ

      -- evaluation of the condition failed - fail ourselves
...   | nothing   = nothing
