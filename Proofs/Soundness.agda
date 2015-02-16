module Proofs.Soundness where

open import Data.Bool renaming (Bool to 𝔹)
open import Data.List
open import Data.Maybe
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Expression.Compiler
open import Expression.Evaluator
open import Interpreter.Executor

{-
Proves that executing a compiled expression and evaluating that same expression
produce the same output.
More verbosely: if, at the end of compiling and executing an expression, the stack
contains a single number, the result of evaluating the raw expression using the same
state will result in the same number.
-}
sound : (T : Set) (e : Exp T) (p : Program) (n : ℕ) (σ : State) (k : ℕ) →
        ⟨⟨ compile e ⟩⟩ [] , σ , k ≡ just [ n ] → ⟦ e ⟧ σ ≡ just n

-- booleans
sound .𝔹 (B x) p n σ zero ()    -- just [] ≡ just (n ∷ []) is false
sound .𝔹 (B x) p n σ (suc k) () -- nothing ≡ just (n ∷ []) is false

-- naturals
sound .ℕ (N x) p n σ k eq = {!!}

-- variables
sound .ℕ (V x) p n σ k eq = {!!}

-- addition
sound .ℕ (e ⊕ e₁) p n σ k eq = {!!}

-- if/else
sound .ℕ (if_then_else e e₁ e₂) p n σ k eq = {!!}
