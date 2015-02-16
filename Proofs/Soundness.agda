module Proofs.Soundness where

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
sound = {!!}
