module CompExp where

open import Data.Nat
open import Data.Bool renaming (Bool to 𝔹; _∧_ to oldand)
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟪_⟫)
open import Data.Maybe
open import Data.String renaming (_++_ to _^_)

open import Expression.Compiler
open import Expression.Evaluator
open import Interpreter.Executor

{-
Proves that if an expression evaluates to a given value n, it can be compiled and 
executed up to a point at which the result will be equal to n.
More verbosely: if the result of evaluating an expression is n, there exists a 
number of steps k, that when the same expression is compiled and evaluated over k 
steps, will produce the result n.
-}
adeq : (T : Set) (e : Exp T) (p : Program) (σ : State) (n : ℕ) →
        ⟦ e ⟧ σ ≡ just n → (∃ λ k → ⟨⟨ compile e ⟩⟩ [] , σ , k ≡ just [ n ])
adeq = {!!}

{-
Identical to adeq above, except that if the result of evaluation is nothing, there 
exists a number of execution steps after which the result will also be nothing.
-}
adeq-fail : (T : Set) (e : Exp T) (p : Program) (σ : State) (n : ℕ) →
        ⟦ e ⟧ σ ≡ nothing → (∃ λ k → ⟨⟨ compile e ⟩⟩ [] , σ , k ≡ nothing)
adeq-fail = {!!}
