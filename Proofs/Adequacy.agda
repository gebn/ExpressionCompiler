module Proofs.Adequacy where

open import Data.Bool renaming (Bool to 𝔹)
open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.String
open import Relation.Binary.PropositionalEquality hiding ([_])

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

-- booleans
adeq .𝔹 (B x) p σ n () -- nothing ≡ just n is false

-- naturals
adeq .ℕ (N .n) p σ n refl = suc zero , refl          -- just (n :: []) is trivially equal to just [ n ]

-- variables
adeq .ℕ (V x) p σ n eq = {!!}

-- addition
adeq .ℕ (e ⊕ e₁) p σ n eq = {!!}

-- subtraction
adeq .ℕ (e ⊝ e₁) p σ n eq = {!!}

-- if/else
adeq .ℕ (if_then_else e e₁ e₂) p σ n eq = {!!}


V-lemma : (σ : State) (x : String ) → 
      σ x ≡ nothing → (⟨⟨ Var x ∷ [] ⟩⟩ [] , σ , suc 0) ≡ nothing
V-lemma σ x p rewrite p = refl
{-
Identical to adeq above, except that if the result of evaluation is nothing, there
exists a number of execution steps after which the result will also be nothing.
-}
adeq-fail : (T : Set) (e : Exp T) (p : Program) (σ : State) (n : ℕ) →
        ⟦ e ⟧ σ ≡ nothing → (∃ λ k → ⟨⟨ compile e ⟩⟩ [] , σ , k ≡ nothing)

-- booleans
adeq-fail .𝔹 (B x) p σ n refl = suc n , refl -- nothing ≡ nothing is trivially correct

-- naturals
adeq-fail .ℕ (N x) p σ n () -- just x ≡ nothing is false

-- variables
adeq-fail .ℕ (V x) p σ n eq = suc 0 , V-lemma σ x eq

-- addition
adeq-fail .ℕ (e ⊕ e₁) p σ n eq = {!!}

-- subtraction
adeq-fail .ℕ (e ⊝ e₁) p σ n eq = {!!}

-- if/else
adeq-fail .ℕ (if_then_else e e₁ e₂) p σ n eq = {!!}
