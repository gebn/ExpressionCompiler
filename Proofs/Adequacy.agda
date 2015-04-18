module Proofs.Adequacy where

open import Data.Bool renaming (Bool to 𝔹)
open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.String hiding (_++_)
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
adeq .𝔹 (B x) p σ n eq = {!!} 
adeq .𝔹 (¬ x) p σ n eq = {!!} 
adeq .𝔹 (x & y) p σ n eq = {!!} 
adeq .𝔹 (x ∥ y) p σ n eq = {!!} 

-- naturals
adeq .ℕ (N .n) p σ n refl = suc zero , refl          -- just (n :: []) is trivially equal to just [ n ]

-- variables
adeq .ℕ (V x) p σ zero eq = {!!}
adeq .ℕ (V x) p σ (suc n) eq = {!!}

-- addition
adeq .ℕ (e ⊕ e₁) p σ n eq = {!!}

-- subtraction
adeq .ℕ (e ⊝ e₁) p σ n eq = {!!}

-- if/else
adeq .ℕ (if_then_else e e₁ e₂) p σ n eq = {!!}


--Refined version of adequacy proof
adeq' : (T : Set) (s : Stack) (e : Exp T) (p : Program) (σ : State) (n : ℕ) →
        ⟦ e ⟧ σ ≡ just n → (∃ λ k → ∃ λ k' → ⟨⟨ compile e ++ p ⟩⟩ s , σ , k ≡ ⟨⟨ p ⟩⟩ (n ∷ s), σ , k')

-- booleans
adeq' .𝔹 s (B x) p σ n eq = {!!} 
adeq' .𝔹 s (¬ x) p σ n eq = {!!}
adeq' .𝔹 s (x & y) p σ n eq = {!!}
adeq' .𝔹 s (x ∥ y)  p σ n eq = {!!}

-- naturals
adeq' .ℕ s (N x) p σ .x refl = suc x , x , refl -- just x ≡ just x 

-- variables
adeq' .ℕ s (V x) p σ n eq = {!!}

-- addition
adeq' .ℕ s (e ⊕ e₁) p σ n eq = {!!}

-- subtraction
adeq' .ℕ s (e ⊝ e₁) p σ n eq = {!!}

-- if/else
adeq' .ℕ s (if_then_else e e₁ e₂) p σ n eq = {!!}


{-
The following lemma is used to prove adeq-fail for variables.

V-lemma : (σ : State) (x : String ) → 
      σ x ≡ nothing → (⟨⟨ Var x ∷ [] ⟩⟩ [] , σ , suc 0) ≡ nothing
V-lemma σ x p rewrite p = refl

But we can use the aux function instead of this.
-}

{-
Identical to adeq above, except that if the result of evaluation is nothing, there
exists a number of execution steps after which the result will also be nothing.
-}
adeq-fail : (T : Set) (e : Exp T) (p : Program) (σ : State) (n : ℕ) →
        ⟦ e ⟧ σ ≡ nothing → (∃ λ k → ⟨⟨ compile e ⟩⟩ [] , σ , k ≡ nothing)

-- booleans
adeq-fail .𝔹 (B x) p σ n eq = {!!}
adeq-fail .𝔹 (¬ x) p σ n eq = {!!}
adeq-fail .𝔹 (x & y) p σ n eq = {!!}
adeq-fail .𝔹 (x ∥ y) p σ n eq = {!!}


-- naturals
adeq-fail .ℕ (N x) p σ n () -- just x ≡ nothing is false

-- variables
adeq-fail .ℕ (V x) p σ n eq = {!!}

-- addition
adeq-fail .ℕ (e ⊕ e₁) p σ n eq = {!!}

-- subtraction
adeq-fail .ℕ (e ⊝ e₁) p σ n eq = {!!}

-- if/else
adeq-fail .ℕ (if_then_else e e₁ e₂) p σ n eq = {!!}
