module Proofs.Soundness where

open import Data.Bool renaming (Bool to 𝔹)
open import Data.List
open import Data.Maybe
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

open import Expression.Compiler
open import Expression.Evaluator
open import Interpreter.Executor

{-
Refined version of soundness proof
Proves that executing a compiled expression and evaluating that same expression
produce the same output and is added to the exisiting stack.
More verbosely: if, at the end of compiling and executing an expression in a program, 
a new number is concatenated with the exisiting stack, the result of evaluating the 
raw expression using the same state will result in the same number.
-}
sound' : (T : Set)(s : Stack) (e : Exp T) (p : Program) (n : ℕ) (σ : State) (k k' : ℕ) →
        ⟨⟨ compile e ++ p ⟩⟩ s , σ , k ≡ ⟨⟨ p ⟩⟩ (n ∷ s), σ , k' → ⟦ e ⟧ σ ≡ just n

-- booleans
sound' .𝔹 s (B x) p n σ k k' eq = {!!}

-- naturals
sound' .ℕ s (N x) p n σ k k' eq = {!!}

-- variables
sound' .ℕ s (V x) p n σ k k' eq = {!!}

--addition
sound' .ℕ s (e ⊕ e₁) p n σ k k' eq = {!!}

--subtraction
sound' .ℕ s (e ⊝ e₁) p n σ k k' eq = {!!}

--if/else
sound' .ℕ s (if_then_else e e₁ e₂) p n σ k k' eq = {!!} 


{-
Original version of soundness proof
Proves that executing a compiled expression and evaluating that same expression
produce the same output.
More verbosely: if, at the end of compiling and executing an expression, the stack
contains a single number, the result of evaluating the raw expression using the same
state will result in the same number.
-}
sound : (T : Set) (e : Exp T) (p : Program) (n : ℕ) (σ : State) (k : ℕ) →
        ⟨⟨ compile e ⟩⟩ [] , σ , k ≡ just [ n ] → ⟦ e ⟧ σ ≡ just n

--we can prove the original version of soundness by the stronger refined proof above.
sound t e p n σ k eq = sound' t [] e [] n σ k (suc 0) fact 
  where
  ++-empty : {A : Set} (x : List A) → x ++ [] ≡ x 
  ++-empty  [] = refl
  ++-empty (x ∷ xs) = cong (_∷_ x) (++-empty xs)
  fact : ⟨⟨ compile e ++ [] ⟩⟩ [] , σ , k ≡ just (n ∷ [])
  fact = begin 
    ⟨⟨ compile e ++ [] ⟩⟩ [] , σ , k  ≡⟨ cong (λ w → ⟨⟨ w ⟩⟩ [] , σ , k) (++-empty (compile e)) ⟩
    ⟨⟨ compile e ⟩⟩ [] , σ , k        ≡⟨ eq ⟩ 
    just (n ∷ []) 
    ∎

{-
--ORIGINAL PROOFS
-- booleans
sound .𝔹 (B x) p n σ zero ()    -- just [] ≡ just (n ∷ []) is false
sound .𝔹 (B x) p n σ (suc k) () -- nothing ≡ just (n ∷ []) is false

-- naturals
sound .ℕ (N x) p n σ zero ()              -- just [] ≡ just n is false                                                      --
sound .ℕ (N .n) p n σ (suc k) refl = refl -- just n ≡ just n is trivially correct

-- variables
sound .ℕ (V x) p n σ zero ()                       -- just [] ≡ just (suc n ∷ []) is false
sound .ℕ (V x) p n σ (suc k) eq with σ x
sound .ℕ (V x) p n σ (suc k) refl | just .n = refl -- just (suc n) ≡ just (suc n) is trivially correct
sound .ℕ (V x) p n σ (suc k) () | nothing          -- nothing ≡ just (suc n ∷ []) is false

-- addition
sound .ℕ (e ⊕ e') p n σ k eq = {!!}

-- subtraction
sound .ℕ (e ⊝ e₁) p n σ k eq = {!!}

-- if/else
sound .ℕ (if_then_else e e₁ e₂) p n σ zero ()    -- just [] ≡ just (n ∷ []) is false
sound .ℕ (if_then_else e e₁ e₂) p n σ (suc k) () -- nothing ≡ just (n ∷ []) is false
-}
