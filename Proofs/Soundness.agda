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
sound .𝔹 (B _) _ _ _ zero    () -- just [] ≡ just (n ∷ []) is false
sound .𝔹 (B _) _ _ _ (suc _) () -- nothing ≡ just (n ∷ []) is false

-- naturals
sound .ℕ (N _)       _ _        _ zero    ()          -- just [] ≡ just n is false
sound .ℕ (N zero)    _ zero     _ (suc _) _    = refl -- just 0 ≡ just 0 is trivially correct
sound .ℕ (N zero)    _ (suc _)  _ (suc _) ()          -- just (0 ∷ []) ≡ just (suc n ∷ []) is false
sound .ℕ (N (suc _)) _ .(suc _) _ (suc _) refl = refl -- just (suc x) ≡ just (suc x) is trivially correct

-- variables
sound .ℕ (V _) _ zero    _ zero    ()                          -- just [] ≡ just (0 ∷ []) is false
sound .ℕ (V x) _ zero    σ (suc _) _ with σ x
sound .ℕ (V _) _ zero    _ (suc _) refl | just .zero = refl    -- just 0 ≡ just 0 is trivially correct
sound .ℕ (V _) _ zero    _ (suc _) ()   | nothing              -- nothing ≡ just (0 ∷ []) is false
sound .ℕ (V _) _ (suc _) _ zero    ()                          -- just [] ≡ just (suc n ∷ []) is false
sound .ℕ (V x) _ (suc _) σ (suc _) _ with σ x
sound .ℕ (V _) _ (suc n) _ (suc _) refl | just .(suc n) = refl -- just (suc n) ≡ just (suc n) is trivially correct
sound .ℕ (V _) _ (suc _) _ (suc _) ()   | nothing              -- nothing ≡ just (suc n ∷ []) is false

--addition
sound .ℕ (e ⊕ e') p n σ k eq = {!!}

--subtraction
sound .ℕ (e ⊝ e₁) p n σ k eq = {!!}

--if/else
sound .ℕ (if_then_else e e₁ e₂) p n σ k eq = {!!}
