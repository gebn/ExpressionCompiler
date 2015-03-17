module Util.NatBool where

open import Data.Bool renaming (Bool to 𝔹)
open import Data.Nat

open import Util.Convert

{- Apply a unary boolean operator to a natural. -}
ubop : (𝔹 → 𝔹) → ℕ → ℕ
ubop op n = 𝔹→ℕ (op (ℕ→𝔹 n))

{- Apply a binary boolean operator to naturals. -}
bbop : (𝔹 → 𝔹 → 𝔹) → ℕ → ℕ → ℕ
bbop op n₁ n₂ = ubop op' n₂
  where op' = op (ℕ→𝔹 n₁)
