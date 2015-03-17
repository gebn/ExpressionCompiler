module Utilities.Convert where

open import Data.Bool renaming (Bool to 𝔹)
open import Data.Nat

{- Converts a natural to a boolean. -}
ℕ→𝔹 : ℕ → 𝔹
ℕ→𝔹 0 = false
ℕ→𝔹 _ = true

{- Convert a boolean to a natural. -}
𝔹→ℕ : 𝔹 → ℕ
𝔹→ℕ false = 0
𝔹→ℕ true  = 1
