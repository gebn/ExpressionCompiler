module Interpreter.Instructions where

open import Data.Nat
open import Data.String

{- The various types of instruction that our interpreter can execute. -}
data Instr : Set where
  Var : String → Instr -- a variable name
  Val : ℕ → Instr      -- a literal value
  Add : Instr
  Sub : Instr
  Jmp : ℕ → Instr      -- jump
  Joz : ℕ → Instr      -- jump on zero
  Err : Instr
