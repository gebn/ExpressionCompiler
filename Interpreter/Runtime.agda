module Interpreter.Runtime where

open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.String

open import Interpreter.Instructions public

{- A program is simply a list of instructions. -}
Program = List Instr

{- The stack is a list of natural numbers, with the head at the front.
   Instructions remove and add elements to the stack as required. -}
Stack = List ℕ

{- The program state holds variable values.
   Providing a variable name as a string returns its value, or nothing if the variable is not defined. -}
State = String → Maybe ℕ
