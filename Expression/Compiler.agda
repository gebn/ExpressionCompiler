module Expression.Compiler where

open import Data.List
open import Data.Nat
open import Data.Bool
open import Expression.Blocks
open import Interpreter.Runtime

{- Turns an expression construct into an executable program. -}
compile : ∀ {T} → Exp T → Program

-- raw values map to a single instruction
compile (N n)    = [ Val n ]

-- as do variable names
compile (V s)    = [ Var s ]

-- the operand goes after the arguments as the instruction list is executed in-order
compile (E ⊕ E') = (compile E ++ compile E') ++ [ Add ]

-- same as the arguments for the addition
compile (E ⊝ E') = (compile E ++ compile E') ++ [ Sub ]

compile (B true) = [ Val (suc zero) ]
compile (B false) = [ Val zero ] 


compile (if_then_else b E E') = {!!}  -- {!( [ Joz (compile b) ] ++ compile E ++ compile E')!}

-- everything else at the top level is an error
--compile _        = [  ]
