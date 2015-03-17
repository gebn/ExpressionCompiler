module Expression.Compiler where

open import Data.List
open import Data.Nat
open import Data.Bool

open import Expression.Blocks
open import Interpreter.Runtime

{- Turns an expression construct into an executable program. -}
compile : ∀ {T} → Exp T → Program


-- boolean true and false are equivalent to the naturals 1 and 0 respectively
compile (B true)  = [ Val (suc zero) ]
compile (B false) = [ Val zero ]

-- raw values map to a single instruction
compile (N n)     = [ Val n ]

-- as do variable names
compile (V s)     = [ Var s ]


-- compute the result of the expression, then invert it
compile (¬ E)    = compile E ++ [ Not ]

-- compute the results of both expressions, and check both for true-ness
compile (E & E') = compile E ++ compile E' ++ [ And ]

-- compute the results of both expressions, and check either for true-ness
compile (E ∥ E') = compile E ++ compile E' ++ [ Or ]


-- the operand goes after the arguments as the instruction list is executed in-order
compile (E ⊕ E')  = (compile E ++ compile E') ++ [ Add ]

-- same as the arguments for the addition
compile (E ⊝ E')  = (compile E ++ compile E') ++ [ Sub ]


-- if-then-else is a bit more complex, and required the addition of a `Jmp` instruction
compile (if E then E' else E'') =
    e                          -- compute the condition
    ++ [ Joz (length e' + 1) ] -- if the condition is false, jump to the else
                               -- (the + 1 is to include our Jmp instruction at the end of the if branch)
    ++ e'                      -- execute the if branch
    ++ [ Jmp (length e'') ]    -- jump over the else branch
    ++ e''                     -- execute the else branch
  where
    e = compile E
    e' = compile E'
    e'' = compile E''
