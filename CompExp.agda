module CompExp where

open import Data.Nat
open import Data.Bool renaming (Bool to 𝔹; _∧_ to oldand)
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟪_⟫)
open import Data.Maybe
open import Data.String renaming (_++_ to _^_)

{- The various types of instruction that our interpreter can execute. -}
data Instr : Set where
  Var : String → Instr -- a variable name
  Val : ℕ → Instr      -- a literal value
  Add : Instr
  Sub : Instr
  Joz : ℕ → Instr      -- jump on zero
  Err : Instr

{- A program is simply a list of instructions. -}
Program = List Instr

{- The stack is a list of natural numbers, with the head at the front.
   Instructions remove and add elements to the stack as required. -}
Stack = List ℕ

{- The program state holds variable values.
   Providing a variable name as a string returns its value, or nothing if the variable is not defined. -}
State = String → Maybe ℕ

{- Executes a program, returning the final state of its stack, or nothing if an error occurred. -}
⟨⟨_⟩⟩_,_,_ : Program → Stack → State → ℕ → Maybe Stack
⟨⟨ [] ⟩⟩ s , _ , _                         = just s                       -- if there are no (more) instructions to execute, return the stack
⟨⟨ _ ⟩⟩ s , _ , zero                       = just s                       -- if the counter has reached zero, ignore any further instructions and return the stack
⟨⟨ Val x ∷ p ⟩⟩ s , σ , suc k              = ⟨⟨ p ⟩⟩ (x ∷ s) , σ , k     -- if we're given a constant, just push it onto the stack and decrement the counter
⟨⟨ Var x ∷ p ⟩⟩ s , σ , suc k with σ x                                    -- if we're provided with a variable, retrieve its value from the state
...                            | just v  = ⟨⟨ p ⟩⟩ (v ∷ s) , σ , k        -- success - push it onto the stack in the same way as if we'd just received a Val
...                            | nothing = nothing                        -- error (e.g. it is undefined) - fail
⟨⟨ Add ∷ p ⟩⟩ (m ∷ n ∷ s) , σ , suc k      = ⟨⟨ p ⟩⟩ (m + n ∷ s) , σ , k -- addition sums the first two elements in the stack, and pushes the result back onto the stack
⟨⟨ Sub ∷ p ⟩⟩ (m ∷ n ∷ s) , σ , suc k      = ⟨⟨ p ⟩⟩ (m ∸ n ∷ s) , σ , k -- subtraction reduces the head of the stack by the second element, and pushes back the result
⟨⟨ Joz n ∷ p ⟩⟩ (zero  ∷ s) , σ , suc k    = ⟨⟨ drop n p ⟩⟩ s , σ , k    -- jump on zero and the head of the stack is zero, so skip forward n instructions
⟨⟨ Joz _ ∷ p ⟩⟩ (suc _ ∷ s) , σ , suc k    = ⟨⟨ p ⟩⟩ s , σ , k           -- jump on zero, but the head of the stack is not zero, so just ignore the instruction and continue
⟨⟨ _ ⟩⟩ _ , _ , _ = nothing                                               -- any other scenario is an error (e.g. an empty stack when asked to do addition)

{- The recursive type of arithmetic expressions. -}
data Exp : (A : Set) → Set where
  B   : 𝔹 → Exp 𝔹                              -- boolean
  N   : ℕ → Exp ℕ                               -- natural number (linked to Val)
  V   : String → Exp ℕ                          -- variable (linked to Var)
  _⊕_ : Exp ℕ → Exp ℕ → Exp ℕ                   -- addition
  if_then_else : Exp 𝔹 → Exp ℕ → Exp ℕ → Exp ℕ -- if/else flow control statement
infixl 5 _⊕_

{- Evaluates an expression and returns the result, or nothing if an error occured. -}
⟦_⟧ : ∀ {T} → Exp T → State → Maybe ℕ
⟦ N(v) ⟧ σ = just v                       -- a literal value trivially evaluates to itself
⟦ V(s) ⟧ σ = σ s                          -- a variable name - look up its value in the state
⟦ E ⊕ E' ⟧ σ = ⟦ E ⟧ σ +' ⟦ E' ⟧ σ where -- recursively evaluate each side of the operator (N.B. states are identical)
  _+'_ : Maybe ℕ → Maybe ℕ → Maybe ℕ
  just m +' just n = just (m + n)         -- if both sides returned a value, the result is simply the sum of them
  _      +'      _ = nothing              -- otherwise halt evaluation and return an error
⟦ if E then E′ else E″ ⟧ σ with ⟦ E ⟧ σ   -- evaluate the condition
...  | just zero    = ⟦ E″ ⟧ σ            -- zero is equivalent to false - return the evaluation of the 'else' block
...  | just (suc _) = ⟦ E′ ⟧ σ            -- all other non-error values evaluate to true - evaluate and return the 'if' block
...  | nothing      = nothing             -- evaluation of the condition failed - fail ourselves
⟦ _ ⟧ _ = nothing                        -- any other scenario is an error (e.g. a boolean expression on its own)

compile : ∀ {T} → Exp T → Program
compile (N n)    = [ Val n ]
compile (V s)    = [ Var s ]
compile (E ⊕ E') = (compile E ++ compile E') ++ [ Add ]
compile E        = [ Err ]

{-
Proves that executing a compiled expression and evaluating that same expression 
produce the same output.
More verbosely: if, at the end of compiling and executing an expression, the stack 
contains a single number, the result of evaluating the raw expression using the same 
state will result in the same number.
-}
sound : (T : Set) (e : Exp T) (p : Program) (n : ℕ)(σ : State) (k : ℕ) →
        ⟨⟨ compile e ⟩⟩ [] , σ , k ≡ just [ n ] → ⟦ e ⟧ σ ≡ just n
sound = {!!}

{-
Proves that if an expression evaluates to a given value n, it can be compiled and 
executed up to a point at which the result will be equal to n.
More verbosely: if the result of evaluating an expression is n, there exists a 
number of steps k, that when the same expression is compiled and evaluated over k 
steps, will produce the result n.
-}
adeq : (T : Set) (e : Exp T) (p : Program) (σ : State) (n : ℕ) →
        ⟦ e ⟧ σ ≡ just n → (∃ λ k → ⟨⟨ compile e ⟩⟩ [] , σ , k ≡ just [ n ])
adeq = {!!}

{-
Identical to adeq above, except that if the result of evaluation is nothing, there 
exists a number of execution steps after which the result will also be nothing.
-}
adeq-fail : (T : Set) (e : Exp T) (p : Program) (σ : State) (n : ℕ) →
        ⟦ e ⟧ σ ≡ nothing → (∃ λ k → ⟨⟨ compile e ⟩⟩ [] , σ , k ≡ nothing)
adeq-fail = {!!}
