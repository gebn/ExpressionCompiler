# Expression Compiler

A compiler from arithmetic expressions to a stack machine, written in Agda. This project was completed as part of the *Advanced Functional Programming* module at the University of Birmingham.

## Structure

We refactored the initial code into several modules for clarity. Our project is divided into four namespaces:

 - *Expression*  
   Building blocks for creating (`Exp`) and evaluating (`⟦_⟧`) expressions, as well as code to turn them into executable programs (`compile`).
    - The `Expr` type can be found in `Blocks.agda`.
    - Our `compile` function is in `Compiler.agda`.
    - Code to evaluate `Expr`essions `⟦_⟧` is located in `Evaluator.agda`.

 - *Interpreter*  
   Contains instructions (`Instr`) and infrastructure to execute programs (`⟨⟨_⟩⟩_,_,_`).
    - The `Instr` type can be found in `Instructions.agda`.
    - The supporting `Program`, `Stack` and `State`  types are in `Runtime.agda`.
    - `Program`s can be executed using `⟨⟨_⟩⟩_,_,_`, which is located in `Executor.agda`.

 - *Proofs*  
   Various proofs for the correctness of our compiler.
    - `sound` can be found in `Soundness.agda`.
    - `adeq` and `adeq-fail` proofs are in `Adequacy.agda`.

 - *Utilities*  
   Additional, general functions useful throughout the project.
    - Functions converting between booleans and naturals are housed in `Convert.agda`.
    - `NaturalBooleanLogic.agda` allows unary and binary boolean logic to be applied to natural arguments.
