# Expression Compiler

A compiler from arithmetic expressions to a stack machine, written in Agda. This project was completed as part of the *Advanced Functional Programming* module at the University of Birmingham.

## Team

 - **George Brighton** ([@gebn](https://github.com/gebn)) ([contributions](https://github.com/gebn/ExpressionCompiler/commits?author=gebn))
 - Renu Budiyanto ([@RenuAB](https://github.com/RenuAB)) ([contributions](https://github.com/gebn/ExpressionCompiler/commits?author=RenuAB))
 - Sam Jones ([@Sam066](https://github.com/Sam066)) ([contributions](https://github.com/gebn/ExpressionCompiler/commits?author=Sam066))
 - Michael Thomas ([@mikeyt103](https://github.com/mikeyt103)) ([contributions](https://github.com/gebn/ExpressionCompiler/commits?author=mikeyt103))
 - Grace Wong ([@gcywong](https://github.com/gcywong)) ([contributions](https://github.com/gebn/ExpressionCompiler/commits?author=gcywong))

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

## Management

We made the decision at an early stage to focus on proofs rather than extending functionality, in order to fit in with the spirit of the module - after all, Agda is a proof assistant.

Given how each part of the project is fairly self contained, very little inter-person management was necessary; it was simply a case of assigning work. This was done by breaking down a given proof into pattern matches, each case becoming a work unit. GitHub's [Issues](https://github.com/gebn/ExpressionCompiler/issues) feature was used to track allocation of work to team members so everyone knew who was working on what. Although not necessary, each unit of work was completed in its own branch, before being rebased onto `master`.

I was very laid back with how cases were completed, allowing team members to work together, and switch when they became stuck, in an effort to avoid getting bogged down. We also set up a [Facebook group](https://www.facebook.com/groups/917497978290063/) (secret) and held a one-hour team meeting every Monday for members to update others, ask questions and raise issues. This all worked well until *all* the cases became difficult, at which time we moved towards adding new operators (`¬`, `&`, `∥`).

Overall, I think the team felt the project was rather impenetrable beyond a certain stage. Initial cases were trivial, but making progress with latter ones, despite several meetings, proved to be extremely difficult.
