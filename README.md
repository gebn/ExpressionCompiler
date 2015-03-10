# ExpressionCompiler

A compiler from arithmetic expressions to a stack machine, written in Agda.

## Structure

We refactored the initial code into three modules:

 - *Expression*
   Building blocks for creating (`Exp`) and evaluating (`⟦_⟧`) expressions, as well as code to turn them into executable programs (`compile`).

 - *Interpreter*
   Contains instructions (`Instr`) and infrastructure to execute programs (`⟨⟨_⟩⟩_,_,_`).

 - *Proofs*
   Various proofs for the correctness of our compiler.
