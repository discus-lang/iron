
Iron Lambda.
http://iron.ouroborus.net

Iron Lambda is a collection of Coq formalizations for functional languages
of increasing complexity. All proofs use straight deBruijn indices for binders.

-------------------------------------------------------------------------------
Proofs that are "done" have at least Progress and Preservation theorems.

 Simple
  Simply Typed Lambda Calculus (STLC).
  "Simple" here refers to the lack of polymorphism.

 SimplePCF
  STLC with booleans, naturals and fixpoint.

 SimpleRef
  STLC with mutable references. 
  The typing judgement includes a store typing.

 SimpleData
  STLC with algebraic data and case expressions.
  The definition of expressions uses indirect mutual recursion. Expressions
  contain a list of case-alternatives, and alternatives contain expressions,
  but the definition of the list type is not part of the same recursive group.
  The proof requires that we define our own induction scheme for expressions. 

 SystemF
  Compared to STLC, the proof for SystemF needs more lifting lemmas so it can
  deal with deBruijn indices at the type level.

 SystemF2
  Very similar to SystemF, but with higher kinds.

 SystemF2Data
  SystemF2 with algebraic data and case expressions.
  Requires that we define simultaneous substitutions, which are used when
  subsituting expressions bound by pattern variables into the body of
  an alternative. The language allows data constructors to be applied to 
  general expressions rather than just values, which requires more work
  when defining evaluation contexts.

 SystemF2Store
  SystemF2 with algebraic data, case expressions and a mutable store.
  All data is allocated into the store and can be updated with primitive
  polymorphic update operators.

 SystemF2Effect
  SystemF2 with a region and effect system. Mutable references are allocated
  in regions in the store, and their lifetime follows the lexical structure
  of the code. 
