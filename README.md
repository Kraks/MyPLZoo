## Type Systems in Small Pieces

Type checkers and interpreters for various toy typed languages.

Each file is a standalone implementation, including a parser for S-expression based syntax, a type checker if any, an interpreter and a bunch of examples written in this language.

Any comments or pull requests are welcomed.

* `uni-typed.rkt` Uni-typed Lambda Calculus with numbers and arithmetics

* `stlc.rkt` Simple Typed Lambda Calculus (STLC)

* `stlc-sub.rkt` STLC + Record + Subtyping

* `stlc-infer.rkt` STLC + Type Inference

* `stlc-sum-prod.rkt` STLC + Sum type + Product type

* `stlc-union-intsec.rkt` STLC + Union type + Intersection type #TODO#

* `stlc-rec.rkt` STLC + Sum/Product tpye + Recursive function + Recursive type #TODO#

* `systemf.rkt` System F, i.e. STLC + Polymorhpism

* `systemf-ext.rkt` System F + Existential type #TODO#

* `systemf-omega.rkt` System F Omega #TODO#

* `hm.rkt` Hindley-Milner Type System, i.e. restricted System F with type inference #TODO#

* `dependent.rkt` Dependent Type #TODO#

* `refinement.rkt` Refinement Type #TODO#

* `cpcf.rkt` Contract PCF with dependent contract #TODO#

  ​

### Acknowledgements 
Many thanks to Matthew Flatt and [CS6510@Utah](http://www.eng.utah.edu/~cs6510/schedule.html), where I first learned crucial knowledge on semantics and interpreters.
