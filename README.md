## Type Systems in Small Pieces

Type checkers and interpreters for various toy typed languages.

Each file is a standalone implementation, including a parser for S-expression based syntax, a type checker if any, an interpreter and a bunch of examples written in this language.

Any comments or pull requests are welcomed.

* `uni-typed.rkt` Uni-typed Lambda Calculus
* `stlc.rkt` Simple Typed Lambda Calculus (STLC)
* `stlc-sub.rkt` STLC + Record + Subtyping
* `stlc-infer.rkt` STLC + Type Inference
* `stlc-sum-prod.rkt` STLC + sum type + product type #TODO#
* `stlc-rec.rkt` STLC + sum/product tpye + recursive function + recursive type #TODO#
* `systemf.rkt` System F, i.e. STLC + Polymorhpism
* `hm.rkt` HM Type System, i.e. restricted System F with type inference #TODO#
* `systemf-omega.rkt` System F Omega #TODO#
* `dependent.rkt` Dependent Type #TODO#
* `refinement.rkt` Refinement Type #TODO#
* `gradual.rkt` Gradual Type #TODO#
* `cpcf.rkt` Contract PCF + dependent contract #TODO#

### Acknowledgements 
Many thanks to Matthew Flatt and [CS6510@Utah](http://www.eng.utah.edu/~cs6510/schedule.html), where I first learned crucial knowledge on semantics and interpreters.
