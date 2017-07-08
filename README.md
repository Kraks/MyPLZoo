## Type Systems in Small Pieces

Type checkers and interpreters for various toy typed languages.

Each file is a standalone implementation, including a parser for S-expression based syntax, a type checker if any, an interpreter and a bunch of examples written in this language.

Any comments or pull requests are welcomed.

* `uni-typed.rkt` Uni-typed Lambda Calculus with numbers and arithmetics

* `stlc.rkt` Simply Typed Lambda Calculus (STLC)

* `stlc-infer.rkt` STLC with Type Inference

* `stlc+sub.rkt` STLC + Record + Subtyping

* `stlc+sum+prod.rkt` STLC + Sum type + Product type

* `stlc+intsec.rkt` STLC + Intersection type #TODO#

* `stlc+rec.rkt` STLC + Sum/Product tpye + Recursive function + Recursive type #TODO#

* `systemf.rkt` System F, i.e. STLC + Universal quantification

* `systemf+ext.rkt` System F + Existential type #TODO#

* `systemf+sub.rkt` System F + Bounded quantifications and Subtyping #TODO#

* `systemf-omega.rkt` System F Omega #TODO#

* `hm.rkt` Hindley-Milner Type System, i.e. restricted System F with type inference #TODO#

* `dependent.rkt` Dependent Types #TODO#

* `linear.rkt` Pure Linear Types 

* `stlc+linear.rkt` STLC with Linear Types #TODO#

* `refinement.rkt` Refinement Types #TODO#

* `cpcf.rkt` Contract PCF with dependent contract #TODO#

* `gradual.rkt` STLC with Gradual Types #TODO#


### Acknowledgements 
Many thanks to Matthew Flatt and [CS6510@Utah](http://www.eng.utah.edu/~cs6510/schedule.html), where I first learned crucial knowledge on semantics and interpreters.
