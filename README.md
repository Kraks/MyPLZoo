## My PL Zoo

> Inside every large language is a small language struggling to get out...
> Tony Hoare

Interpreters and type checkers for various toy programming languages written in Racket.

Each file is a standalone and runnable implementation, including a parser for S-expression based syntax, a type checker if necessary, an interpreter and a set of test cases written in that language.

* `uni-typed.rkt` Uni-typed lambda calculus with numbers and arithmetics

* `interp-cps.rkt` An interpreter that supports `call/cc` operator

* `interp-delimited.rkt` An interpreter that supports delimited control operators (`reset` and `shift`)

* `stlc.rkt` Simply typed lambda calculus (STLC)

* `stlc-infer.rkt` STLC with type inference

* `stlc+sub.rkt` STLC + record + subtyping

* `stlc+sum+prod.rkt` STLC + sum/product types

* `stlc-omega.rkt` STLC + type operator

* `stlc+intsec.rkt` STLC + intersection types #TODO#

* `stlc+rec.rkt` STLC + sum/product tpye + recursive function + recursive types #TODO#

* `systemf.rkt` System F

* `systemf+ext.rkt` System F + existential types

* `systemf-omega.rkt` System F-omega

* `systemf+sub.rkt` System F + bounded quantifications and Subtyping #TODO#

* `letpoly.rkt` STLC with type inference and let-polymorphism #TODO#

* `lf.rkt` First-order dependent types, i.e. λLF #TODO#

* `lf+sum.rkt` λLF + sigma types #TODO#

* `linear.rkt` Pure linear types 

* `stlc+linear.rkt` STLC with linear types #TODO#

* `refinement.rkt` Refinement types #TODO#

* `cpcf.rkt` Contract PCF with dependent contract #TODO#

* `gradual.rkt` STLC with gradual types #TODO#

