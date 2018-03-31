#lang racket

(require rackunit)
(require "share.rkt")

;; Expressions

(struct NumE (n) #:transparent)
(struct IdE (id) #:transparent)
(struct PlusE (l r) #:transparent)
(struct MultE (l r) #:transparent)
(struct AppE (fun arg) #:transparent)
(struct LamE (arg body) #:transparent)
(struct CallccE (k body) #:transparent)
(struct ResetE (e) #:transparent)
(struct ShiftE (k body) #:transparent)

;; Values

(struct NumV (n) #:transparent)
(struct ClosureV (arg body env) #:transparent)

(struct Cont (body))

;; Environment

(struct Binding (name val) #:transparent)
(define lookup (make-lookup 'lookup Binding? Binding-name Binding-val))
(define ext-env cons)

;; Parser

(define (parse s)
  (match s
    [(? number? x) (NumE x)]
    [(? symbol? x) (IdE x)]
    [`(+ ,l ,r) (PlusE (parse l) (parse r))]
    [`(* ,l ,r) (MultE (parse l) (parse r))]
    [`(λ (,var) ,body) (LamE var (parse body))]
    [`(call/cc (λ (,k) ,body))
     (CallccE k (parse body))]
    [`(let/cc ,k ,body)
     (CallccE k (parse body))]
    [`(reset ,e) (ResetE (parse e))]
    [`(shift ,k ,body)
     (ShiftE k (parse body))]
    [`(,fun ,arg) (AppE (parse fun) (parse arg))]
    [else (error 'parse "invalid expression")]))

;; Interpreter

(define (primop op l r)
  (match* (l r)
    [((NumV lv) (NumV rv))
     (match op
       ['+ (NumV (+ lv rv))]
       ['* (NumV (* lv rv))])]
    [(_ _) (error 'primop "invalid operator")]))

(define (interpd exp env k r)
  (match exp
    [(IdE x) ((k r) (lookup x env))]
    [(NumE n) ((k r) (NumV n))]
    [(PlusE lhs rhs)
     (interpd lhs env
              (λ (r)
                (λ (lv)
                  (interpd rhs env
                           (λ (r)
                             (λ (rv)
                               ((k r) (primop '+ lv rv))))
                           r)))
              r)]
    [(MultE lhs rhs)
     (interpd lhs env
              (λ (r)
                (λ (lv)
                  (interpd rhs env
                           (λ (r)
                             (λ (rv)
                               ((k r) (primop '* lv rv))))
                           r)))
              r)]
    [(LamE arg body)
     ((k r) (ClosureV arg body env))]
    [(CallccE x e)
     (interpd e (ext-env (Binding x (Cont (λ (k1)
                                            (λ (r)
                                              (λ (v)
                                                ((k r) v)))))) ; discard k1, do k and escape
                         env) 
              k
              r)]
    [(ResetE e)
     (interpd e env (λ (r) r) (k r))]
    [(ShiftE x e)
     (interpd e (ext-env (Binding x (Cont (λ (k1)
                                            (λ (r)
                                              (λ (v)
                                                ((k (k1 r)) v)))))) ; do k and go back to k1
                         env) 
              (λ (r) r)
              r)]
    [(AppE fun arg)
     (interpd fun env
              (λ (r)
                (λ (funv)
                  (cond [(ClosureV? funv)
                         (interpd arg env
                                  (λ (r)
                                    (λ (argv)
                                      (interpd (ClosureV-body funv)
                                               (ext-env (Binding (ClosureV-arg funv) argv)
                                                        (ClosureV-env funv))
                                               k
                                               r)))
                                  r)]
                        [(Cont? funv) (interpd arg env ((Cont-body funv) k) r)]))) ; feed with current continuation `k`
              r)]))


(define mt-env empty)
(define mt-k (λ (r) (λ (v) (r v))))
(define mt-r (λ (x) x))

(define (run prog)
  (define prog* (parse prog))
  (interpd prog* mt-env mt-k mt-r))

;; Tests

(check-equal? (run '{+ 1 2}) (NumV 3))
(check-equal? (run '{* 2 3}) (NumV 6))
(check-equal? (run '{{λ {x} {+ x x}} 3})
              (NumV 6))
(check-equal? (run '{+ 1 {let/cc k1
                           {+ 2 {+ 3 {let/cc k2
                                       {+ 4 {k1 5}}}}}}})
              (NumV 6))
(check-equal? (run '{+ 1 {let/cc k1
                           {+ 2 {+ 3 {let/cc k2
                                       {+ 4 {k2 5}}}}}}})
              (NumV 11))
(check-equal? (run '{+ 1 {call/cc {λ {k1}
                                    {+ 2 {+ 3 {k1 4}}}}}})
              (NumV 5))

(check-equal? (run '{+ 5 {reset {+ 2 {shift k {+ 1 {k {k 3}}}}}}})
              (NumV 13))

(check-equal? (run '{+ 5 {reset {+ 3 {shift c {+ {c 0} {c 1}}}}}})
              (NumV 12))

(check-equal? (run '{+ 1 {reset {+ 2 {reset {+ 4 {shift k {shift k2 8}}}}}}})
              (NumV 11))
#|
{+ 1 {reset {+ 2 {reset {+ 4 {shift k {shift k2 {k {k2 8}}}}}}}}}

{+ 1 {reset {+ 2 {reset {{λ {k} {shift k2 {k {k2 8}}}}
                         {λ {v} {reset {+ 4 v}}}}}}}}

{+ 1 {reset {+ 2 {reset {{λ {k} {shift k2 {k {k2 8}}}}
                         {λ {v} {reset {+ 4 v}}}}}}}}

{+ 1 {reset {+ 2 {reset {{λ {k2} {k2 8}} 
                         {λ {v2}
                           {reset {{λ {k} {k v2}}
                                   {λ {v} {reset {+ 4 v}}}}}}}}}}}
|#

(check-equal? (run '{{λ {f} {+ 1 {reset {+ 2 {f 3}}}}}
                        {λ {x} {shift k x}}})
              (NumV 4))

(check-equal? (run '{reset {+ 1 {+ {shift a {a 1}}
                                      {shift b {b {b 1}}}}}})
              (NumV 5))

(check-equal? (run '{+ 2 {+ 1 {call/cc {λ {k1}
                                            {+ 2 {+ 3 {k1 4}}}}}}})
              (NumV 7))

(check-equal? (run '{+ 2 {reset {+ 1 {call/cc {λ {k1}
                                                   {+ 2 {+ 3 {k1 4}}}}}}}})
              (NumV 7))

(check-equal? (run '{+ 1 {let/cc k1
                              {+ 2 {+ 3 {let/cc k2
                                          {+ 4 {k1 5}}}}}}})
              (NumV 6))

(check-equal? (run '{+ 1 {let/cc k1
                              {+ 2 {+ 3 {let/cc k2
                                          {+ 4 {k2 5}}}}}}})
              (NumV 11))
