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

(define (interp-cps exp env k)
  (match exp
    [(IdE x) (k (lookup x env))]
    [(NumE n) (k (NumV n))]
    [(PlusE l r)
     (interp-cps l env
                 (λ (lv)
                   (interp-cps r env
                               (λ (rv)
                                 (k (primop '+ lv rv))))))]
    [(MultE l r)
     (interp-cps l env
                 (λ (lv)
                   (interp-cps r env
                               (λ (rv)
                                 (k (primop '* lv rv))))))]
    [(LamE arg body)
     (k (ClosureV arg body env))]
    [(CallccE x body)
     (interp-cps body (ext-env (Binding x (Cont k)) env) k)]
    [(AppE fun arg)
     (interp-cps fun env
                 (λ (funv)
                   (cond [(ClosureV? funv)
                          (interp-cps arg env
                                      (λ (argv)
                                        (interp-cps (ClosureV-body funv)
                                                    (ext-env (Binding (ClosureV-arg funv) argv)
                                                             (ClosureV-env funv))
                                                    k)))]
                         [(Cont? funv) (interp-cps arg env (Cont-body funv))]
                         [else (error 'cps "not a function or continuation")])))]))

(define mt-env empty)
(define mt-k (lambda (v) v))

(define (run prog)
  (define prog* (parse prog))
  (interp-cps prog* mt-env mt-k))

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