#lang racket

;; Uni-typed Lambda Calculus
;; Guannan Wei <guannanwei@outlook.com>

(require rackunit)
(require "share.rkt")

;; Expressions

(struct NumE (n) #:transparent)
(struct IdE (id) #:transparent)
(struct PlusE (l r) #:transparent)
(struct MultE (l r) #:transparent)
(struct AppE (fun arg) #:transparent)
(struct LamE (arg body) #:transparent)
(struct If0E (cnd thn els) #:transparent)

;; Values

(struct NumV (n) #:transparent)
(struct ClosureV (arg body env) #:transparent)

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
    [`(let ([,var ,val]) ,body)
     (AppE (LamE var (parse body)) (parse val))]
    [`(if0 ,cnd ,thn ,els)
     (If0E (parse cnd) (parse thn) (parse els))]
    [`(,fun ,arg) (AppE (parse fun) (parse arg))]
    [else (error 'parse "invalid expression")]))

;; Interpreter

(define (interp expr env)
  (match expr
    [(IdE x) (lookup x env)]
    [(NumE n) (NumV n)]
    [(PlusE l r) (NumV (+ (NumV-n (interp l env))
                          (NumV-n (interp r env))))]
    [(MultE l r) (NumV (* (NumV-n (interp l env))
                          (NumV-n (interp r env))))]
    [(LamE arg body) (ClosureV arg body env)]
    [(If0E cnd thn els)
     (match (interp cnd env)
       [(NumV 0) (interp thn env)]
       [(NumV _) (interp els env)]
       [else (error 'interp "not a number")])]
    [(AppE fun arg)
     (match (interp fun env)
       [(ClosureV n body env*)
        (interp body (ext-env (Binding n (interp arg env)) env*))]
       [else (error 'interp "not a function")])]))

(define mt-env empty)
(define mt-tenv empty)

(define (run prog)
  (define prog* (parse prog))
  (interp prog* mt-env))

;; Tests

(module+ test
  (check-equal? (run '1) (NumV 1))
  (check-equal? (run '{let {[double {λ {x} {+ x x}}]}
                        {double {double 3}}})
                (NumV 12))
  (check-equal? (run '{let {[five {if0 0 5 6}]} five})
                (NumV 5))
  )
