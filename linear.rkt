#lang racket

;; Pure Linear Types
;; Guannan Wei <guannanwei@outlook.com>

(require rackunit)
(require "share.rkt")

;; Linear Expressions

(struct NumE (n) #:transparent)

(struct IdLE (x) #:transparent)
(struct PlusLE (l r) #:transparent)
(struct UnitLE () #:transparent)
(struct LetUnitLE (e1 e2) #:transparent)
(struct ProdLE (fst snd) #:transparent)
(struct LetProdLE (x y e1 e2) #:transparent)
(struct LamLE (arg arg/lt body) #:transparent)
(struct AppLE (e1 e2) #:transparent)

;; Linear Types

(struct NumT () #:transparent)

(struct UnitLT () #:transparent)
(struct ProdLT (fst/lt snd/lt) #:transparent)
(struct ArrowLT (arg/lt res/lt) #:transparent)

;; Values

(struct NumV (n) #:transparent)
(struct ProdV (fst snd) #:transparent)
(struct UnitV () #:transparent)
(struct ClosureV (arg body env) #:transparent)

;; Environment & Type Environment

(struct Binding (name val) #:transparent)
(define lookup (make-lookup 'lookup Binding? Binding-name Binding-val))
(define ext-env cons)

(struct TypeBinding (name type) #:transparent)
(define type-lookup (make-lookup 'type-lookup TypeBinding? TypeBinding-name TypeBinding-type))
(define ext-tenv cons)

;; Parser

(define (parse s)
  (match s
    [(? number? x) (NumE x)]
    [(? symbol? x) (IdLE x)]
    ['() (UnitLE)]
    [`(+ ,l ,r) (PlusLE (parse l) (parse r))]
    [`(let ([() ,mt]) ,body)
     (LetUnitLE (parse mt) (parse body))]
    [`(let ([(,x ,y) ,e1]) ,body)
     (LetProdLE x y (parse e1) (parse body))]
    [`(λ ([,var : ,ty]) ,body)
     (LamLE var (parse-type ty) (parse body))]
    [`(,e1 ⊗ ,e2) (ProdLE (parse e1) (parse e2))]
    [`(,fun ,arg) (AppLE (parse fun) (parse arg))]))

(define (parse-type t)
  (match t
    [`num (NumT)]
    [`unit (UnitLT)]
    [`(,t1 ⊗ ,t2) (ProdLT (parse-type t1) (parse-type t2))]
    [`(,t1 → ,t2) (ArrowLT (parse-type t1) (parse-type t2))]))

;; Type Checker

(define (free-vars e)
  (match e
    [(NumE n) (set)]
    [(UnitLE) (set)]
    [(IdLE x) (set x)]
    [(PlusLE l r) (set-union (free-vars l)
                             (free-vars r))]
    [(LetUnitLE e1 e2) (free-vars e2)]
    [(ProdLE e1 e2) (set-union (free-vars e1)
                               (free-vars e2))]
    [(LetProdLE x y e1 e2)
     (set-union (free-vars e1)
                (set-subtract (free-vars e2)
                              (set x y)))]
    [(LamLE arg arg/t body)
     (set-subtract (free-vars body) (set arg))]
    [(AppLE e1 e2)
     (set-union (free-vars e1) (free-vars e2))]))

(define (partition-by Δ e1 e2)
  (define free-vars-e1 (set->list (free-vars e1)))
  (define free-vars-e2 (set->list (free-vars e2)))
  (if (empty? free-vars-e2)
      ;; TODO: verify Δ1 Δ2
      (partition (λ (b) (member (TypeBinding-name b) free-vars-e1)) Δ)
      (let-values ([(Δ2 Δ1)
                    (partition (λ (b) (member (TypeBinding-name b) free-vars-e2)) Δ)])
        (values Δ1 Δ2))))

(define (type-error-non-linear Δ)
  (type-error (format "not used: ~a" (map TypeBinding-name Δ))))

(define (typecheck e Δ)
  (match e
    [(NumE n) (if (empty? Δ)
                  (NumT)
                  (type-error-non-linear Δ))]
    [(UnitLE) (if (empty? Δ)
                  (UnitLT)
                  (type-error-non-linear Δ))]
    [(IdLE x) (if (eq? 1 (length Δ))
                  (type-lookup x Δ)
                  (type-error-non-linear Δ))]
    [(PlusLE l r)
     (define-values (Δ1 Δ2) (partition-by Δ l r))
     (match* ((typecheck l Δ1) (typecheck r Δ2))
       [((NumT) (NumT)) (NumT)]
       [(_ _) (type-error "not a num")])]
    [(ProdLE l r)
     (define-values (Δ1 Δ2) (partition-by Δ l r))
     (ProdLT (typecheck l Δ1) (typecheck r Δ2))]
    [(LetUnitLE u body)
     (define-values (Δ1 Δ2) (partition-by Δ u body))
     (match (typecheck u Δ1)
       [(UnitLT) (typecheck body Δ2)]
       [else (type-error "not a unit type")])]
    [(LetProdLE x y p body)
     (define-values (Δ1 Δ2) (partition-by Δ p body))
     (match (typecheck p Δ1)
       [(ProdLT f/t s/t)
        (typecheck body (ext-tenv (TypeBinding x f/t)
                                  (ext-tenv (TypeBinding y s/t) Δ2)))]
       [else (type-error "not a product type")])]
    [(LamLE arg arg/t body)
     (ArrowLT arg/t (typecheck body (ext-tenv (TypeBinding arg arg/t) Δ)))]
    [(AppLE fun arg)
     (define-values (Δ1 Δ2) (partition-by Δ fun arg))
     (match (typecheck fun Δ1)
       [(ArrowLT a/t r/t)
        (if (equal? a/t (typecheck arg Δ2)) r/t
            (type-error "argument types not agree"))]
       [_ (type-error "not a function")])]))

;; Interpreter

(define (interp expr env)
  (match expr
    [(NumE n) (NumV n)]
    [(IdLE x) (lookup x env)]
    [(UnitLE) (UnitV)]
    [(PlusLE l r) (NumV (+ (NumV-n (interp l env))
                           (NumV-n (interp r env))))]
    [(ProdLE l r) (ProdV (interp l env) (interp r env))]
    [(LamLE arg t body) (ClosureV arg body env)]
    [(LetUnitLE u body) (interp body env)]
    [(LetProdLE x y p body)
     (define pv (interp p env))
     (interp body (ext-env (Binding x (ProdV-fst pv))
                           (ext-env (Binding y (ProdV-snd pv)) env)))]
    [(AppLE fun arg)
     (match (interp fun env)
       [(ClosureV n body env*)
        (interp body (ext-env (Binding n (interp arg env)) env*))])]))

(define mt-env empty)
(define mt-tenv empty)

(define (run prog)
  (define prog* (parse prog))
  (typecheck prog* mt-tenv)
  (interp prog* mt-env))

;; Test

(module+ test
  (check-equal? (parse '{{λ {[x : {num ⊗ num}]}
                           {let {[(a b) x]}
                             {+ a b}}}
                         {3 ⊗ 4}})
                (AppLE
                 (LamLE
                  'x
                  (ProdLT (NumT) (NumT))
                  (LetProdLE 'a 'b (IdLE 'x) (PlusLE (IdLE 'a) (IdLE 'b))))
                 (ProdLE (NumE 3) (NumE 4))))

  (check-equal? (parse '{{λ {[x : unit]}
                           {let {[() x]}
                             4}}
                         {}})
                (AppLE (LamLE 'x (UnitLT) (LetUnitLE (IdLE 'x) (NumE 4)))
                       (UnitLE)))

  (check-equal? (free-vars (parse '{{λ {[x : {num ⊗ num}]}
                                      {let {[(a b) x]}
                                        {+ a b}}}
                                    {3 ⊗ 4}}))
                (set))

  (check-equal? (free-vars (parse '{{λ {[x : {num ⊗ num}]}
                                      {let {[(a b) x]}
                                        {+ d y}}}
                                    {3 ⊗ 4}}))
                (set 'y 'd))

  (check-equal? (typecheck (parse '{+ 1 2}) empty)
                (NumT))

  (check-equal? (typecheck (parse '{λ {[x : num]}
                                     {λ {[y : num]}
                                       {+ x y}}}) empty)
                (ArrowLT (NumT) (ArrowLT (NumT) (NumT))))

  (check-equal?  (typecheck (parse '{λ {[x : {num ⊗ num}]}
                                      {let {[(a b) x]}
                                        {+ a b}}})
                            empty)
                 (ArrowLT (ProdLT (NumT) (NumT)) (NumT)))

  (check-equal? (typecheck (parse '{{λ {[x : {num ⊗ num}]}
                                      {let {[(a b) x]}
                                        {+ a b}}}
                                    {3 ⊗ 4}}) empty)
                (NumT))

  (check-equal? (typecheck (parse '{{λ {[u : unit]}
                                      {let {[() u]}
                                        0}}
                                    ()})
                           empty)
                (NumT))

  (check-exn exn:fail? (λ () (typecheck (parse '{{λ {[u : unit]}
                                                   {let {[() u]}
                                                     u}}
                                                 ()})
                                        empty)))

  (check-exn exn:fail? (λ () (typecheck (parse '{{λ {[x : {num ⊗ num}]}
                                                   {let {[(a b) x]}
                                                     {+ a a}}}
                                                 {3 ⊗ 4}})
                                        empty)))

  (check-exn exn:fail? (λ () (typecheck (parse '{{λ {[x : {num ⊗ num}]}
                                                   {let {[(a b) x]}
                                                     {+ 3 4}}}
                                                 {3 ⊗ 4}})
                                        empty)))

  (check-exn exn:fail? (λ () (typecheck (parse '{{λ {[x : {num ⊗ num}]}
                                                   {let {[(a b) x]}
                                                     {+ a 3}}}
                                                 {3 ⊗ 4}})
                                        empty)))

  (check-exn exn:fail? (λ () (typecheck (parse '{{λ {[x : {num ⊗ num}]}
                                                   {let {[(a b) x]}
                                                     {+ 3 a}}}
                                                 {3 ⊗ 4}})
                                        empty)))
  )