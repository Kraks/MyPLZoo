#lang racket

;; Simply Typed Lamdba Calculus
;; Guannan Wei <guannanwei@outlook.com>

(require rackunit)
(require "share.rkt")

;; Expressions

(struct NumE (n) #:transparent)
(struct BoolE (b) #:transparent)
(struct IdE (id) #:transparent)
(struct PlusE (l r) #:transparent)
(struct MultE (l r) #:transparent)
(struct AppE (fun arg) #:transparent)
(struct LamE (arg arg-type body) #:transparent)
(struct IfE (cnd thn els) #:transparent)

;; Types

(struct NumT () #:transparent)
(struct BoolT () #:transparent)
(struct ArrowT (arg res) #:transparent)

;; Values

(struct NumV (n) #:transparent)
(struct BoolV (b) #:transparent)
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
    ['true (BoolE #t)]
    ['false (BoolE #f)]
    [(? symbol? x) (IdE x)]
    [`(+ ,l ,r) (PlusE (parse l) (parse r))]
    [`(* ,l ,r) (MultE (parse l) (parse r))]
    [`(λ ([,var : ,ty]) ,body)
     (LamE var (parse-type ty) (parse body))]
    [`(let ([,var : ,ty ,val]) ,body)
     (AppE (LamE var (parse-type ty) (parse body)) (parse val))]
    [`(if ,cnd ,thn ,els)
     (IfE (parse cnd) (parse thn) (parse els))]
    [`(,fun ,arg) (AppE (parse fun) (parse arg))]
    [else (error 'parse "invalid expression")]))

(define (parse-type t)
  (match t
    ['num (NumT)]
    ['bool (BoolT)]
    [`(,tyarg -> ,tyres) (ArrowT (parse-type tyarg) (parse-type tyres))]
    [else (error 'parse-type "invalid type")]))

;; Type Checker

(define (typecheck-nums l r tenv)
  (match* ((typecheck l tenv) (typecheck r tenv))
    [((NumT) (NumT)) (NumT)]
    [(_ _) (type-error "not number")]))

(define (typecheck exp tenv)
  (match exp
    [(NumE n) (NumT)]
    [(BoolE b) (BoolT)]
    [(PlusE l r) (typecheck-nums l r tenv)]
    [(MultE l r) (typecheck-nums l r tenv)]
    [(IdE n) (type-lookup n tenv)]
    [(IfE cnd thn els)
     (if (BoolT? (typecheck cnd tenv))
         (let ([thn-type (typecheck thn tenv)]
               [els-type (typecheck els tenv)])
           (if (equal? thn-type els-type) thn-type
               (type-error "types of branches not agree")))
         (type-error "not a boolean"))]
    [(LamE arg arg-type body)
     (ArrowT arg-type (typecheck body (ext-tenv (TypeBinding arg arg-type) tenv)))]
    [(AppE fun arg)
     (match (typecheck fun tenv)
       [(ArrowT atype rtype) 
        (if (equal? atype (typecheck arg tenv)) rtype
            (type-error "argument types not agree"))]
       [_ (type-error "not a function")])]))

;; Interpreter

(define (interp expr env)
  (match expr
    [(IdE x) (lookup x env)]
    [(NumE n) (NumV n)]
    [(BoolE b) (BoolV b)]
    [(PlusE l r) (NumV (+ (NumV-n (interp l env))
                          (NumV-n (interp r env))))]
    [(MultE l r) (NumV (* (NumV-n (interp l env))
                          (NumV-n (interp r env))))]
    [(LamE arg at body) (ClosureV arg body env)]
    [(IfE cnd thn els)
     (match (interp cnd env)
       [(BoolV #t) (interp thn env)]
       [(BoolV #f) (interp els env)])]
    [(AppE fun arg)
     (match (interp fun env)
       [(ClosureV n body env*)
        (interp body (ext-env (Binding n (interp arg env)) env*))])]))

(define mt-env empty)
(define mt-tenv empty)

(define (run prog)
  (define prog* (parse prog))
  (typecheck prog* mt-tenv)
  (interp prog* mt-env))

;; Tests

(module+ test
  (check-equal? (run '1) (NumV 1))
  (check-equal? (run '{λ {[x : num]} x})
                (ClosureV 'x (IdE 'x) '()))
  (check-equal? (run '{{λ {[x : num]} {+ x x}} 3})
                (NumV 6))
  (check-equal? (run '{let {[double : {num -> num}
                                    {λ {[x : num]} {+ x x}}]}
                        {double 3}})
                (NumV 6))
  (check-equal? (run '{{if true
                           {λ {[x : num]} {+ x 1}}
                           {λ {[x : num]} {+ x 2}}}
                       3})
                (NumV 4))
  )
