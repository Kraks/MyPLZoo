#lang racket

;; Simple Typed Lamdba Calculus
;; Guannan Wei <guannanwei@outlook.com>

(require rackunit)

;; Expressions

(struct NumE (n) #:transparent)
(struct BoolE (b) #:transparent)
(struct IdE (id) #:transparent)
(struct PlusE (l r) #:transparent)
(struct MultE (l r) #:transparent)
(struct AppE (fun arg) #:transparent)
(struct LamE (arg arg-type body) #:transparent)
(struct IfE (cnd thn els) #:transparent)

; Product

(struct ProdE (fst snd) #:transparent)
(struct FstE (p) #:transparent)
(struct SndE (p) #:transparent)

; Sum

(struct InLeftE (ty e) #:transparent)
(struct InRightE (ty e) #:transparent)
(struct MatchE (s v1 e1 v2 e2) #:transparent)

;; Types

(struct NumT () #:transparent)
(struct BoolT () #:transparent)
(struct ArrowT (arg/t res/t) #:transparent)
(struct ProdT (fst/t snd/t) #:transparent)
(struct SumT (l/t r/t) #:transparent)

;; Values

(struct NumV (n) #:transparent)
(struct BoolV (b) #:transparent)
(struct ClosureV (arg body env) #:transparent)
(struct ProdV (fst snd) #:transparent)
(struct SumV (label val) #:transparent)

;; Environment & Type Environment

(define (make-lookup error-hint isa? name-of val-of)
  (λ (name vals)
    (cond [(empty? vals) (error error-hint "free variable")]
          [(and (isa? (first vals))
                (equal? name (name-of (first vals))))
           (val-of (first vals))]
          [else ((make-lookup error-hint isa? name-of val-of) name (rest vals))])))

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
    [`(fst ,e) (FstE (parse e))]
    [`(snd ,e) (SndE (parse e))]
    [`(,l * ,r) (ProdE (parse l) (parse r))]
    [`(in-left ,e : ,ty) (InLeftE (parse-type ty) (parse e))]
    [`(in-right ,e : ,ty) (InRightE (parse-type ty) (parse e))]
    [`(match ,e ((,v1) ,e1) ((,v2) ,e2))
     (MatchE (parse e) v1 (parse e1) v2 (parse e2))]
    [`(lambda ([,var : ,ty]) ,body)
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
    [`(sum ,t1 ,t2) (SumT (parse-type t1) (parse-type t2))]
    [`(,tyfst * ,tysnd) (ProdT (parse-type tyfst) (parse-type tysnd))]
    [`(,tyarg -> ,tyres) (ArrowT (parse-type tyarg) (parse-type tyres))]
    [else (error 'parse-type "invalid type")]))

;; Type Checker

(define type-error
  (case-lambda
    [(msg) (error 'type-error "type error: ~a" msg)]
    [(e ty) (error 'type-error "~a should has type: ~a" e ty)]))

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
    [(ProdE l r) (ProdT (typecheck l tenv)
                        (typecheck r tenv))]
    [(FstE p) (ProdT-fst/t (typecheck p tenv))]
    [(SndE p) (ProdT-snd/t (typecheck p tenv))]
    [(InLeftE ty e)
     (define l/t (typecheck e tenv))
     (if (equal? l/t (SumT-l/t ty)) ty
         (type-error "sum types not agree"))]
    [(InRightE ty e)
     (define r/t (typecheck e tenv))
     (if (equal? r/t (SumT-r/t ty)) ty
         (type-error "sum types not agree"))]
    [(MatchE se v1 e1 v2 e2)
     (match (typecheck se tenv)
       [(SumT l/t r/t)
        (define e1/t (typecheck e1 (ext-tenv (TypeBinding v1 l/t) tenv)))
        (define e2/t (typecheck e2 (ext-tenv (TypeBinding v2 r/t) tenv)))
        (if (equal? e1/t e2/t) e1/t
            (type-error "types of branches not agree"))]
       [else (type-error "not a sum type")])]
    [(IfE cnd thn els)
     (if (BoolT? (typecheck cnd tenv))
         (let ([thn-type (typecheck thn tenv)]
               [els-type (typecheck els tenv)])
           (if (equal? thn-type els-type) thn-type
               (type-error "types of branches not agree")))
         (error 'typecheck "not a boolean"))]
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
    [(ProdE l r) (ProdV (interp l env)
                        (interp r env))]
    [(FstE p) (ProdV-fst (interp p env))]
    [(SndE p) (ProdV-snd (interp p env))]
    [(InLeftE ty e) (SumV 'left (interp e env))]
    [(InRightE ty e) (SumV 'right (interp e env))]
    [(MatchE e v1 e1 v2 e2)
     (match (interp e env)
       [(SumV 'left val) (interp e1 (ext-env (Binding v1 val) env))]
       [(SumV 'right val) (interp e2 (ext-env (Binding v2 val) env))])]
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
  (check-equal? (parse '{3 * 4})
                (ProdE (NumE 3) (NumE 4)))
  (check-equal? (parse '{lambda {[x : {num * num}]} {fst x}})
                (LamE 'x (ProdT (NumT) (NumT)) (FstE (IdE 'x))))
  (check-equal? (parse '{in-left 3 : {sum num num}})
                (InLeftE (SumT (NumT) (NumT)) (NumE 3)))
  (check-equal? (parse '{in-right 4 : {sum bool num}})
                (InRightE (SumT (BoolT) (NumT)) (NumE 4)))
  (check-equal? (parse '{match {in-right 4 : {sum bool num}}
                          {{l} {if l 3 4}}
                          {{r} {+ r r}}})
                (MatchE
                 (InRightE (SumT (BoolT) (NumT)) (NumE 4))
                 'l
                 (IfE (IdE 'l) (NumE 3) (NumE 4))
                 'r
                 (PlusE (IdE 'r) (IdE 'r))))

  (check-equal? (typecheck (parse '{match {in-right 4 : {sum bool num}}
                                     {{l} {if l 3 4}}
                                     {{r} {+ r r}}}) empty)
                (NumT))

  (check-equal? (typecheck (parse '{match {in-left {in-left 3 : {sum num bool}} : {sum {sum num bool} bool}}
                                     {{l} {match l
                                            {{l1} {+ l1 3}}
                                            {{l2} {if l2 1 2}}}}
                                     {{r} {if r 1 2}}}) empty)
                (NumT))
  
  (check-equal? (run '1) (NumV 1))
  (check-equal? (run '{lambda {[x : num]} x})
                (ClosureV 'x (IdE 'x) '()))
  (check-equal? (run '{{lambda {[x : num]} {+ x x}} 3})
                (NumV 6))
  (check-equal? (run '{let {[double : {num -> num}
                                    {lambda {[x : num]} {+ x x}}]}
                        {double 3}})
                (NumV 6))
  (check-equal? (run '{{if true
                           {lambda {[x : num]} {+ x 1}}
                           {lambda {[x : num]} {+ x 2}}}
                       3})
                (NumV 4))
  (check-equal? (run '{{lambda {[p : {num * bool}]}
                         {if {snd p} {fst p} {* 2 {fst p}}}}
                       {3 * true}})
                (NumV 3))
  (check-equal? (run '{{lambda {[p : {num * bool}]}
                         {if {snd p} {fst p} {* 2 {fst p}}}}
                       {3 * false}})
                (NumV 6))

  (check-equal? (run '{match {in-left {in-left 3 : {sum num bool}} : {sum {sum num bool} bool}}
                        {{l} {match l
                               {{l1} {+ l1 3}}
                               {{l2} {if l2 1 2}}}}
                        {{r} {if r 1 2}}})
                (NumV 6))
  )
