#lang racket

;; Simple Typed Lamdba Calculus with Type Operators
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
(struct VarT (name) #:transparent)
(struct OpAbsT (arg arg-kind body) #:transparent)
(struct OpAppT (t1 t2) #:transparent)
(struct ArrowT (arg res) #:transparent)

;; Kinds

(struct StarK () #:transparent)
(struct ArrowK (k1 k2) #:transparent)

;; Values

(struct NumV (n) #:transparent)
(struct BoolV (b) #:transparent)
(struct ClosureV (arg body env) #:transparent)

;; Environment & Type Environment

(struct Binding (name val) #:transparent)
(define lookup (make-lookup 'lookup Binding? Binding-name Binding-val))
(define ext-env cons)

(struct TypeBinding (name type) #:transparent)
(struct KindBinding (name kind) #:transparent)
(define type-lookup (make-lookup 'type-lookup TypeBinding? TypeBinding-name TypeBinding-type))
(define kind-lookup (make-lookup 'kind-lookup KindBinding? KindBinding-name KindBinding-kind))
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
    [(? symbol? x) (VarT x)]
    [`(Λ ([,tvar : ,k]) ,tbody)
     (OpAbsT tvar (parse-kind k) (parse-type tbody))]
    [`(,tyarg -> ,tyres) (ArrowT (parse-type tyarg) (parse-type tyres))]
    [`(,t1 ,t2) (OpAppT (parse-type t1) (parse-type t2))]
    [else (error 'parse-type "invalid type")]))

(define (parse-kind k)
  (match k
    ['* (StarK)]
    [`(,k1 -> ,k2) (ArrowK (parse-kind k1) (parse-kind k2))]))

;; Type Checker

(define (kind-check t tenv)
  (match t
    [(NumT) (StarK)]
    [(BoolT) (StarK)]
    [(ArrowT arg ret) (StarK)]
    [(VarT name) (kind-lookup name tenv)]
    [(OpAbsT arg arg/k body)
     (ArrowK arg/k (kind-check body (ext-tenv (KindBinding arg arg/k) tenv)))]
    [(OpAppT t1 t2)
     (match (kind-check t1 tenv)
       [(ArrowK k1 k2)
        (if (equal? (kind-check t2 tenv) k1)
            k2
            (error 'kind-check "kinds not agree"))]
       [else (error 'kind-check "not an arrow kind")])]))

(define (gen-name n i for body)
  (let ([new-n (string->symbol (string-append (symbol->string n)
                                              (number->string i)))])
    (if (or (free-type-var? new-n for)
            (free-type-var? new-n body))
        (gen-name n (+ i 1) for body)
        new-n)))

(define (free-type-var? n ty)
  (match ty
    [(NumT) #f]
    [(BoolT) #f]
    [(ArrowT a r)
     (or (free-type-var? n a) (free-type-var? n r))]
    [(VarT n^) (equal? n^ n)]
    [(OpAppT t1 t2)
     (or (free-type-var? n t1) (free-type-var? n t2))]
    [(OpAbsT arg arg/k body)
     (if (equal? arg n) #f
         (free-type-var? n body))]))

(define (type-subst what for in)
  (match in
    [(NumT) (NumT)]
    [(BoolT) (BoolT)]
    [(ArrowT arg res)
     (ArrowT (type-subst what for arg)
             (type-subst what for res))]
    [(VarT n) (if (equal? what n) for in)]
    [(OpAppT t1 t2)
     (OpAppT (type-subst what for t1)
             (type-subst what for t2))]
    [(OpAbsT arg arg/k body)
     (cond [(equal? arg what) in]
           [(free-type-var? arg for)
            (define new-n (gen-name arg 1 for body))
            (define new-body (type-subst arg (VarT new-n) body))
            (type-subst what for (OpAbsT new-n new-body))]
           [else (OpAbsT arg arg/k (type-subst what for body))])]))

(define (norm t)
  (match t
    [(OpAppT t1 t2)
     (match (norm t1)
       [(OpAbsT arg arg/k body) (type-subst arg t2 body)]
       [else (error 'type-norm "can not substitute")])]
    [else t]))

(define (type-equal? t1 t2)
  (match* (t1 t2)
    [((NumT) (NumT)) #true]
    [((BoolT) (BoolT)) #true]
    [((ArrowT t11 t12) (ArrowT t21 t22))
     (and (type-equal? t11 t21) (type-equal? t12 t22))]
    [((OpAbsT arg1 arg/k1 body1)
      (OpAbsT arg2 arg/k2 body2))
     (type-equal? body1 body2)]
    [((OpAppT t11 t12) (OpAppT t21 t22))
     (and (type-equal? t11 t21) (type-equal? t12 t22))]
    [(_ _) (type-equal? (norm t1) (norm t2))]))

(define (typecheck-nums l r tenv)
  (if (and (type-equal? (NumT) (typecheck l tenv))
           (type-equal? (NumT) (typecheck r tenv)))
      (NumT)
      (type-error "not a number")))

(define (typecheck exp tenv)
  (match exp
    [(NumE n) (NumT)]
    [(BoolE b) (BoolT)]
    [(PlusE l r) (typecheck-nums l r tenv)]
    [(MultE l r) (typecheck-nums l r tenv)]
    [(IdE n) (type-lookup n tenv)]
    [(IfE cnd thn els)
     (if (type-equal? (BoolT) (typecheck cnd tenv))
         (let ([thn-type (typecheck thn tenv)]
               [els-type (typecheck els tenv)])
           (if (type-equal? thn-type els-type)
               thn-type
               (type-error "types of branches not agree")))
         (type-error "not a boolean"))]
    [(LamE arg arg-type body)
     (if (equal? (StarK) (kind-check arg-type tenv))
         (ArrowT arg-type (typecheck body (ext-tenv (TypeBinding arg arg-type) tenv)))
         (error 'kind-check "not a star kind"))]
    [(AppE fun arg)
     (match (norm (typecheck fun tenv))
       [(ArrowT atype rtype)
        (if (type-equal? atype (typecheck arg tenv))
            rtype
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

  (check-equal? (type-subst 'z (NumT)
                            (parse-type '{Λ {[x : *]} {Λ {[y : *]} {x -> {z -> y}}}}))
                (OpAbsT 'x (StarK)
                        (OpAbsT 'y (StarK) (ArrowT (VarT 'x) (ArrowT (NumT) (VarT 'y))))))

  (check-true (type-equal? (parse-type '{{Λ {[x : *]} {x -> x}} num})
                           (parse-type '{num -> num})))

  (check-equal? (typecheck (parse '{{λ {[id : {{Λ {[x : *]} {x -> x}} num}]}
                                      {+ 4 {id 3}}}
                                    {λ {[x : num]} x}})
                           empty)
                (NumT))

  (check-equal? (run '{{λ {[id : {{Λ {[x : *]} {x -> x}} num}]}
                         {+ 4 {id 3}}}
                       {λ {[x : num]} x}})
                (NumV 7))

  (check-equal? (run '{let {[plus : {{{Λ {[x : *]}
                                         {Λ {[y : *]}
                                            {x -> {y -> x}}}}
                                      num} num}
                                  {λ {[x : num]}
                                    {λ {[y : num]}
                                      {+ x y}}}]}
                        {{plus 1} 2}})
                (NumV 3))
                            
  )
