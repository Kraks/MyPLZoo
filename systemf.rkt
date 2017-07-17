#lang racket

;; Implementation of System F
;; Guannan Wei <guannanwei@outlook.com>

(require rackunit)
(require "share.rkt")

;; Values

(struct NumV (n) #:transparent)
(struct BoolV (b) #:transparent)
(struct ClosureV (arg body env) #:transparent)
(struct PolyV (body env) #:transparent)

;; Expressions

(struct NumE (n) #:transparent)
(struct BoolE (b) #:transparent)
(struct IdE (id) #:transparent)
(struct PlusE (l r) #:transparent)
(struct MultE (l r) #:transparent)
(struct LamE (arg arg-type body) #:transparent)
(struct AppE (fun arg) #:transparent)
(struct TyLamE (arg body) #:transparent)
(struct TyAppE (tyfun tyarg) #:transparent)

;; Types

(struct NumT () #:transparent)
(struct BoolT () #:transparent)
(struct FunT (arg result) #:transparent)
(struct VarT (name) #:transparent)
(struct ForallT (name tbody) #:transparent)

;; Environment & Type Environment

(struct Binding (name val) #:transparent)
(define lookup (make-lookup 'lookup Binding? Binding-name Binding-val))
(define ext-env cons)

(struct TypeVar (id) #:transparent)
(struct TypeBinding (name type) #:transparent)
(define type-lookup (make-lookup 'type-lookup TypeBinding? TypeBinding-name TypeBinding-type))
(define type-var-lookup (make-lookup 'type-var-lookup TypeVar? TypeVar-id TypeVar-id))
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
    [`(let ([,var : ,ty ,val]) ,body)
     (AppE (LamE var (parse-type ty) (parse body)) (parse val))]
    [`(λ ([,var : ,ty]) ,body)
     (LamE var (parse-type ty) (parse body))]
    [`(Λ [,tvar] ,body) (TyLamE tvar (parse body))]
    [`(@ ,tyfun ,tyarg) (TyAppE (parse tyfun) (parse-type tyarg))]
    [`(,fun ,arg) (AppE (parse fun) (parse arg))]
    [else (error 'parse "invalid expression")]))

(define (parse-type t)
  (match t
    ['num (NumT)]
    ['bool (BoolT)]
    [(? symbol? tvar) (VarT tvar)]
    [`(,tyarg -> ,tyres) (FunT (parse-type tyarg) (parse-type tyres))]
    [`(∀ (,tvar) ,t) (ForallT tvar (parse-type t))]
    [else (error 'parse-type "invalid type")]))

;; Type Checker

(define (type-check e tenv)
  (match e
    [(NumE n) (NumT)]
    [(BoolE b) (BoolT)]
    [(IdE n) (type-lookup n tenv)]
    [(PlusE l r) (type-check-nums l r tenv)]
    [(MultE l r) (type-check-nums l r tenv)]
    [(LamE arg-name arg-type body)
     (type-var-check arg-type tenv)
     (FunT arg-type (type-check body
                                (ext-tenv (TypeBinding arg-name arg-type) tenv)))]
    [(AppE fun arg)
     (match (type-check fun tenv)
       [(FunT arg-type res-type)
        (if (equal? arg-type (type-check arg tenv))
            res-type
            (type-error arg arg-type))]
       [else (type-error fun "function")])]
    [(TyLamE n body)
     (ForallT n (type-check body (ext-tenv (TypeVar n) tenv)))]
    [(TyAppE tyfun tyarg)
     (type-var-check tyarg tenv)
     (match (type-check tyfun tenv)
       [(ForallT n body) (type-subst n tyarg body)]
       [else (type-error tyfun "polymorphic function")])]))

(define (type-check-nums l r tenv)
  (match* ((type-check l tenv)
           (type-check r tenv))
    [((NumT) (NumT)) (NumT)]
    [((NumT) _) (type-error r (NumT))]
    [(_ _) (type-error l (NumT))]))

(define (type-var-check arg-type tenv)
  (match arg-type
    [(NumT) (values)]
    [(BoolT) (values)]
    [(FunT arg res)
     (type-var-check arg tenv) (type-var-check res tenv)
     (values)]
    [(VarT id) (type-var-lookup id tenv) (values)]
    [(ForallT id ty) (type-var-check ty (ext-tenv (TypeVar id) tenv))]))

(define (type-subst what for in)
  (match in
    [(NumT) (NumT)]
    [(BoolT) (BoolT)]
    [(FunT arg res) (FunT (type-subst what for arg)
                          (type-subst what for res))]
    [(VarT n) (if (equal? what n) for in)]
    [(ForallT n body)
     (cond [(equal? what n) (ForallT n body)]
           [(free-type-var? n for)
            (define new-n (gen-name n 1 for body))
            (define new-body (type-subst n (VarT new-n) body))
            (type-subst what for (ForallT new-n new-body))]
           [else (ForallT n (type-subst what for body))])]))

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
    [(FunT a r) (or (free-type-var? n a)
                    (free-type-var? n r))]
    [(VarT n^) (equal? n^ n)]
    [(ForallT n^ body)
     (if (equal? n n^) #f (free-type-var? n body))]))

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
    [(LamE n t body) (ClosureV n body env)]
    [(AppE fun arg)
     (match (interp fun env)
       [(ClosureV n body env*)
        (interp body (ext-env (Binding n (interp arg env)) env*))])]
    [(TyLamE n body) (PolyV body env)]
    [(TyAppE tyfun tyarg)
     (match (interp tyfun env)
       [(PolyV body env*) (interp body env*)])]))

(define mt-env empty)
(define mt-tenv empty)
(define (run prog)
  (define prog* (parse prog))
  (type-check prog* mt-tenv)
  (interp prog* mt-env))

;; Test

(module+ test
  (check-equal? (parse-type '{a -> a})
                (FunT (VarT 'a) (VarT 'a)))

  (check-equal? (parse-type '{∀ {a} {a -> a}})
                (ForallT 'a (FunT (VarT 'a) (VarT 'a))))
              
  (check-equal? (parse '{let {[id : {∀ {a} {a -> a}}
                                  [Λ [a] {λ {[x : a]} x}]]}
                          {+ {[@ id num] 1} {[@ id num] 2}}})
                (AppE
                 (LamE
                  'id
                  (ForallT 'a (FunT (VarT 'a) (VarT 'a)))
                  (PlusE
                   (AppE (TyAppE (IdE 'id) (NumT)) (NumE 1))
                   (AppE (TyAppE (IdE 'id) (NumT)) (NumE 2))))
                 (TyLamE 'a (LamE 'x (VarT 'a) (IdE 'x)))))

  (check-equal? (type-check (parse '{let {[id : {∀ {a} {a -> a}}
                                              [Λ [a] {λ {[x : a]} x}]]}
                                      {+ {[@ id num] 1} {[@ id num] 2}}})
                            mt-tenv)
                (NumT))

  (check-equal? (parse '{let {[x : num 4]}
                          {let {[y : num 5]}
                            {{{λ {[x : num]}
                                {λ {[y : num]}
                                  {+ x y}}} x} y}}})
                (AppE (LamE 'x (NumT)
                            (AppE (LamE 'y (NumT)
                                        (AppE (AppE (LamE 'x (NumT)
                                                          (LamE 'y (NumT) (PlusE (IdE 'x) (IdE 'y)))) (IdE 'x))
                                              (IdE 'y))) (NumE 5))) (NumE 4)))

  (check-equal? (type-check (parse '{let {[x : num 4]}
                                      {let {[y : num 5]}
                                        {{{λ {[x : num]}
                                            {λ {[y : num]}
                                              {+ x y}}} x} y}}}) mt-tenv)
                (NumT))

  (check-equal? (run '{let {[x : num 4]}
                        {let {[y : num 5]}
                          {{{λ {[x : num]}
                              {λ {[y : num]}
                                {+ x y}}} x} y}}})
                (NumV 9))

  (check-equal? (run '{let {[id : {∀ {a} {a -> a}}
                                [Λ [a] {λ {[x : a]} x}]]}
                        {+ {[@ id num] 1} {{[@ id {num -> num}] {λ {[x : num]} x}} 2}}})
                (NumV 3))

  (check-equal? (type-check
                 (parse '{let {[f : {∀ {a} {a -> {∀ {b} {{a -> b} -> b}}}}
                                  [Λ [a] {λ {[x : a]}
                                                [Λ [b] {λ {[g : {a -> b}]} {g x}}]}]]}
                           {[@ {[@ f num] 3} bool] {λ {[x : num]} true}}})
                 mt-tenv)
                (BoolT))

  (check-equal? (run '{let {[f : {∀ {a} {a -> {∀ {b} {{a -> b} -> b}}}}
                               [Λ [a] {λ {[x : a]}
                                             [Λ [b] {λ {[g : {a -> b}]} {g x}}]}]]}
                        {[@ {[@ f num] 3} bool] {λ {[x : num]} true}}})
                (BoolV #t))

  ; Boolean Encodings
  
  (define Bool '{∀ [a] {a -> {a -> a}}})
  (define True '{Λ [a] {λ {[x : a]} {λ {[y : a]} x}}})
  (define False '{Λ [a] {λ {[x : a]} {λ {[y : a]} y}}})
  (define And `{λ {[x : ,Bool]} {λ {[y : ,Bool]} {{[@ x ,Bool] y} ,False}}})
  (define Bool->Num `{λ {[x : ,Bool]} {{[@ x num] 1} 0}})

  (check-equal? (run `{let {[t : ,Bool ,True]}
                        {let {[f : ,Bool ,False]}
                          {let {[and : {,Bool -> {,Bool -> ,Bool}} ,And]}
                            {,Bool->Num {{and t} f}}}}})
                (NumV 0))

  (check-equal? (run `{let {[t : ,Bool ,True]}
                        {let {[f : ,Bool ,False]}
                          {let {[and : {,Bool -> {,Bool -> ,Bool}} ,And]}
                            {,Bool->Num {{and t} t}}}}})
                (NumV 1))
  )
