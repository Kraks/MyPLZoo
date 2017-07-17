#lang racket

;; System F with Existential Types and Product Types
;; Guannan Wei <guannanwei@outlook.com>

(require rackunit)
(require "share.rkt")

;; Values

(struct NumV (n) #:transparent)
(struct BoolV (b) #:transparent)
(struct ClosureV (arg body env) #:transparent)
(struct PolyV (body env) #:transparent)
(struct PackV (body concrete/t tvar ext/t) #:transparent)
(struct ProdV (fst snd) #:transparent)

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

(struct ProdE (fst snd) #:transparent)
(struct FstE (p) #:transparent)
(struct SndE (p) #:transparent)

(struct PackE (body conc/t tvar ext/t) #:transparent)
(struct UnPackE (tvar pvar pack body) #:transparent)

;; Types

(struct NumT () #:transparent)
(struct BoolT () #:transparent)
(struct FunT (arg result) #:transparent)
(struct VarT (name) #:transparent)
(struct ForallT (name tbody) #:transparent)
(struct ExtT (name tbody) #:transparent)
(struct ProdT (fst/t snd/t) #:transparent)

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
    [`(fst ,e) (FstE (parse e))]
    [`(snd ,e) (SndE (parse e))]
    [`(,l × ,r) (ProdE (parse l) (parse r))]
    ; Type Abstraction
    [`(Λ [,tvar] ,body) (TyLamE tvar (parse body))]
    [`(@ ,tyfun ,tyarg) (TyAppE (parse tyfun) (parse-type tyarg))]
    ; Existential Types
    [`(pack [,ct] ,body : (∃ [,atvar] ,tbody))
     (PackE (parse body) (parse-type ct) atvar (parse-type tbody))]
    [`(unpack ([,tvar] [,pvar ,pack]) ,body)
     (UnPackE tvar pvar (parse pack) (parse body))]
    [`(,fun ,arg) (AppE (parse fun) (parse arg))]
    [else (error 'parse "invalid expression")]))

(define (parse-type t)
  (match t
    ['num (NumT)]
    ['bool (BoolT)]
    [(? symbol? tvar) (VarT tvar)]
    [`(,tyarg -> ,tyres) (FunT (parse-type tyarg) (parse-type tyres))]
    [`(∀ (,tvar) ,t) (ForallT tvar (parse-type t))]
    [`(∃ (,tvar) ,t) (ExtT tvar (parse-type t))]
    [`(,tyfst × ,tysnd) (ProdT (parse-type tyfst) (parse-type tysnd))]
    [else (error 'parse-type "invalid type")]))

;; Type Checker

(define (typecheck e tenv)
  (match e
    [(NumE n) (NumT)]
    [(BoolE b) (BoolT)]
    [(IdE n) (type-lookup n tenv)]
    [(PlusE l r) (typecheck-nums l r tenv)]
    [(MultE l r) (typecheck-nums l r tenv)]
    [(ProdE l r) (ProdT (typecheck l tenv)
                        (typecheck r tenv))]
    [(FstE p) (ProdT-fst/t (typecheck p tenv))]
    [(SndE p) (ProdT-snd/t (typecheck p tenv))]
    [(LamE arg-name arg-type body)
     (type-var-check arg-type tenv)
     (FunT arg-type (typecheck body
                                (ext-tenv (TypeBinding arg-name arg-type) tenv)))]
    [(AppE fun arg)
     (match (typecheck fun tenv)
       [(FunT arg-type res-type)
        (if (equal? arg-type (typecheck arg tenv))
            res-type
            (type-error arg arg-type))]
       [else (type-error fun "function")])]
    [(TyLamE n body)
     (ForallT n (typecheck body (ext-tenv (TypeVar n) tenv)))]
    [(TyAppE tyfun tyarg)
     (type-var-check tyarg tenv)
     (match (typecheck tyfun tenv)
       [(ForallT n body) (type-subst n tyarg body)]
       [else (type-error tyfun "polymorphic function")])]
    [(PackE body ct tvar ext)
     (type-var-check ct tenv)
     (define tybody (typecheck body tenv))
     (if (equal? tybody (type-subst tvar ct ext))
         (ExtT tvar ext)
         (type-error "types not agree"))]
    [(UnPackE tvar pvar pack body)
     (match (typecheck pack tenv)
       [(ExtT n ext)
        (typecheck body (ext-tenv (TypeBinding pvar
                                               (type-subst n (VarT tvar) ext))
                                  (ext-tenv (TypeVar tvar) tenv)))]
       [else (type-error pack "package value")])]))

(define (typecheck-nums l r tenv)
  (match* ((typecheck l tenv)
           (typecheck r tenv))
    [((NumT) (NumT)) (NumT)]
    [((NumT) _) (type-error r (NumT))]
    [(_ _) (type-error l (NumT))]))

(define (type-var-check arg-type tenv)
  (match arg-type
    [(NumT) (values)]
    [(BoolT) (values)]
    [(ProdT lhs rhs)
     (type-var-check lhs tenv) (type-var-check rhs tenv)
     (values)]
    [(FunT arg res)
     (type-var-check arg tenv) (type-var-check res tenv)
     (values)]
    [(VarT id) (type-var-lookup id tenv) (values)]
    [(ForallT id ty) (type-var-check ty (ext-tenv (TypeVar id) tenv))]
    [(ExtT id ty) (type-var-check ty (ext-tenv (TypeVar id) tenv))]))

(define (type-subst what for in)
  (match in
    [(NumT) (NumT)]
    [(BoolT) (BoolT)]
    [(FunT arg res) (FunT (type-subst what for arg)
                          (type-subst what for res))]
    [(VarT n) (if (equal? what n) for in)]
    [(ProdT fst snd) (ProdT (type-subst what for fst)
                            (type-subst what for snd))]
    [(ExtT n body)
     (cond [(equal? what n) (ExtT n body)]
           [(free-type-var? n for)
            (define new-n (gen-name n 1 for body))
            (define new-body (type-subst n (VarT new-n) body))
            (type-subst what for (ExtT new-n new-body))]
           [else (ExtT n (type-subst what for body))])]
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
    [(ProdT fst snd)
     (or (free-type-var? n fst) (free-type-var? n snd))]
    [(FunT a r)
     (or (free-type-var? n a) (free-type-var? n r))]
    [(VarT n^) (equal? n^ n)]
    [(ForallT n^ body)
     (if (equal? n n^) #f (free-type-var? n body))]
    [(ExtT n^ body)
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
    [(FstE p) (ProdV-fst (interp p env))]
    [(SndE p) (ProdV-snd (interp p env))]
    [(ProdE l r) (ProdV (interp l env)
                        (interp r env))]
    [(LamE n t body) (ClosureV n body env)]
    [(AppE fun arg)
     (match (interp fun env)
       [(ClosureV n body env*)
        (interp body (ext-env (Binding n (interp arg env)) env*))])]
    [(TyLamE n body) (PolyV body env)]
    [(TyAppE tyfun tyarg)
     (match (interp tyfun env)
       [(PolyV body env*) (interp body env*)])]
    [(PackE body conc/t tvar ext/t)
     (PackV (interp body env) conc/t tvar ext/t)]
    [(UnPackE new-tvar pvar pack body)
     (match (interp pack env)
       [(PackV p conc/t tvar ext/t)
        (interp body (ext-env (Binding pvar p) env))])]))

(define mt-env empty)
(define mt-tenv empty)
(define (run prog)
  (define prog* (parse prog))
  (typecheck prog* mt-tenv)
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

  (check-equal? (typecheck (parse '{let {[id : {∀ {a} {a -> a}}
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

  (check-equal? (typecheck (parse '{let {[x : num 4]}
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

  (check-equal? (typecheck
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

  ;; Boolean Encodings
  
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

  ;; Test Existential Types
  
  (check-equal? (parse '{pack [{num × bool}] {λ {[x : num]} {x × false}} :
                              {∃ [a] {num -> a}}})
                (PackE
                 (LamE 'x (NumT) (ProdE (IdE 'x) (BoolE #f)))
                 (ProdT (NumT) (BoolT))
                 'a
                 (FunT (NumT) (VarT 'a))))

  (check-equal? (parse-type '{∃ [a] {num -> a}})
                (ExtT 'a (FunT (NumT) (VarT 'a))))

  (check-equal? (typecheck (parse '{pack [{num × bool}] {λ {[x : num]} {x × false}} :
                                         {∃ [a] {num -> a}}}) empty)
                (ExtT 'a (FunT (NumT) (VarT 'a))))

  (check-equal? (parse '{unpack ([b] [x {pack [{num × bool}]
                                              {λ {[x : num]} {x × false}} : {∃ [a] {num -> a}}}])
                                {x 3}})
                (UnPackE
                 'b
                 'x
                 (PackE
                  (LamE 'x (NumT) (ProdE (IdE 'x) (BoolE #f)))
                  (ProdT (NumT) (BoolT))
                  'a
                  (FunT (NumT) (VarT 'a)))
                 (AppE (IdE 'x) (NumE 3))))

  ;; Define a Counter with an initial value 1, a to-num function and a increment function
  (define counter '{pack [num] {1 × {{λ {[x : num]} x} × {λ {[x : num]} {+ x 1}}}} :
                         {∃ [Counter] {Counter × {{Counter -> num} × {Counter -> Counter}}}}})

  (check-equal? (typecheck (parse counter) empty)
                (ExtT
                 'Counter
                 (ProdT
                  (VarT 'Counter)
                  (ProdT (FunT (VarT 'Counter) (NumT)) (FunT (VarT 'Counter) (VarT 'Counter))))))

  ;; Unpack Counter, retrieve the initial value, increase it and turn to num
  (check-equal? (typecheck (parse `{unpack {[C] [counter ,counter]}
                                           {let {[init : C {fst counter}]}
                                             {let {[inc : {C -> C} {snd {snd counter}}]}
                                               {let {[C->num : {C -> num} {fst {snd counter}}]}
                                                 {C->num {inc init}}}}}})
                           empty)
                (NumT))
  
  (check-equal? (run`{unpack {[C] [counter ,counter]}
                             {let {[init : C {fst counter}]}
                               {let {[inc : {C -> C} {snd {snd counter}}]}
                                 {let {[C->num : {C -> num} {fst {snd counter}}]}
                                   {C->num {inc init}}}}}})
                (NumV 2))

  (check-equal? (run`{unpack {[C] [counter ,counter]}
                             {let {[init : C {fst counter}]}
                               {let {[inc : {C -> C} {snd {snd counter}}]}
                                 {let {[C->num : {C -> num} {fst {snd counter}}]}
                                   {C->num {inc {inc {inc init}}}}}}}})
                (NumV 4))
  )
