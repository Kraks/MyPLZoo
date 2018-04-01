#lang racket

;; An Implementation of Let-polymorphism with Type Inference

(require rackunit)
(require racket/set)
(require "share.rkt")

;; Expressions

(struct NumE (n) #:transparent)
(struct BoolE (b) #:transparent)
(struct IdE (id) #:transparent)
(struct PlusE (l r) #:transparent)
(struct MultE (l r) #:transparent)
(struct LamE (arg body) #:transparent)
(struct AppE (fun arg) #:transparent)
(struct LetE (x e body) #:transparent)

;; Types

(struct NumT () #:transparent)
(struct BoolT () #:transparent)
(struct VarT (n) #:transparent)
(struct ArrowT (arg result) #:transparent)
(struct ForallT (ns tybody) #:transparent)

;; Values

(struct NumV (n) #:transparent)
(struct BoolV (b) #:transparent)
(struct PolyV (body env) #:transparent)
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
    [`(let ([,var ,val]) ,body)
     (LetE var (parse val) (parse body))]
    [`(λ (,var) ,body)
     (LamE var (parse body))]
    [`(,fun ,arg) (AppE (parse fun) (parse arg))]
    [else (error 'parse "invalid expression")]))

;; Fresh Number Generator

(define (counter)
  (define count 0)
  (define (inner)
    (set! count (add1 count))
    count)
  (values inner (λ () count)))

(define-values (fresh-n current-n) (counter))

(define (refresh!)
  (define-values (fresh-n^ current-n^) (counter))
  (set! fresh-n fresh-n^)
  (set! current-n current-n^))

;; Type Inference

(struct Eq (fst snd) #:transparent)

(define (free-type-var? n ty)
  (match ty
    [(NumT) #f]
    [(BoolT) #f]
    [(ArrowT a r) (or (free-type-var? n a)
                    (free-type-var? n r))]
    [(VarT n^) (equal? n^ n)]
    [(ForallT n^ body)
     (if (equal? n n^) #f (free-type-var? n body))]))

(define (generalize ty vars [gen-vars '{}])
  (if (eq? vars 0)
      (if (empty? gen-vars) ty (ForallT gen-vars ty))
      (if (free-type-var? vars ty)
          (generalize ty (- vars 1) (cons vars gen-vars))
          (generalize ty (- vars 1) gen-vars))))

(define (instantiate ty ns)
  (cond [(empty? ns) ty]
        [else (instantiate (type-subst ty (VarT (car ns)) (VarT (fresh-n)))
                (rest ns))]))

(define (type-subst in src dst)
  (match in
    [(NumT) in]
    [(BoolT) in]
    [(VarT x) (if (equal? src in) dst in)]
    [(ArrowT t1 t2) (ArrowT (type-subst t1 src dst)
                            (type-subst t2 src dst))]
    [(ForallT n ty)
     (cond [(equal? src n) (ForallT n ty)]
           [(free-type-var? n dst)
            (define new-n (fresh-n))
            (define new-ty (type-subst n (VarT new-n) ty))
            (type-subst (ForallT new-n new-ty) src dst)]
           [else (ForallT n (type-subst ty src dst))])]))

(define (unify/subst eqs src dst)
  (cond [(empty? eqs) eqs]
        [else (define eq (first eqs))
              (define eqfst (Eq-fst eq))
              (define eqsnd (Eq-snd eq))
              (cons (Eq (type-subst eqfst src dst)
                        (type-subst eqsnd src dst))
                    (unify/subst (rest eqs) src dst))]))

(define (occurs? t in)
  (match in
    [(NumT) #f]
    [(BoolT) #f]
    [(VarT x) (equal? t in)]
    [(ArrowT at rt) (or (occurs? t at) (occurs? t rt))]
    [(ForallT n ty)
     (match t
       [(VarT n^) (if (eq? n n^) #f
                      (occurs? t ty))]
       [_ (error 'occurs? "not a VarT")])]))

(define not-occurs? (compose not occurs?))

(define (unify-error t1 t2)
  (error 'type-error "can not unify: ~a and ~a" t1 t2))

(define (unify/helper substs result)
  (match substs
    ['() result]
    [(list (Eq fst snd) rest ...)
     (match* (fst snd)
       [((VarT x) t)
        (if (not-occurs? fst snd)
            (unify/helper (unify/subst rest fst snd) (cons (Eq fst snd) result))
            (unify-error fst snd))]
       [(t (VarT x))
        (if (not-occurs? snd fst)
            (unify/helper (unify/subst rest snd fst) (cons (Eq snd fst) result))
            (unify-error snd fst))]
       [((ArrowT t1 t2) (ArrowT t3 t4))
        (unify/helper `(,(Eq t1 t3) ,(Eq t2 t4) ,@rest) result)]
       [(x x) (unify/helper rest result)]
       [(_ _)  (unify-error fst snd)])]))

(define (unify substs) (unify/helper (set->list substs) (list)))

(define (type-infer exp tenv const)
  (match exp
    [(NumE n) (values (NumT) const)]
    [(BoolE b) (values (BoolT) const)]
    [(PlusE l r)
     (define-values (lty lconst) (type-infer l tenv (set)))
     (define-values (rty rconst) (type-infer r tenv (set)))
     (values (NumT)
             (set-add (set-add (set-union lconst rconst) (Eq lty (NumT))) (Eq rty (NumT))))]
    [(MultE l r)
     (define-values (lty lconst) (type-infer l tenv (set)))
     (define-values (rty rconst) (type-infer r tenv (set)))
     (values (NumT)
             (set-add (set-add (set-union lconst rconst) (Eq lty (NumT))) (Eq rty (NumT))))]
    [(IdE x)
     (values (type-lookup x tenv) const)]
    [(LamE arg body)
     (define new-tvar (VarT (fresh-n)))
     (define-values (bty bconst)
       (type-infer body (ext-tenv (TypeBinding arg new-tvar) tenv) const))
     (values (ArrowT new-tvar bty) bconst)]
    [(LetE x e body)
     (define-values (ety econst) (type-infer e tenv (set)))
     (define new-var (VarT (fresh-n)))
     (define new-ety (generalize (reify (unify (set-add econst (Eq new-var ety))) new-var)
                                 (current-n)))
     (define-values (bdty bdconst) (type-infer body (ext-tenv (TypeBinding x new-ety) tenv) (set)))
     (values bdty (set-union econst bdconst))]
    [(AppE fun arg)
     (define-values (funty funconst) (type-infer fun tenv (set)))
     (define new-funty (match funty
                         [(ForallT ns ty) (instantiate ty ns)]
                         [_ funty]))
     (define-values (argty argconst) (type-infer arg tenv (set)))
     (define new-tvar (VarT (fresh-n)))
     (values new-tvar (set-add (set-union funconst argconst) (Eq new-funty (ArrowT argty new-tvar))))]))

(define (reify substs ty)
  (define (lookup/default x sts)
    (match sts
      ['() x]
      [(list (Eq fst snd) rest ...)
       (if (equal? fst x)
           (lookup/default snd substs)
           (lookup/default x rest))]))
  
  (match ty
    [(NumT) (NumT)]
    [(BoolT) (BoolT)]
    [(VarT x)
     (define ans (lookup/default ty substs))
     (if (ArrowT? ans) (reify substs ans) ans)]
    [(ArrowT t1 t2)
     (ArrowT (reify substs t1) (reify substs t2))]
    [(ForallT ns ty)
     (reify substs ty)]))

(define (typecheck exp tenv)
  (refresh!)
  (define-values (ty constraints) (type-infer exp tenv (set)))
  (generalize (reify (unify constraints) ty) (current-n)))

;; Interpreter

(define (interp expr env)
  (match expr
    [(IdE x) (lookup x env)]
    [(NumE n) (NumV n)]
    [(BoolE b) (BoolV b)]
    [(PlusE l r) (NumV (+ (NumV-n (interp l env)) (NumV-n (interp r env))))]
    [(MultE l r) (NumV (* (NumV-n (interp l env)) (NumV-n (interp r env))))]
    [(LamE arg body) (ClosureV arg body env)]
    [(AppE fun arg)
     (match (interp fun env)
       [(ClosureV n body env*) (interp body (ext-env (Binding n (interp arg env)) env*))])]
    [(LetE x e body)
     (interp body (ext-env (Binding x (interp e env)) env))])) 

(define mt-env empty)
(define mt-tenv empty)

(define (run prog)
  (define prog* (parse prog))
  (typecheck prog* mt-tenv)
  (interp prog* mt-env))

;; Tests

(module+ test
  (check-equal? (generalize (ArrowT (VarT 1) (VarT 1)) 1 (list))
                (ForallT (list 1) (ArrowT (VarT 1) (VarT 1))))
  
  (check-equal? (typecheck (parse '{let {[id {λ {x} x}]}
                                     {{id {id {λ {y} y}}}
                                      {id 0}}})
                           empty)
                (NumT))

  (check-equal? (typecheck (parse '{let {[plus {λ {x} {λ {y} {+ x y}}}]}
                                     {{plus 3} 4}})
                           empty)
                (NumT))

  (check-equal? (typecheck (parse '{let {[id {λ {x} x}]}
                                     id})
                           empty)
                (ForallT '(1) (ArrowT (VarT 1) (VarT 1))))

  (define S '{λ {x} {λ {y} {λ {z} {{x z} {y z}}}}})
  (check-equal? (typecheck (parse S) mt-tenv)
                (ForallT '(3 5 6)
                         (ArrowT (ArrowT (VarT 3) (ArrowT (VarT 5) (VarT 6)))
                                 (ArrowT (ArrowT (VarT 3) (VarT 5))
                                         (ArrowT (VarT 3) (VarT 6))))))
  
  (define K '{λ {x} {λ {y} x}})
  (check-equal? (typecheck (parse K) mt-tenv)
                (ForallT '(1 2) (ArrowT (VarT 1) (ArrowT (VarT 2) (VarT 1)))))
                
  (check-exn exn:fail? (λ () (typecheck (parse '{{λ {id} {{id id} 3}} {λ {x} x}}) mt-tenv)))
  )