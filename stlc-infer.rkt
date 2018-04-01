#lang racket

;; Type Inference for Simply Typed Lambda Calculus
;; Guannan Wei <guannanwei@outlook.com>

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

;; Types

(struct NumT () #:transparent)
(struct BoolT () #:transparent)
(struct VarT (name) #:transparent)
(struct ArrowT (arg result) #:transparent)

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

;; Parsers

(define (parse s)
  (match s
    [(? number? x) (NumE x)]
    ['true (BoolE #t)]
    ['false (BoolE #f)]
    [(? symbol? x) (IdE x)]
    [`(+ ,l ,r) (PlusE (parse l) (parse r))]
    [`(* ,l ,r) (MultE (parse l) (parse r))]
    [`(let ([,var ,val]) ,body)
     (AppE (LamE var (parse body)) (parse val))]
    [`(λ (,var) ,body) (LamE var (parse body))]
    [`(,fun ,arg) (AppE (parse fun) (parse arg))]
    [else (error 'parse "invalid expression")]))

;; Fresh Number Generator

(define (counter)
  (define count 0)
  (define (inner)
    (set! count (add1 count))
    count)
  inner)

(define fresh-n (counter))

;; Type Inference

(struct Eq (fst snd) #:transparent)

(define (type-subst in src dst)
  (match in
    [(NumT) in]
    [(BoolT) in]
    [(VarT x) (if (equal? src in) dst in)]
    [(ArrowT t1 t2) (ArrowT (type-subst t1 src dst)
                            (type-subst t2 src dst))]))

(define (subst eqs src dst)
  (cond [(empty? eqs) eqs]
        [else (define eq (first eqs))
              (define eqfst (Eq-fst eq))
              (define eqsnd (Eq-snd eq))
              (cons (Eq (type-subst eqfst src dst)
                        (type-subst eqsnd src dst))
                    (subst (rest eqs) src dst))]))

(define (occurs? t in)
  (match in
    [(NumT) #f]
    [(ArrowT at rt) (or (occurs? t at) (occurs? t rt))]
    [(VarT x) (equal? t in)]))

(define not-occurs? (compose not occurs?))

(define (unify-error t1 t2)
  (error 'type-error "can not unify: ~a and ~a" t1 t2))

(define (unify-helper substs result)
  (match substs
    ['() result]
    [(list (Eq fst snd) rest ...)
     (match* (fst snd)
       [((VarT x) t)
        (if (not-occurs? fst snd)
            (unify-helper (subst rest fst snd) (cons (Eq fst snd) result))
            (unify-error fst snd))]
       [(t (VarT x))
        (if (not-occurs? snd fst)
            (unify-helper (subst rest snd fst) (cons (Eq snd fst) result))
            (unify-error snd fst))]
       [((ArrowT t1 t2) (ArrowT t3 t4))
        (unify-helper `(,(Eq t1 t3) ,(Eq t2 t4) ,@rest) result)]
       [(x x) (unify-helper rest result)]
       [(_ _)  (unify-error fst snd)])]))

(define (unify substs) (unify-helper (set->list substs) (list)))

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
    [(AppE fun arg)
     (define-values (funty funconst) (type-infer fun tenv (set)))
     (define-values (argty argconst) (type-infer arg tenv (set)))
     (define new-tvar (VarT (fresh-n)))
     (values new-tvar (set-add (set-union funconst argconst) (Eq funty (ArrowT argty new-tvar))))]))

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
     (ArrowT (reify substs t1) (reify substs t2))]))

(define (typecheck exp tenv)
  (set! fresh-n (counter))
  (define-values (ty constraints) (type-infer exp tenv (set)))
  (reify (unify constraints) ty))

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
       [(ClosureV n body env*) (interp body (ext-env (Binding n (interp arg env)) env*))])]))

(define mt-env empty)
(define mt-tenv empty)

(define (run prog)
  (define prog* (parse prog))
  (typecheck prog* mt-tenv)
  (interp prog* mt-env))

;; Tests

(module+ test
  (check-equal? (type-subst (VarT 'x) (VarT 'x) (NumT))
                (NumT))
  
  (check-equal? (subst (list (Eq (VarT 'a) (NumT))) (VarT 'a) (NumT))
                (list (Eq (NumT) (NumT))))

  (check-equal? (subst (list (Eq (VarT 'a) (VarT 'a))) (VarT 'a) (NumT))
                (list (Eq (NumT) (NumT))))

  (check-equal? (subst (list (Eq (VarT 'b) (VarT 'a))) (VarT 'a) (NumT))
                (list (Eq (VarT 'b) (NumT))))
  
  (check-equal? (unify-helper (list (Eq (ArrowT (VarT 't1) (VarT 't1))
                                          (ArrowT (NumT) (VarT 't2))))
                              (list))
                (list (Eq (VarT 't2) (NumT)) (Eq (VarT 't1) (NumT))))

  (check-equal? (unify-helper (list (Eq (VarT 'a1) (ArrowT (NumT) (VarT 'a2)))
                                    (Eq (ArrowT (VarT 'a1) (VarT 'a2))
                                          (ArrowT (ArrowT (VarT 'a3) (VarT 'a3)) (VarT 'a4))))
                              (list))
                (list (Eq (VarT 'a4) (NumT)) (Eq (VarT 'a2) (NumT))
                      (Eq (VarT 'a3) (NumT)) (Eq (VarT 'a1) (ArrowT (NumT) (VarT 'a2)))))

  (check-exn exn:fail?
             (λ () (unify (list (Eq (VarT 'a1) (ArrowT (VarT 'a1) (VarT 'a2)))))))

  (check-values-equal? (type-infer (parse '{λ {x} {+ x 1}}) empty (set))
                       (values (ArrowT (VarT 1) (NumT))
                               (set (Eq (NumT) (NumT)) (Eq (VarT 1) (NumT)))))
  
  (check-values-equal? (type-infer (parse '{λ {x} {λ {y} {+ x y}}}) empty (set))
                       (values (ArrowT (VarT 2) (ArrowT (VarT 3) (NumT)))
                               (set (Eq (VarT 3) (NumT)) (Eq (VarT 2) (NumT)))))

  (check-values-equal? (type-infer (parse '{{λ {x} x} 1}) empty (set))
                       (values (VarT 5)
                               (set (Eq (ArrowT (VarT 4) (VarT 4)) (ArrowT (NumT) (VarT 5))))))

  (check-values-equal? (type-infer (parse '{{λ {f} {f 0}} {λ {x} x}}) empty (set))
                       (values (VarT 9)
                               (set (Eq (VarT 6) (ArrowT (NumT) (VarT 7)))
                                    (Eq (ArrowT (VarT 6) (VarT 7))
                                        (ArrowT (ArrowT (VarT 8) (VarT 8)) (VarT 9))))))

  (check-values-equal? (type-infer (parse '{λ {x} x}) empty (set))
                       (values (ArrowT (VarT 10) (VarT 10))
                               (set)))
  
  (check-equal? (typecheck (parse '{{λ {f} {f 0}} {λ {x} x}}) mt-tenv)
                (NumT))

  (check-equal? (typecheck (parse '{λ {x} {λ {y} {+ x y}}}) mt-tenv)
                (ArrowT (NumT) (ArrowT (NumT) (NumT))))

  ; λf.λu.u (f u) :: ((a -> b) -> a) -> (a -> b) -> b
  (check-equal? (typecheck (parse '{λ {f} {λ {u} {u {f u}}}}) mt-tenv)
                (ArrowT (ArrowT (ArrowT (VarT 3) (VarT 4)) (VarT 3))
                        (ArrowT (ArrowT (VarT 3) (VarT 4)) (VarT 4))))

  ; λx.λy.x (x y) :: (a -> a) -> a -> a
  (check-equal? (typecheck (parse '{λ {x} {λ {y} {x {x y}}}}) mt-tenv)
                (ArrowT (ArrowT (VarT 2) (VarT 2))
                        (ArrowT (VarT 2) (VarT 2))))

  ; λx.λy.x (y x) :: (a -> b) -> ((a -> b) -> a) -> b
  (check-equal? (typecheck (parse '{λ {x} {λ {y} {x {y x}}}}) mt-tenv)
                (ArrowT
                 (ArrowT (VarT 3) (VarT 4))
                 (ArrowT (ArrowT (ArrowT (VarT 3) (VarT 4)) (VarT 3))
                         (VarT 4))))

  ;; λx.λy.y (y x) :: a -> (a -> a) -> a
  (check-equal? (typecheck (parse '{λ {x} {λ {y} {y {y x}}}}) mt-tenv)
                (ArrowT (VarT 4) (ArrowT (ArrowT (VarT 4) (VarT 4)) (VarT 4))))
  
  (check-equal? (run '{{{λ {x} {λ {y} {+ x y}}} 3} 7})
                (NumV 10))

  ;; (a -> (b -> c)) -> (a -> b) -> (a -> c)
  (define S '{λ {x} {λ {y} {λ {z} {{x z} {y z}}}}})
  (check-equal? (typecheck (parse S) mt-tenv)
                (ArrowT (ArrowT (VarT 3) (ArrowT (VarT 5) (VarT 6)))
                        (ArrowT (ArrowT (VarT 3) (VarT 5))
                                (ArrowT (VarT 3) (VarT 6)))))
  
  ;; a -> b -> a
  (define K '{λ {x} {λ {y} x}})
  (check-equal? (typecheck (parse K) mt-tenv)
                (ArrowT (VarT 1) (ArrowT (VarT 2) (VarT 1))))

  ;; (a -> b) -> (a -> a)
  (check-equal? (typecheck (parse `(,S ,K)) mt-tenv)
                (ArrowT (ArrowT (VarT 6) (VarT 5)) (ArrowT (VarT 6) (VarT 6))))

  ;; a -> a
  (check-equal? (typecheck (parse `((,S ,K) ,K)) mt-tenv)
                (ArrowT (VarT 6) (VarT 6)))
  
  (check-exn exn:fail? (λ () (typecheck (parse '{{λ {id} {{id id} 3}} {λ {x} x}}) mt-tenv)))

  (check-exn exn:fail? (λ () (typecheck (parse '{λ {x} {λ {y} {{x y} x}}}) mt-tenv)))
  
  (check-exn exn:fail? (λ () (run '{{λ {x} {x x}} {λ {x} {x x}}})))

  (check-exn exn:fail? (λ () (run '{+ 3 true})))
)
