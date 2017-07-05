#lang racket

;; Type Inference for Simple Typed Lambda Calculus
;; Guannan Wei <guannanwei@outlook.com>

(require rackunit)
(require racket/set)

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

(define (make-lookup error-hint isa? name-of val-of)
  (λ (name vals)
    (cond [(empty? vals) (error error-hint "free variable")]
          [else (if (and (isa? (first vals))
                         (equal? name (name-of (first vals))))
                    (val-of (first vals))
                    ((make-lookup error-hint isa? name-of val-of) name (rest vals)))])))

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
    [`(lambda (,var) ,body) (LamE var (parse body))]
    [`(,fun ,arg) (AppE (parse fun) (parse arg))]
    [else (error 'parse "invalid expression")]))

;; Type Inference

(struct Pair (fst snd) #:transparent)

(define (type-subst in src dst)
  (match in
    [(NumT) in]
    [(BoolT) in]
    [(VarT x) (if (equal? src in) dst in)]
    [(ArrowT t1 t2) (ArrowT (type-subst t1 src dst)
                            (type-subst t2 src dst))]))

(define (subst pairs src dst)
  (cond [(empty? pairs) pairs]
        [else (define p (first pairs))
              (define pf (Pair-fst p))
              (define ps (Pair-snd p))
              (cons (Pair (type-subst pf src dst)
                          (type-subst ps src dst))
                    (subst (rest pairs) src dst))]))

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
    [(list (Pair fst snd) rest ...)
     (match* (fst snd)
       [((NumT) (NumT)) (unify-helper rest result)]
       [((BoolT) (BoolT)) (unify-helper rest result)]
       [((VarT x) t)
        (if (not-occurs? fst snd)
            (unify-helper (subst rest fst snd) (cons (Pair fst snd) result))
            (unify-error fst snd))]
       [(t (VarT x))
        (if (not-occurs? snd fst)
            (unify-helper (subst rest snd fst) (cons (Pair snd fst) result))
            (unify-error snd fst))]
       [((ArrowT t1 t2) (ArrowT t3 t4))
        (unify-helper `(,(Pair t1 t3) ,(Pair t2 t4) ,@rest) result)]
       [(_ _)  (unify-error fst snd)])]))

(define (unify substs) (unify-helper (set->list substs) (list)))

(define (type-infer exp tenv const vars)
  (match exp
    [(NumE n) (values (NumT) const vars)]
    [(BoolE b) (values (BoolT) const vars)]
    [(PlusE l r)
     (define-values (lty lconst lvars) (type-infer l tenv const vars))
     (define-values (rty rconst rvars) (type-infer r tenv lconst lvars))
     (values (NumT) (set-add (set-add rconst (Pair lty (NumT))) (Pair rty (NumT))) rvars)]
    [(MultE l r)
     (define-values (lty lconst lvars) (type-infer l tenv const vars))
     (define-values (rty rconst rvars) (type-infer r tenv lconst lvars))
     (values (NumT) (set-add (set-add rconst (Pair lty (NumT))) (Pair rty (NumT))) rvars)]
    [(IdE x)
     (values (type-lookup x tenv) const vars)]
    [(LamE arg body)
     (define new-tvar (VarT (add1 vars)))
     (define-values (bty bconst bvars)
       (type-infer body (ext-tenv (TypeBinding arg new-tvar) tenv) const (add1 vars)))
     (values (ArrowT new-tvar bty) bconst bvars)]
    [(AppE fun arg)
     (define-values (funty funconst funvars) (type-infer fun tenv const vars))
     (define-values (argty argconst argvars) (type-infer arg tenv funconst funvars))
     (define new-tvar (VarT (add1 argvars)))
     (values new-tvar (set-add (set-union funconst argconst)
                               (Pair funty (ArrowT argty new-tvar))) (add1 argvars))]))

(define (reify substs ty)
  (define lookup (make-lookup 'pair-lookup Pair? Pair-fst Pair-snd))
  (foldl (λ (p acc) (type-subst acc (Pair-fst p) (Pair-snd p)))
         (if (VarT? ty) (lookup ty substs) ty)
         substs))

(define (typecheck exp tenv)
  (define-values (ty constraints vars) (type-infer exp tenv (set) 0))
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
       [(ClosureV n body env*) (interp body (ext-env (Binding n (interp arg env)) env*))]
       [else (error 'interp "not a function")])]))

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
  
  (check-equal? (subst (list (Pair (VarT 'a) (NumT))) (VarT 'a) (NumT))
                (list (Pair (NumT) (NumT))))

  (check-equal? (subst (list (Pair (VarT 'a) (VarT 'a))) (VarT 'a) (NumT))
                (list (Pair (NumT) (NumT))))

  (check-equal? (subst (list (Pair (VarT 'b) (VarT 'a))) (VarT 'a) (NumT))
                (list (Pair (VarT 'b) (NumT))))
  
  (check-equal? (unify-helper (list (Pair (ArrowT (VarT 't1) (VarT 't1))
                                          (ArrowT (NumT) (VarT 't2))))
                              (list))
                (list (Pair (VarT 't2) (NumT)) (Pair (VarT 't1) (NumT))))

  (check-equal? (unify-helper (list (Pair (VarT 'a1) (ArrowT (NumT) (VarT 'a2)))
                                    (Pair (ArrowT (VarT 'a1) (VarT 'a2))
                                          (ArrowT (ArrowT (VarT 'a3) (VarT 'a3)) (VarT 'a4))))
                              (list))
                (list (Pair (VarT 'a4) (NumT)) (Pair (VarT 'a2) (NumT))
                      (Pair (VarT 'a3) (NumT)) (Pair (VarT 'a1) (ArrowT (NumT) (VarT 'a2)))))

  (check-exn exn:fail?
             (λ () (unify (list (Pair (VarT 'a1) (ArrowT (VarT 'a1) (VarT 'a2)))))))
  
  (define (check-values-equal? l1 l2)
    (call-with-values
     l1
     (λ vs1 (call-with-values
             l2
             (λ vs2 (check-true (andmap equal? vs1 vs2)))))))

  (check-values-equal? (λ () (type-infer (parse '{lambda {x} {+ x 1}}) empty (set) 0))
                       (λ () (values (ArrowT (VarT 1) (NumT))
                                     (set (Pair (VarT 1) (NumT)) (Pair (NumT) (NumT)))
                                     1)))

  (check-values-equal? (λ () (type-infer (parse '{lambda {x} {lambda {y} {+ x y}}}) empty (set) 0))
                       (λ () (values (ArrowT (VarT 1) (ArrowT (VarT 2) (NumT)))
                                     (set (Pair (VarT 1) (NumT)) (Pair (VarT 2) (NumT)))
                                     2)))
  
  (check-values-equal? (λ () (type-infer (parse '{{lambda {x} x} 1}) empty (set) 0))
                       (λ () (values (VarT 2)
                                     (set (Pair (ArrowT (VarT 1) (VarT 1)) (ArrowT (NumT) (VarT 2))))
                                     2)))
  
  (check-values-equal? (λ () (type-infer (parse '{{lambda {f} {f 0}} {lambda {x} x}}) empty (set) 0))
                       (λ () (values (VarT 4)
                                     (set (Pair (ArrowT (VarT 1) (VarT 2))
                                                (ArrowT (ArrowT (VarT 3) (VarT 3)) (VarT 4)))
                                          (Pair (VarT 1) (ArrowT (NumT) (VarT 2))))
                                     4)))

  (check-equal? (typecheck (parse '{{lambda {f} {f 0}} {lambda {x} x}}) mt-tenv)
                (NumT))

  (check-equal? (typecheck (parse '{lambda {x} {lambda {y} {+ x y}}}) mt-tenv)
                (ArrowT (NumT) (ArrowT (NumT) (NumT))))

  (check-equal? (run '{{{lambda {x} {lambda {y} {+ x y}}} 3} 7})
                (NumV 10))

  (check-exn exn:fail? (λ () (run '{{lambda {x} {x x}} {lambda {x} {x x}}})))

  (check-exn exn:fail? (λ () (run '{+ 3 true})))
  )