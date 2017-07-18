#lang racket

;; Simply Typed Lamdba Calculus with Record and Subtyping
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

(struct RecordE (ns es) #:transparent)
(struct GetE (rec n) #:transparent)
(struct SetE (rec n val) #:transparent)

;; Types

(struct NumT () #:transparent)
(struct BoolT () #:transparent)
(struct ArrowT (arg res) #:transparent)
(struct RecordT (ns ts) #:transparent)

;; Values

(struct NumV (n) #:transparent)
(struct BoolV (b) #:transparent)
(struct RecordV (ns vs) #:transparent)
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
    [`(rec {,ns : ,vs} ...)
     (RecordE ns (map parse vs))]
    [`(get ,rec ,n)
     (GetE (parse rec) n)]
    [`(set ,rec ,n ,val)
     (SetE (parse rec) n (parse val))]
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
    [`((,ns : ,ts) ...) (RecordT ns (map parse-type ts))]
    [`(,tyarg -> ,tyres) (ArrowT (parse-type tyarg) (parse-type tyres))]
    [else (error 'parse-type "invalid type")]))

;; Type Checker

(define (typecheck-nums l r tenv)
  (match* ((typecheck l tenv) (typecheck r tenv))
    [((NumT) (NumT)) (NumT)]
    [(_ _) (type-error "not number")]))

(define (record-find n ns ts)
  (cond [(empty? ns) (error 'find "can not find")]
        [else (if (symbol=? n (first ns)) (first ts)
                  (record-find n (rest ns) (rest ts)))]))

;; is t1 a subtype of t2?
(define (subtype? t1 t2)
  (match* (t1 t2)
    [((NumT) (NumT)) #t]
    [((NumT) _) #f]
    [((BoolT) (BoolT)) #t]
    [((BoolT) _) #f]
    [((ArrowT l1 r1) (ArrowT l2 r2))
     (and (subtype? l2 l1)   ;contra-variant
          (subtype? r1 r2))] ;co-variant
    [((ArrowT _ _) _) #f]
    [((RecordT ns1 ts1) (RecordT ns2 ts2))
     ; every field in ns2 must be in ns1 and types in
     ; ts1 should be a subtype of the one in ts2
     (andmap (λ (n) (and (member n ns1)
                         (subtype? (record-find n ns1 ts1)
                                   (record-find n ns2 ts2))))
             ns2)]
    [((RecordT _ _) _) #f]
    [(_ _) #f]))

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
        (if (subtype? (typecheck arg tenv) atype) rtype
            (type-error "argument types not agree"))]
       [_ (type-error "not a function")])]
    [(RecordE ns es)
     (RecordT ns (map (λ (e) (typecheck e tenv)) es))]
    [(GetE rec n)
     (match (typecheck rec tenv)
       [(RecordT ns ts) (record-find n ns ts)]
       [else (type-error "not a record")])]
    [(SetE rec n val)
     (define rec-type (typecheck rec tenv))
     (match rec-type
       [(RecordT ns ts)
        (define field-type (record-find n ns ts))
        (if (subtype? (typecheck val tenv) field-type)
            rec-type
            (type-error "should be subtype of field"))]
       [_ (type-error "not a record")])]))

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
    [(AppE fun arg)
     (match (interp fun env)
       [(ClosureV n body env*)
        (interp body (ext-env (Binding n (interp arg env)) env*))])]
    [(RecordE ns es)
     (RecordV ns (map (λ (e) (box (interp e env))) es))]
    [(GetE rec n)
     (define rec-v (interp rec env))
     (unbox (record-find n (RecordV-ns rec-v) (RecordV-vs rec-v)))]
    [(SetE rec n v)
     (define rec-v (interp rec env))
     (set-box! (record-find n (RecordV-ns rec-v) (RecordV-vs rec-v))
               (interp v env))
     rec-v]
    [(IfE cnd thn els)
     (match (interp cnd env)
       [(BoolV #t) (interp thn env)]
       [(BoolV #f) (interp els env)])]))

(define mt-env empty)
(define mt-tenv empty)

(define (run prog)
  (define prog* (parse prog))
  (typecheck prog* mt-tenv)
  (interp prog* mt-env))

;; Tests

(module+ test
  (check-equal? (parse-type '{{x : num} {y : num}})
                (RecordT '(x y) (list (NumT) (NumT))))
  (check-equal? (parse-type '{{x : {num -> num}}
                              {y : {bool -> bool}}})
                (RecordT '(x y) (list (ArrowT (NumT) (NumT))
                                      (ArrowT (BoolT) (BoolT)))))
  
  (check-equal? (parse '{let {[r : {{x : num}} {rec {x : 3}}]}
                          {get r x}})
                (AppE
                 (LamE 'r (RecordT '(x) (list (NumT))) (GetE (IdE 'r) 'x))
                 (RecordE '(x) (list (NumE 3)))))

  (check-equal? (typecheck (parse '{let {[r : {{x : num}} {rec {x : 3}}]}
                                     {get r x}}) mt-tenv)
                (NumT))
  
  (check-true (subtype? (parse-type '{{x : num} {y : num}})
                        (parse-type '{{x : num}})))
  
  (check-true (subtype? (parse-type '{{{x : num}} -> {{x : num} {y : num}}})
                        (parse-type '{{{x : num} {y : num}} -> {{x : num}}})))

  (check-equal? (typecheck (parse '{{lambda {[r : {{x : num}}]} {+ {get r x} 1}}
                                    {rec {x : 3} {y : 4}}})
                           mt-tenv)
                (NumT))

  (check-equal? (typecheck (parse '{{lambda {[r : {{x : num}}]} {+ {get r x} 1}}
                                    {rec {y : true} {x : 4}}})
                           mt-tenv)
                (NumT))

  (check-equal? (interp (parse '{let {[r : {{x : num}} {rec {x : 3}}]}
                                  {get r x}}) mt-env)
                (NumV 3))

  (check-equal? (interp (parse '{{lambda {[r : {{x : num}}]} {+ {get r x} 1}}
                                 {rec {x : 3} {y : 4}}})
                        mt-env)
                (NumV 4))
  
  (check-equal? (interp (parse '{{lambda {[r1 : {{x : num}}]}
                                   {let {[r2 : {{x : num}}
                                             {rec {x : 3}}]}
                                     {set r2 x {+ {get r1 x} {get r2 x}}}}}
                                 {rec {x : 4}}})
                        mt-env)
                (RecordV '(x) (list (box (NumV 7)))))

  )
