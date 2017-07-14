#lang racket

(require (for-syntax syntax/parse)
         rackunit)

(provide type-error
         make-lookup
         check-values-equal?)

(define type-error
  (case-lambda
    [(msg) (error 'type-error "~a" msg)]
    [(e ty) (error 'type-error "~a should has type: ~a" e ty)]))

(define (make-lookup error-hint isa? name-of val-of)
  (λ (name vals)
    (cond [(empty? vals) (error error-hint "free variable: ~a" name)]
          [(and (isa? (first vals))
                (equal? name (name-of (first vals))))
           (val-of (first vals))]
          [else ((make-lookup error-hint isa? name-of val-of) name (rest vals))])))

(define-syntax (check-values-equal? stx)
  (syntax-parse stx
    [(_ v1 v2)
     #'(call-with-values (λ () v1)
                         (λ vlist1 (call-with-values (λ () v2)
                                                     (λ vlist2 (check-true (equal? vlist1 vlist2))))))]))
  
