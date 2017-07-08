#lang racket

(provide type-error
         make-lookup)

(define type-error
  (case-lambda
    [(msg) (error 'type-error "type error: ~a" msg)]
    [(e ty) (error 'type-error "~a should has type: ~a" e ty)]))

(define (make-lookup error-hint isa? name-of val-of)
  (λ (name vals)
    (cond [(empty? vals) (error error-hint "free variable: ~a" name)]
          [(and (isa? (first vals))
                (equal? name (name-of (first vals))))
           (val-of (first vals))]
          [else ((make-lookup error-hint isa? name-of val-of) name (rest vals))])))
