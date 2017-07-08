#lang racket

(provide type-error)

(define type-error
  (case-lambda
    [(msg) (error 'type-error "type error: ~a" msg)]
    [(e ty) (error 'type-error "~a should has type: ~a" e ty)]))