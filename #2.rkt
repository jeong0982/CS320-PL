#lang plai
;define WAE
(define-type WAE
  [num (n number?)]
  [add (lhs WAE?) (rhs WAE?)]
  [sub (lhs WAE?) (rhs WAE?)]
  [with (name symbol?)
        (named-expr WAE?)
        (body WAE?)]
  [id (name symbol?)])
;symbol<?: symbol symbol -> boolean
(define (symbol<? a b)
  (string<? (symbol->string a) (symbol->string b)))
;make-list-free: WAE-> list-of-sym
(define (make-list-free wae)
  (type-case WAE wae
    (num (n) empty)
    (add (l r) (append (make-list-free l) (make-list-free r)))
    (sub (l r) (append (make-list-free l) (make-list-free r)))
    (with (n ne b) (append (make-list-free ne) (remove* (list n)(make-list-free b))))
    (id (n) (cons n empty))))
;free-ids: WAE -> list-of-sym
(define (free-ids wae)
  (remove-duplicates(sort (make-list-free wae) symbol<?)))
;make-list-bindings: WAE-> list-of-sym
(define (make-list-binding wae)
  (type-case WAE wae
    (num (n) empty)
    (add (l r) (append (make-list-binding l) (make-list-binding r)))
    (sub (l r) (append (make-list-binding l) (make-list-binding r)))
    (with (n ne b) (cons n (append (make-list-binding ne) (make-list-binding b))))
    (id (n) empty)))
;binding-ids: WAE -> list-of-sym
(define (binding-ids wae)
  (remove-duplicates(sort (make-list-binding wae) symbol<?)))
;make-list-bound: WAE-> list-of-sym
(define (make-list-bound wae)
  (type-case WAE wae
    (num (n) empty)
    (add (l r) (append(make-list-bound l) (make-list-bound r)))
    (sub (l r) (append(make-list-bound l) (make-list-bound r)))
    (with (n ne b) (append (filter (lambda (arg) (symbol=? arg n)) (make-list-free b)) (make-list-bound ne) (make-list-bound b))) 
    (id (n) empty)))
;bound-ids: WAE -> list-of-sym
(define (bound-ids wae)
  (remove-duplicates(sort (make-list-bound wae) symbol<?)))