#lang plai
(require (for-syntax racket/base) racket/match racket/list racket/string
         (only-in mzlib/string read-from-string-all))

;; build a regexp that matches restricted character expressions, can use only
;; {}s for lists, and limited strings that use '...' (normal racket escapes
;; like \n, and '' for a single ')
(define good-char "(?:[ \t\r\na-zA-Z0-9_{}!?*/<=>:+-]|[.][.][.])")
;; this would make it awkward for students to use \" for strings
;; (define good-string "\"[^\"\\]*(?:\\\\.[^\"\\]*)*\"")
(define good-string "[^\"\\']*(?:''[^\"\\']*)*")
(define expr-re
  (regexp (string-append "^"
                         good-char"*"
                         "(?:'"good-string"'"good-char"*)*"
                         "$")))
(define string-re
  (regexp (string-append "'("good-string")'")))

(define (string->sexpr str)
  (unless (string? str)
    (error 'string->sexpr "expects argument of type <string>"))
    (unless (regexp-match expr-re str)
      (error 'string->sexpr "syntax error (bad contents)"))
    (let ([sexprs (read-from-string-all
                 (regexp-replace*
                  "''" (regexp-replace* string-re str "\"\\1\"") "'"))])
    (if (= 1 (length sexprs))
      (car sexprs)
      (error 'string->sexpr "bad syntax (multiple expressions)"))))

;; MUWAE abstract syntax trees
(define-type MUWAE
  [num  (num list?)]
  [add  (left MUWAE?) (right MUWAE?)]
  [sub  (left MUWAE?) (right MUWAE?)]
  [with (name symbol?) (init MUWAE?) (body MUWAE?)]
  [id   (name symbol?)]
  [minimum (first MUWAE?) (second MUWAE?) (third MUWAE?)]
  [maximum (first MUWAE?) (second MUWAE?) (third MUWAE?)])

;bin-op : (number number -> number) (listof number) (listof number) -> (listof number)
;; applies a binary numeric function on all combinations of numbers from
;; the two input lists, and return the list of all of the results
(define (bin-op op ls rs)
  (define (helper l rs)
    (cond
      [(symbol=? op '+) (map (lambda (n) (+ l n)) rs)]
      [(symbol=? op '-) (map (lambda (n) (- l n)) rs)]
    ))
  (if (null? ls)
    null
    (append (helper (first ls) rs) (bin-op op (rest ls) rs))))
  

; parse-sexpr : sexpr -> MUWAE
;; to convert s-expressions into WAEs
(define (parse-sexpr sexp)
  (match sexp
    [(? number?) (num (list sexp))]
    [(? (listof number?)) (num sexp)]
    [(list '+ l r) (add (parse-sexpr l) (parse-sexpr r))]
    [(list '- l r) (sub (parse-sexpr l) (parse-sexpr r))]
    [(list 'with (list x i) b) (with x (parse-sexpr i) (parse-sexpr b))]
    [(? symbol?) (id sexp)]
    [(list 'muwae-min f s t) (minimum(parse-sexpr f)(parse-sexpr s)(parse-sexpr t))]
    [(list 'muwae-max f s t) (maximum(parse-sexpr f)(parse-sexpr s)(parse-sexpr t))]
    [else (error 'parse "bad syntax: ~a" sexp)]))

;; parses a string containing a MUWAE expression to a MUWAE AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))

;; substitutes the second argument with the third argument in the
;; first argument, as per the rules of substitution; the resulting
;; expression contains no free instances of the second argument
(define (subst expr from to)
  (type-case MUWAE expr
    [num (n)   expr]
    [add (l r) (add (subst l from to) (subst r from to))]
    [sub (l r) (sub (subst l from to) (subst r from to))]
    [id (name) (if (symbol=? name from) (num to) expr)]
    [with (bound-id named-expr bound-body)
          (with bound-id
                (subst named-expr from to)
                (if (symbol=? bound-id from)
                    bound-body
                    (subst bound-body from to)))]
    [minimum (f s t) (minimum (subst f from to) (subst s from to) (subst t from to))]
    [maximum (f s t) (maximum (subst f from to) (subst s from to) (subst t from to))]
     ))

;eval : MUWAE -> list of number
;; evaluates MUWAE expressions by reducing them to numbers
(define (eval expr)
  (type-case MUWAE expr
    [num (n) n]
    [add (l r) (bin-op '+ (eval l) (eval r))]
    [sub (l r) (bin-op '- (eval l) (eval r))]
    [with (bound-id named-expr bound-body)
          (eval (subst bound-body
                       bound-id
                       (eval named-expr)))]
    [id (name) (error 'eval "free identifier: ~s" name)]
    [minimum (f s t) (list (first (sort  (append (eval f) (eval s) (eval t)) < )))]
    [maximum (f s t) (list (first (sort  (append (eval f) (eval s) (eval t)) > )))]
             ))

; run : string -> list of number
;; evaluate a MUWAE program contained in a string
(define (run str)
  (eval (parse str)))

;my-tests
(test (run "{+ {1 2 3} {3 4 5}}") '(4 5 6 5 6 7 6 7 8))
(test (run "{+ 3 {7 3}}") '(10 6))
(test (run "{with {x { 5 5}} {+ x x}}") '(10 10 10 10))
(test/exn (run "{x}") "bad syntax")
(test (run "{+ {muwae-max 3 5 7} {muwae-min 10 100 1000}}") '(17))
(test (run "{with {x 19} {muwae-max x 2 3}}") '(19))
(test (run "{with {x {muwae-min 3 9 5}} {with {y {- x 3}} y}}") '(0))
(test (run "{with {x {muwae-max 2 3 5}} {muwae-min x 7 6}}") '(5))
(test (run "{3939}") '(3939))
(test (run "98") '(98))
(test (run "{+ 1 {muwae-max 1 2 {muwae-min 6 7 8}}}") '(7))