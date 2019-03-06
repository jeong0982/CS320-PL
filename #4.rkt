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

(test/exn (string->sexpr 1) "expects argument of type <string>")
(test/exn (string->sexpr ".") "syntax error (bad contents)")
(test/exn (string->sexpr "{} {}") "bad syntax (multiple expressions)")

;; FWAE abstract syntax trees
(define-type FWAE
  [num  (num number?)]
  [add  (left FWAE?) (right FWAE?)]
  [sub  (left FWAE?) (right FWAE?)]
  [with (name symbol?) (init FWAE?) (body FWAE?)]
  [id   (name symbol?)]
  [fun  (param (listof symbol?)) (body FWAE?)]
  [app  (ftn FWAE?) (arg (listof FWAE?))]
  [record (sets (listof list?))]
  [access (field FWAE?) (name symbol?)])

;; FWAE Values
(define-type FWAE-Value
  [numV (n number?)]
  [closureV (param (listof symbol?)) (body FWAE?) (ds DefrdSub?)]
  [recV (ds DefrdSub?)]
   )

(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?) (value FWAE-Value?) (ds DefrdSub?)])

; lookup : symbol DefrdSub -> number
(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free identifier")]
    [aSub (x val rest)
          (if (symbol=? x name)
              val
              (lookup name rest))]))

;;num-op
(define (num-op op)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))

(define num+ (num-op +))
(define num- (num-op -))

; parse-sexpr : sexpr -> FWAE
;; to convert s-expressions into FWAEs
(define (parse-sexpr sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(list '+ l r) (add (parse-sexpr l) (parse-sexpr r))]
    [(list '- l r) (sub (parse-sexpr l) (parse-sexpr r))]
    [(list 'with (list x i) b) (with x (parse-sexpr i) (parse-sexpr b))]
    [(? symbol?) (id sexp)]
    [(list 'fun p b)(if (check-duplicates p)
                        (error 'parse "bad syntax: ~a" p)
                        (fun p (parse-sexpr b)))]
    [(list 'access f n) (access (parse-sexpr f) n)]
    [(? list?) (cond
                      [(equal? (first sexp) 'record) (record (rest sexp))]
                      [else (app (parse-sexpr (first sexp)) (map parse-sexpr (rest sexp)))])]
    [else (error 'parse "bad syntax: ~a" sexp)]))

;; parses a string containing a WAE expression to a WAE AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))

;; make aSub recursively
;; list list -> DefrdSub
(define (make par arg ds)
  (cond
    [(and (empty? par) (empty? arg)) ds]
    [(and (or (empty? par) (empty? arg)) (not (and (empty? par) (empty? arg)))) (error "wrong arity")]
    [else (aSub (first par) (first arg) (make (rest par) (rest arg) ds))]))

;; make ds
;; list DefrdSub DefrdSub -> DefrdSub
(define (mds s ds ss)
  (cond
    [(empty? s) (mtSub)]
    [else(cond
           [(look s ss) (aSub (first(first s)) (interp (parse-sexpr (second (first s))) ds)
                (mds (rest s) ds (aSub (first(first s)) (interp (parse-sexpr (second (first s))) ds) ss )))]
           [else (error "duplicate fields")])]))

(define (look s ss)
  (type-case DefrdSub ss
    [mtSub () #t]
    [aSub (n v d)
          (if (symbol=? (first(first s)) n)
              #f
              (look s d))]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; list for arguments
;; list DefrdSub -> list
(define (arl arg ds)
  (cond
    [(empty? arg) empty]
    [else (cons (interp (first arg) ds) (arl (rest arg) ds))]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; find
;; FWAE-Value DefrdSub -> FWAE-Value
(define (findrecV r c)
  (type-case FWAE-Value r
    [numV (n) (error "not record")]
    [closureV (p b d)(error "not record")]
    [recV (s)(findV s c)]))
;; find value
;; DefrdSub symbol -> FWAE-Value
(define (findV s c)
  (type-case DefrdSub s
    [mtSub () (error "no such field")]
    [aSub (n v d) (cond
                    [(equal? n c) v]
                    [else (findV d c)])]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; interprets FWAE expressions by reducing them to Values
(define (interp expr ds)
  (type-case FWAE expr
    [num (n) (numV n)]
    [add (l r) (num+ (interp l ds) (interp r ds))]
    [sub (l r) (num- (interp l ds) (interp r ds))]
    [with (x i b) (interp b (aSub x (interp i ds) ds))]
    [id  (s)  (lookup s ds)]
    [fun (x b) (closureV x b ds)]
    [app (f a) (local [(define f-val (interp f ds))
                       (define a-val (arl a ds))]
                 (interp (closureV-body f-val)
                         (make (closureV-param f-val) a-val (closureV-ds f-val))
                         ))]
    [record (s) (recV (mds s ds (mtSub)))]
    [access (r c) (findrecV (interp r ds) c)]))

; run : string -> listof number
;; evaluate a FWAE program contained in a string
(define (run str)
  (type-case FWAE-Value (interp (parse str) (mtSub))
    [numV (n) n]
    [closureV (p d s) 'function]
    [recV (d) 'record]))

;; my-tests
(test (run "{fun {x y} {+ x y}}") 'function)
(test (length (arl (list (num 1) (num 2)) (mtSub)))2)
(test (first (closureV-param (interp (fun '(x y) (add (id 'x) (id 'y))) (mtSub)))) 'x)
(test/exn (run "{with {f {fun {x y} {+ x y}}} {f 1 2 3}}") "wrong arity")
(test/exn (run "{with {f {fun {x x} {+ x x}}} {f 1 2}}") "bad syntax")
(test/exn (run "{with {f {fun {x y z} {+ x y}}} {f 1 2}}") "wrong arity")
(test (run "{record {a 10} {b {+ 1 2}} {c {+ 1 4}}}") 'record)
(test/exn (run "{access {record {a 10} {a {+ 1 2}}} b}")
          "duplicate fields")
(test (run "{with {f {fun {a b c} {record {a b} {b c} {c a}}}}
                  {access {f 1 2 3} b}}") 3)
(test/exn (run "{access {record {x {+ 2 5}} {y {+ 1 2}}} a}")
          "no such field")
(test (run "{access {access {record {x {record {y 5252}}}} x} y}") 5252)