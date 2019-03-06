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
;-------------------------------------------------------------------
(define-type KCFAE
  [num (n number?)]
  [add (lhs KCFAE?)
       (rhs KCFAE?)]
  [sub (lhs KCFAE?)
       (rhs KCFAE?)]
  [id (name symbol?)]
  [fun (param list?)
       (body KCFAE?)]
  [app (fun-expr KCFAE?)
       (arg-expr list?)]
  [if0 (test KCFAE?)
       (then KCFAE?)
       (else KCFAE?)]
  [withcc (name symbol?)
          (body KCFAE?)]
  [trycatch (try KCFAE?)
             (catch KCFAE?)]
  [throw])

(define-type KCFAE-Value
  [numV (n number?)]
  [closureV (param list?)
            (body KCFAE?)
            (ds DefrdSub?)]
  [contV (proc procedure?)])

(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?)
        (value KCFAE-Value?)
        (rest DefrdSub?)])

;; ----------------------------------------

;; parse : S-expr -> KCFAE
(define (parse sexp)
  (cond
    [(number? sexp) (num sexp)]
    [(symbol? sexp) (id sexp)]
    [(pair? sexp)
     (case (car sexp)
       [(+) (add (parse (second sexp)) (parse (third sexp)))]
       [(-) (sub (parse (second sexp)) (parse (third sexp)))]
       [(fun) (fun (map parse (second sexp)) (parse (third sexp)))]
       [(if0) (if0 (parse (second sexp))
                   (parse (third sexp))
                   (parse (fourth sexp)))]
       [(withcc) (withcc (second sexp) (parse (third sexp)))]
       [(try) (trycatch (parse (second sexp)) (parse (fourth sexp)))]
       [(throw) (if (= (length sexp) 1)
                    (throw)
                    (error 'parse "throw is not symbol"))]
       [else (app (parse (first sexp)) (map parse (rest sexp)))])]))
;; ----------------------------------------

;;ia : dfrSub dfrSub list-of-id
;;interp arg
(define (ia param arg ds fun-ds k exk uarg)
  (if (null? arg)
      (dsf param uarg fun-ds k)
      (interp (first arg)
              ds
              (lambda (aarg)
                (ia ds fun-ds param (rest arg) k exk
                            (append uarg (list aarg)))) exk)))

;;dsf
(define (dsf param arg nds k)
  (cond
    [(null? arg) (k nds)]
    [else (dsf (rest param) (rest arg) (aSub (id-name (first param)) (first arg) nds) k)]))

;; interp : KCFAE DefrdSub (KCFAE-Value -> alpha) -> alpha
(define (interp a-fae ds k exk)
  (type-case KCFAE a-fae
    [num (n) (k (numV n))]
    [add (l r) (interp l ds
                       (lambda (v1)
                         (interp r ds
                                 (lambda (v2)
                                   (k (num+ v1 v2)))
                                 exk))exk)]
    [sub (l r) (interp l ds
                       (lambda (v1)
                         (interp r ds
                                 (lambda (v2)
                                   (k (num- v1 v2)))
                                 exk))exk)]
    [id (name) (k (lookup name ds))]
    [fun (param body-expr)
         (k (closureV param body-expr ds))]
    [app (fun-expr arg-expr)
         (interp fun-expr ds
                 (lambda (fun-val)
                   (type-case KCFAE-Value fun-val
                     [closureV (param body ds1)
                               (if (= (length param) (length arg-expr))
                                   (ia param arg-expr ds ds1 (lambda (nds) (interp body nds k exk)) exk empty)
                                   (error "wrong arity"))]
                     [contV (nk)
                            (if (= 1 (length arg-expr))
                                (interp (first arg-expr) ds (lambda (val) (nk val)) exk)
                                (error "continuation"))]
                     [else (error 'interp "not a function")]))
                 exk)]
    [if0 (test-expr then-expr else-expr)
         (interp test-expr ds
                 (lambda (v)
                   (if (numzero? v)
                       (interp then-expr ds k exk)
                       (interp else-expr ds k exk)))exk)]
    [withcc (id body-expr)
            (interp body-expr 
                    (aSub id
                          (contV k)
                          ds)
                    k exk)]
    [trycatch (try-expr catch-expr) (interp try-expr ds k (lambda () (interp catch-expr ds k exk)))]
    [throw () (exk)]))

;; num-op : (number number -> number) -> (KCFAE-Value KCFAE-Value -> KCFAE-Value)
(define (num-op op op-name)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))

(define num+ (num-op + '+))
(define num- (num-op - '-))

;; numzero? : KCFAE-Value -> boolean
(define (numzero? x)
  (zero? (numV-n x)))

(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub (sub-name num rest-sc)
          (if (symbol=? sub-name name)
              num
              (lookup name rest-sc))]))

(test/exn (lookup 'x (mtSub)) "free variable")
(test (lookup 'x (aSub 'x (numV 9) (mtSub))) (numV 9))
(test (lookup 'x (aSub 'y (numV 10) (aSub 'x (numV 9) (mtSub)))) (numV 9))

;; interp-expr : KCFAE -> KCFAE-Value
(define (interp-expr a-fae)
  (type-case KCFAE-Value a-fae
    [numV (n) n]
    [closureV (param body ds) 'function]
    [contV (k) 'function]))

;; run : string -> number or symbol
(define (run str)
  (interp-expr (interp (parse (string->sexpr str))
                       (mtSub)
                       identity (lambda () (error "exception")))))

;;my-test
(test (parse '{throw}) (throw))
(test/exn (parse '{throw 4 2}) "throw is not symbol")
(test (run "{try {throw} catch {+ 2 4}}") 6)
(test (run "{fun {} 1}") 'function)
(test (ia (list (id 'x))
          (list (app (id 'x) (list (throw) (num 4))))
          (aSub 'x (closureV (list (id 'x) (id 'y)) (trycatch (id 'x) (id 'y)) (mtSub)) (mtSub))
          (mtSub)
          identity
          (lambda () (numV 42))
          empty)
      (numV 42))

