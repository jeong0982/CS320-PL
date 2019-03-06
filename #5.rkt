#lang plai

;; BFAE abstract syntax trees
(define-type BFAE
  [num  (num number?)]
  [add  (left BFAE?) (right BFAE?)]
  [sub  (left BFAE?) (right BFAE?)]
  [id   (name symbol?)]
  [fun  (param symbol?) (body BFAE?)]
  [app  (ftn BFAE?) (arg BFAE?)]
  [newbox (value BFAE?)]
  [setbox (box BFAE?) (value BFAE?)]
  [openbox (box BFAE?)]
  [seqn (fe BFAE?) (re list?)]
  [rec (sets (listof list?))]
  [get (field BFAE?) (name id?)]
  [setrec (field BFAE?) (name id?) (val BFAE?)]
  )

;; BFAE Values
(define-type BFAE-Value
  [numV (n number?)]
  [closureV (param symbol?) (body BFAE?) (ds DefrdSub?)]
  [boxV (address integer?)]
  [recV (record list?)])
;;record
(define-type relement
  [element (name id?) (address integer?)])
;; DefrdSub
(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?) (value BFAE-Value?) (ds DefrdSub?)])
;; Store
(define-type Store
  [mtSto]
  [aSto (address integer?) (value BFAE-Value?) (rest Store?)])
;; Value*Store
(define-type Value*Store
  [v*s (value BFAE-Value?) (store Store?)])

; lookup : symbol DefrdSub -> number
(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free identifier")]
    [aSub (x val rest)
          (if (symbol=? x name)
              val
              (lookup name rest))]))
; store-lookup : integer store -> BFAE-Value
(define (store-lookup address st)
  (type-case Store st
    [mtSto () (error "unallocated")]
    [aSto (a v r) (if (= a address) v (store-lookup address r))]))

;; lookup-rec : list-of-relement id -> integer
(define (lookup-rec record name)
  (cond
    [(empty? record) (error 'lookup-rec "no such field : ~a" (id-name name))]
    [(symbol=? (id-name name) (id-name (element-name (first record)))) (element-address (first record))]
    [else (lookup-rec (rest record) name)]))

;;num-op
(define (num-op op)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))

(define num+ (num-op +))
(define num- (num-op -))

; make : (symbol, sexpr) -> (id, BFAE)
;; to make record
(define (make l)
  (cond
    [(= 2 (length l)) (list (parse-sexpr (first l)) (parse-sexpr (second l)))]
    [else (error "it's not 2 element list")]))

;mre : list-of-(<id>, <BFAE>) DefrdSub Store list-of-symbol -> list-of-relement
(define (mre r ds st ids)
  (cond
    [(empty? r) (list st)]
    [else (local [(define f (first r))]
            (cond
              [(= (length ids) (length (remove-duplicates (append (list (id-name (first f))) ids)))) (error "duplicate fields")]
              [else (type-case Value*Store (interp (second f) ds st)
                      [v*s (val1 st1) (local [(define p (malloc st1))]
                                        (append (list (element (first f) p))
                                                (mre (rest r) ds (aSto p val1 st1) (append (list (id-name (first f))) ids))))])]))]))


; parse-sexpr : sexpr -> BFAE
;; to convert s-expressions into BFAEs
(define (parse-sexpr sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(list '+ l r) (add (parse-sexpr l) (parse-sexpr r))]
    [(list '- l r) (sub (parse-sexpr l) (parse-sexpr r))]
    [(? symbol?) (id sexp)]
    [(list 'fun (list p) b) (fun p (parse-sexpr b))]
    [(list 'newbox v) (newbox (parse-sexpr v))]
    [(list 'setbox b v) (setbox (parse-sexpr b) (parse-sexpr v))]
    [(list 'openbox b) (openbox (parse-sexpr b))]
    [(list 'seqn f r ...) (seqn (parse-sexpr f) (map parse-sexpr r))]
    [(list 'rec l ...) (rec (map make l))]
    [(list 'get r n) (get (parse-sexpr r) (parse-sexpr n))]
    [(list 'set r n v) (setrec (parse-sexpr r) (parse-sexpr n) (parse-sexpr v))]
    [(list f a) (app (parse-sexpr f) (parse-sexpr a))]
    [else (error 'parse "bad syntax: ~a" sexp)]))

;; parses a string containing a WAE expression to a WAE AST
(define (parse str)
  (parse-sexpr str))

; malloc : Store -> integer
(define (malloc st)
  (+ 1 (max-address st)))

; max-address : Store -> integer
(define (max-address st)
  (type-case Store st
    [mtSto () 0]
    [aSto (n v st)
          (max n (max-address st))]))

; rep : number Store -> Store
;; replace value
(define (rep ad nval st)
  (type-case Store st
    [mtSto () (error "bad address")]
    [aSto (oad v rst) (if (= ad oad) (aSto ad nval rst) (aSto oad v (rep ad nval rst)))]))



; interp-two : BFAE BFAE DefrdSub Store
; (Value Value Store -> Value*Store)
; -> Value*Store
(define (interp-two expr1 expr2 ds st handle)
  (type-case Value*Store (interp expr1 ds st)
    [v*s (val1 st2)
         (type-case Value*Store (interp expr2 ds st2)
           [v*s (val2 st3)
                (handle val1 val2 st3)])]))

; interp-seqn : BFAE list-of-BFAE DefrdSub Store -> Value*Store
(define (interp-seqn fe oe ds st)
  (type-case Value*Store (interp fe ds st)
    [v*s (v s) (cond
                 [(empty? oe) (v*s v s)]
                 [(empty? (rest oe)) (interp (first oe) ds s)]
                 [else (interp-seqn (first oe) (rest oe) ds s)])]))

;; interprets BFAE expressions and make Value*Store
(define (interp expr ds st)
  (type-case BFAE expr
    [num (n) (v*s (numV n) st)]
    [add (l r) (interp-two l r ds st (lambda (v1 v2 st1) (v*s (num+ v1 v2) st1)))]
    [sub (l r) (interp-two l r ds st (lambda (v1 v2 st1) (v*s (num- v1 v2) st1)))]
    [id  (s)  (v*s (lookup s ds) st)]
    [fun (x b) (v*s (closureV x b ds) st)]
    [app (f a) (interp-two f a ds st
                           (lambda (val1 val2 st1) (type-case Value*Store (interp (closureV-body val1) (aSub (closureV-param val1) val2 (closureV-ds val1)) st1)
                                                               [v*s (fun-val st2) (v*s fun-val st2)])))]
    [newbox (val)
            (type-case Value*Store (interp val ds st)
              [v*s (v1 st1)
                   (local [(define a (malloc st1))]
                     (v*s (boxV a)
                          (aSto a v1 st1)))])]
    [openbox (b)
             (type-case Value*Store (interp b ds st)
               [v*s (bx-val st1)
                    (v*s (store-lookup (boxV-address bx-val)
                                       st1)
                         st1)])]
    [setbox (b v) (interp-two b v ds st (lambda (v1 v2 st) (v*s v2 (rep (boxV-address v1) v2 st))))]
    [seqn (fe se) (interp-seqn fe se ds st)]
    [rec (r) (cond
               [(empty? r) (v*s (recV empty) st)]
               [else (local [(define e (mre r ds st empty))]
                       (v*s (recV (drop-right e 1)) (first (list (last e)))))])]
    [get (f n) (type-case Value*Store (interp f ds st)
                 [v*s (v s) (v*s (store-lookup (lookup-rec (recV-record v) n) s) s)])]
    [setrec (f n v) (type-case Value*Store (interp f ds st)
                      [v*s (v1 s1) (local [(define i (lookup-rec (recV-record v1) n))]
                                   (type-case Value*Store (interp v ds s1)
                                     [v*s (v2 s2) (v*s v2 (rep i v2 s2))]))])]))

; interp-expr
(define (interp-expr e)
  (type-case Value*Store (interp e (mtSub) (mtSto))
    [v*s (v s) (represent v)]))
; represent
;; represent its value
(define (represent v)
  (type-case BFAE-Value v
    [numV (n) n]
    [closureV (p d s) 'func]
    [boxV (a) 'box]
    [recV (d) 'record]))
          
                    
                    
;; my-tests
(test (store-lookup 1 (aSto 2 (numV 1) (aSto 1 (numV 2) (mtSto)))) (numV 2))
(test/exn (store-lookup 100 (aSto 0 (boxV 0) (mtSto))) "unallocated")
(test (lookup-rec (list (element (id 'a) 0) (element (id 'b) 1)) (id 'y)) 1)
(test/exn (lookup-rec (list (element (id 'k) 0) (element (id 'l) 1)) (id 'a)) "no such field")
(test (interp-expr (parse '{set {rec {x 1} {a 3} {w 9} {q 42}} q 5252})) 5252)
(test (interp-expr (parse '{{fun {r}
                                 {get r a}}
                            {rec {x 1} {a 42} {b 0}}}))42)
(test (interp-expr (parse '{fun {a} a})) 'func)