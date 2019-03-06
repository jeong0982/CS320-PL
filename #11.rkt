
#lang plai-typed

(define-type EXPR
  [num (n : number)]
  [bool (b : boolean)]
  [add (lhs : EXPR) (rhs : EXPR)]
  [sub (lhs : EXPR) (rhs : EXPR)]
  [equ (lhs : EXPR) (rhs : EXPR)]
  [id (name : symbol)]
  [fun (param : symbol) (paramty : TE) (body : EXPR)]
  [app (fun-expr : EXPR) (arg-expr : EXPR)]
  [ifthenelse (test-expr : EXPR) (then-expr : EXPR) (else-expr : EXPR)]
  [rec (name : symbol) (ty : TE) (named-expr : EXPR) (body : EXPR)]
  [with-type (name : symbol)
             (var1-name : symbol) (var1-ty : TE)
             (var2-name : symbol) (var2-ty : TE)
             (body-expr : EXPR)]
  [cases (name : symbol)
         (dispatch-expr : EXPR)
         (var1-name : symbol) (bind1-name : symbol) (rhs1-expr : EXPR)
         (var2-name : symbol) (bind2-name : symbol) (rhs2-expr : EXPR)]
  [tfun (name : symbol) (expr : EXPR)]
  [tapp (body : EXPR) (type : TE)])

(define-type TE
  [numTE]
  [boolTE]
  [arrowTE (param : TE) (result : TE)]
  [polyTE (forall : symbol) (body : TE)]
  [idTE (name : symbol)]
  [tvTE (name : symbol)])

(define-type Type
  [numT]
  [boolT]
  [arrowT (param : Type) (result : Type)]
  [polyT (forall : symbol) (body : Type)]
  [idT (name : symbol)]
  [tvT (name : symbol)])

(define-type EXPR-Value
  [numV (n : number)]
  [boolV (b : boolean)]
  [closureV (param : symbol) (body : EXPR) (ds : DefrdSub)]
  [variantV (right? : boolean) (val : EXPR-Value)]
  [constructorV (right? : boolean)])

(define-type DefrdSub
  [mtSub]
  [aSub (name : symbol) (value : EXPR-Value) (rest : DefrdSub)]
  [aRecSub (name : symbol) (value-box : (boxof EXPR-Value)) (rest : DefrdSub)])

(define-type TypeEnv
  [mtEnv]
  [aBind (name : symbol)
         (type : Type)
         (rest : TypeEnv)]
  [tBind (name : symbol)
         (var1-name : symbol) (var1-type : Type)
         (var2-name : symbol) (var2-type : Type)
         (rest : TypeEnv)])

(define-type TypeList
  [mtList]
  [aList (type : Type) (rest : TypeList)])

(define-type Tvt
  [mtt]
  [at (name : symbol) (type : Type) (rest : Tvt)])

(define-type realt
  [none]
  [some (type : Type)])
;; get-type : symbol TypeEnv -> Type
(define (get-type name-to-find env)
  (type-case TypeEnv env
    [mtEnv () (error 'get-type "free variable, so no type")]
    [aBind (name ty rest) (if (symbol=? name-to-find name)
                              ty
                              (get-type name-to-find rest))]
    [tBind (name var1-name var1-ty var2-name var2-ty rest)
           (get-type name-to-find rest)]))


;; find-type-id : symbol TypeEnv -> TypeEnv
(define (find-type-id name-to-find env)
  (type-case TypeEnv env
    [mtEnv () (error 'get-type "free type name, so no type")]
    [aBind (name ty rest) (find-type-id name-to-find rest)]
    [tBind (name var1-name var1-ty var2-name var2-ty rest)
           (if (symbol=? name-to-find name)
               env
               (find-type-id name-to-find rest))]))

(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub (sub-name val rest-ds) (if (symbol=? sub-name name) val (lookup name rest-ds))]
    [aRecSub (sub-name val-box rest-ds)
             (if (symbol=? sub-name name)
                 (unbox val-box)
                 (lookup name rest-ds))]))

;; type-list: Type TypeList -> Typelist
(define (type-list ty tl)
  (type-case Type ty
    [numT () (aList (numT) tl)]
    [boolT () (aList (boolT) tl)]
    [arrowT (p b) (local [(define p-list (type-list p tl))]
                    (type-list b p-list))]
    [polyT (f b) (aList (tvT f) (type-list b tl))]
    [idT (id) (aList (idT id) tl)]
    [tvT (id) (aList (tvT id) tl)]))

;; parse-type : TE -> Type
(define (parse-type te)
  (type-case TE te
    [numTE () (numT)]
    [boolTE () (boolT)]
    [arrowTE (p r) (arrowT (parse-type p) (parse-type r))]
    [polyTE (f b) (polyT f (parse-type b))]
    [idTE (n) (idT n)]
    [tvTE (n) (tvT n)]))

;; validtype Type TypeEnv -> TypeEnv
(define (validtype ty env)
  (type-case Type ty
    [numT () (mtEnv)]
    [boolT () (mtEnv)]
    [arrowT (a b) (begin (validtype a env)
                         (validtype b env))]
    [polyT (f b) (validtype b (aBind f (tvT f) env))]
    [idT (id) (find-type-id id env)]
    [tvT (id) (type-case Type (get-type id env)
                [tvT (n) (mtEnv)]
                [else (validtype ty (aBind-rest env))])]))

(test (validtype (tvT 'alpha) (aBind 'alpha (arrowT (numT)(numT)) (aBind 'alpha (tvT 'alpha) (mtEnv)))) (mtEnv))
(test/exn (validtype (tvT 'alpha) (aBind 'alpha (arrowT (numT)(numT)) (mtEnv))) "no")

(define (replace-tvT from name with)
  (type-case Type from
    [arrowT (p r) (arrowT (replace-tvT p name with) (replace-tvT r name with))]
    [polyT (f b) (if (symbol=? name f)
                     from
                     (polyT f (replace-tvT b name with)))]
    [tvT (id) (if (symbol=? id name)
                  with
                  from)]
    [else from]))

;; compare-all-type : TypeList TypeList TvLabel TvLabel -> bool
(define (compare-all-type tl1 tl2 tvl1 tvl2)
  (type-case TypeList tl1
    [mtList () (type-case TypeList tl2
                 [mtList () #t]
                 [else #f])]
    [aList (ty1 rest1) (type-case TypeList tl2
                          [mtList () #f]
                          [aList (ty2 rest2) (type-case Type ty1
                                                [numT () (type-case Type ty2
                                                           [numT () (compare-all-type rest1 rest2 tvl1 tvl2)]
                                                           [boolT () #f]
                                                           [idT (id) #f]
                                                           [tvT (id) (local [(define rt (lookup-tv id tvl2))]
                                                                       (type-case realt rt
                                                                         [none () (compare-all-type rest1 rest2 tvl1 (at id (numT) tvl2))]
                                                                         [some (t) (if (numT? t)
                                                                                       (compare-all-type rest1 rest2 tvl1 tvl2)
                                                                                       #f)]))]
                                                           [else (error 'compare-all-type "impossible case!")])]
                                                [boolT () (type-case Type ty2
                                                           [numT () #f]
                                                           [boolT () (compare-all-type rest1 rest2 tvl1 tvl2)]
                                                           [idT (id) #f]
                                                           [tvT (id) (local [(define rt (lookup-tv id tvl2))]
                                                                       (type-case realt rt
                                                                         [none () (compare-all-type rest1 rest2 tvl1 (at id (boolT) tvl2))]
                                                                         [some (t) (if (boolT? t)
                                                                                       (compare-all-type rest1 rest2 tvl1 tvl2)
                                                                                       #f)]))]
                                                           [else (error 'compare-all-type "impossible case!")])]
                                                [idT (id1) (type-case Type ty2
                                                           [numT () #f]
                                                           [boolT () #f]
                                                           [idT (id2) (if (symbol=? id1 id2) #t #f)]
                                                           [tvT (id) (local [(define rt (lookup-tv id tvl2))]
                                                                       (type-case realt rt
                                                                         [none () (compare-all-type rest1 rest2 tvl1 (at id (idT id1) tvl2))]
                                                                         [some (t) (if (and (idT? t) (symbol=? id1 (idT-name t)))
                                                                                       (compare-all-type rest1 rest2 tvl1 tvl2)
                                                                                       #f)]))]
                                                           [else (error 'compare-all-type "impossible case!")])]
                                                [tvT (id1) (type-case Type ty2
                                                           [numT () (local [(define rt (lookup-tv id1 tvl1))]
                                                                       (type-case realt rt
                                                                         [none () (compare-all-type rest1 rest2 (at id1 (numT) tvl1) tvl2)]
                                                                         [some (t) (if (numT? t)
                                                                                       (compare-all-type rest1 rest2 tvl1 tvl2)
                                                                                       #f)]))]
                                                           [boolT () (local [(define rt (lookup-tv id1 tvl1))]
                                                                       (type-case realt rt
                                                                         [none () (compare-all-type rest1 rest2 (at id1 (boolT) tvl1) tvl2)]
                                                                         [some (t) (if (boolT? t)
                                                                                       (compare-all-type rest1 rest2 tvl1 tvl2)
                                                                                       #f)]))]
                                                           [idT (id) (local [(define rt (lookup-tv id1 tvl1))]
                                                                       (type-case realt rt
                                                                         [none () (compare-all-type rest1 rest2 (at id1 (idT id) tvl1) tvl2)]
                                                                         [some (t) (if (and (idT? t) (symbol=? id (idT-name t)))
                                                                                       (compare-all-type rest1 rest2 tvl1 tvl2)
                                                                                       #f)]))]
                                                           [tvT (id2) (local [(define id1-rt (lookup-tv id1 tvl1))
                                                                              (define id2-rt (lookup-tv id2 tvl2))]
                                                                        (type-case realt id1-rt
                                                                          [none () (type-case realt id2-rt
                                                                                     [none () (compare-all-type rest1 rest2 tvl1 tvl2)]
                                                                                     [some (t) (compare-all-type rest1 rest2 (at id1 t tvl1) tvl2)])]
                                                                          [some (t1) (type-case realt id2-rt
                                                                                      [none () (compare-all-type rest1 rest2 tvl1 (at id2 t1 tvl2))]
                                                                                      [some (t2) (if (eqty t1 t2) (compare-all-type rest1 rest2 tvl1 tvl2) #f)])]))]
                                                           [else (error 'compare-all-type "impossible")])]
                                                [else (error 'compare-all-type "impossible")])])]))
(define (lookup-tv name tv)
  (type-case Tvt tv
    [mtt () (none)]
    [at (n t r) (if (symbol=? n name)
                    (some t)
                    (lookup-tv name r))]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;eqty : Type Type -> bool
(define (eqty ty1 ty2)
  (local [(define ty1-list (type-list ty1 (mtList)))
          (define ty2-list (type-list ty2 (mtList)))]
    (compare-all-type ty1-list ty2-list (mtt) (mtt))))


(test (eqty (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))) (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta)))) #t)
(test (eqty (polyT 'alpha (tvT 'alpha)) (polyT 'beta (tvT 'beta))) #t)
(test (eqty (numT) (numT)) #t)
(test (eqty (polyT 'alpha (polyT 'beta (arrowT (tvT 'beta) (tvT 'alpha)))) (polyT 'beta (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'beta))))) #t)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; typecheck : EXPR TypeEnv -> Type
;; to check the given expression has valid type. If does, return the type
(define (typecheck expr env)
    (type-case EXPR expr
      [num (n) (numT)]
      [bool (b) (boolT)]
      [add (l r) (local [(define l-type (typecheck l env))]
                   (type-case Type l-type
                     [numT () (if (eqty l-type (typecheck r env))
                                  l-type
                                  (error 'typecheck "no type"))]
                     [else (error 'typecheck "no type")]))]
      [sub (l r) (local [(define l-type (typecheck l env))]
                   (type-case Type l-type
                     [numT () (if (eqty l-type (typecheck r env))
                                  l-type
                                  (error 'typecheck "no type"))]
                     [else (error 'typecheck "no type")]))]
      [equ (l r) (local [(define l-type (typecheck l env))]
                   (type-case Type l-type
                     [numT () (if (eqty l-type (typecheck r env))
                                  (boolT)
                                  (error 'typecheck "no type"))]
                     [else (error 'typecheck "no type")]))]
      [id (name) (get-type name env)]
      [fun (name te body)
           (local [(define param-type (parse-type te))]
             (begin
               (validtype param-type env)
               (arrowT param-type
                       (typecheck body
                                  (aBind name param-type env)))))]
      [app (fn arg)
           (type-case Type (typecheck fn env)
             [arrowT (param-type result-type)
                   (if (eqty param-type
                                 (typecheck arg env))
                         result-type
                         (error 'typecheck "no type"))]
             [else (error 'typecheck "no type")])]
      [ifthenelse (t l r)
                (type-case Type (typecheck t env)
                  [boolT () (local [(define l-type (typecheck l env))]
                              (if (eqty l-type (typecheck r env))
                                  l-type
                                  (error 'typecheck "no type")))]
                  [else (error 'typecheck "no type")])]
    [rec (name te rhs-expr body-expr) (local [(define ty (parse-type te))
                                              (define new-env (aBind name ty env))]
                                        (if (eqty ty (typecheck rhs-expr new-env))
                                            (typecheck body-expr new-env)
                                            (error 'typecheck "no type")))]
      [with-type (type-name var1-name var1-te var2-name var2-te body-expr)
        (local [(define var1-ty (parse-type var1-te))
                (define var2-ty (parse-type var2-te))
                (define new-env (tBind type-name
                                       var1-name var1-ty
                                       var2-name var2-ty env))]
          (begin
            (validtype var1-ty new-env)
            (validtype var2-ty new-env)
            (typecheck body-expr
                       (aBind var1-name
                              (arrowT var1-ty
                                      (idT type-name))
                              (aBind var2-name
                                     (arrowT var2-ty
                                             (idT type-name))
                                     new-env)))))]
      [cases (type-name dispatch-expr var1-name var1-id var1-rhs
                        var2-name var2-id var2-rhs)
        (local [(define bind (find-type-id type-name env))]
          (if (and (equal? var1-name (tBind-var1-name bind))
                   (equal? var2-name (tBind-var2-name bind)))
              (type-case Type (typecheck dispatch-expr env)
                [idT (name)
                     (if (equal? name type-name)
                         (local [(define rhs1-ty
                                   (typecheck var1-rhs
                                              (aBind var1-id (tBind-var1-type bind) env)))
                                 (define rhs2-ty
                                   (typecheck var2-rhs
                                              (aBind var2-id (tBind-var2-type bind) env)))]
                           (if (eqty rhs1-ty rhs2-ty)
                               rhs1-ty
                               (error 'typecheck "no type")))
                         (error 'typecheck "no type"))]
                [else (error 'typecheck "no type")])
              (error 'typecheck "no type")))]
      [tfun (n e) (polyT n (typecheck e (aBind n (tvT n) env)))]
      [tapp (b te) (local [(define ty (parse-type te))
                         (define b-type (typecheck b env))]
                   (begin
                     (validtype ty env)
                     (type-case Type b-type
                       [polyT (f body) (replace-tvT body f ty)]
                       [else (error 'typecheck "no type")])))]))

(define (interp expr ds)
  (type-case EXPR expr
    [num (n) (numV n)]
    [bool (b) (boolV b)]
    [add (l r) (numV (+ (numV-n (interp l ds)) (numV-n (interp r ds))))]
    [sub (l r) (numV (- (numV-n (interp l ds)) (numV-n (interp r ds))))]
    [equ (l r) (boolV (= (numV-n (interp l ds)) (numV-n (interp r ds))))]
    [id (name) (lookup name ds)]
    [fun (param te body-expr) (closureV param body-expr ds)]
    [app (fun-expr arg-expr)
         (local [(define fun-val (interp fun-expr ds))
                 (define arg-val (interp arg-expr ds))]
           (type-case EXPR-Value fun-val
             [closureV (param body ds) (interp body (aSub param arg-val ds))]
             [constructorV (right?) (variantV right? arg-val)]
             [else (error 'interp "not applicable")]))]
    [ifthenelse (t l r) (if (boolV-b (interp t ds))
                            (interp l ds)
                            (interp r ds))]
    [rec (bound-id type named-expr body-expr)
      (local [(define value-holder (box (numV 42)))
              (define new-ds (aRecSub bound-id value-holder ds))]
        (begin
          (set-box! value-holder (interp named-expr new-ds))
          (interp body-expr new-ds)))]
    [with-type (type-name var1-name var1-te var2-name var2-te body-expr)
      (interp body-expr (aSub var1-name (constructorV false) (aSub var2-name (constructorV true) ds)))]
    [cases (ty dispatch-expr var1-name var1-id var1-rhs var2-name var2-id var2-rhs)
      (type-case EXPR-Value (interp dispatch-expr ds)
        [variantV (right? val) (if (not right?) (interp var1-rhs (aSub var1-id val ds)) (interp var2-rhs (aSub var2-id val ds)))]
        [else (error 'interp "not a variant result")])]
    [tfun (n e) (interp e ds)]
    [tapp (b te) (interp b ds)]))



