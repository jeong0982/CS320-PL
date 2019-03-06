#lang plai
; dollar->won: number -> number
; consumes a number of dollars and produces the won equivalent
(define (dollar->won dollar)
  (* dollar 1100))
(test (dollar->won 1) 1100)
;volume-cuboid: number number number -> number
;produces the volume of the cuboid made by three sides' length denoted by integers
(define (volume-cuboid width depth height)
  (* width depth height))
(test (volume-cuboid 1 2 3) 6)
;is-even?: number -> boolean
;to determine whether n is even number
(define (is-even? n)
  (= (remainder n 2) 0))
(test (is-even? -257) false)
;gcd: number number -> number
;to find greatest common divisor of given two integers
(define (gcd n1 n2)
  (cond
   ((= n1 0) n2)
   ((= n2 0) n1)
   ((< n1 n2)(gcd (remainder n2 n1) n1))
   ((> n1 n2)(gcd (remainder n1 n2) n2))))
(test (gcd 36 24) 12)
;lcm: number number -> number
;to find least common multiple of given two integers
(define (lcm n1 n2)
  (/ (* n1 n2) (gcd n1 n2)))
(test (lcm 3 4) 12)

(define-type COURSE
  (CS320 (quiz integer?)
         (homework integer?))
  (CS311 (homework integer?))
  (CS330 (projects integer?)
         (homework integer?)))
;have-homework: course -> number
;produces the number of assignments for the given course
(define (have-homework c)
  (type-case COURSE c
    (CS320 (q h) h)
    (CS311 (h) h)
    (CS330 (p h) h)))
(define class1(CS320 2 5))
(test(have-homework class1) 5 )
;have-projects: course -> boolean
;produces true when the given course is CS330 with more than two projects
(define (have-projects c)
  (type-case COURSE c
    (CS320 (q h) false)
    (CS311 (h) false)
    (CS330 (p h) (cond
           ((< p 2) false)
           (else true)))))
(define class2(CS330 5 5))
(test (have-projects class2) true)
;name-pets: list -> list
;if element of given list is "cat" or "dog" or "pig", give their name
(define (name-pets pets)
  (let([newpet empty])
    (for ((i pets)) (set! newpet (append newpet (cond
                                    ((eq? i 'dog) '(happy))
                                    ((eq? i 'cat) '(smart))
                                    ((eq? i 'pig) '(pinky))
                                    (else (list i))))))newpet))
(test (name-pets '(cat dog pig snake)) '(smart happy pinky snake))
;give-name: symbol symbol list -> list
;consumes two symbols, called old and new, and a list of symbols and produces a list of symbols by replacing all occurrences of old by new.
(define (give-name old new sym)
  (let([newname empty])
    (for ((i sym)) (set! newname (append newname (cond
                                    ((eq? i old)  (list new))
                                    (else (list i))))))newname))
(test(give-name 'bear 'pooh (cons 'pig (cons 'cat (cons 'bear empty)))) '(pig cat pooh))