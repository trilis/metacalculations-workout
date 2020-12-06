#lang racket

(require "utils.rkt")
(require "int.rkt")
(require "mix.rkt")

(define find-name
  '((read name namelist valuelist)
    (search (if (equal? name (car namelist)) found cont))
    (cont (:= valuelist (cdr valuelist)) (:= namelist (cdr namelist)) (goto search))
    (found (return (car valuelist)))
    )
  )

(define tm-example '((0 if 0 goto 3) (1 right) (2 goto 0) (3 write 1)))

(define tm-int-division (list 'Q 'Qtail 'Instruction 'Operator 'Symbol 'NextLabel))
(define fc-int-division (list 'program 'labels 'bb 'command))
(define mix-division (list 'program 'division 'bb 'command 'pp0 'ppx 'blocks-in-pending))

(define fut1-tm (int mix `(,tm-int ,tm-int-division ,(make-immutable-hash (list (cons 'Q (cons 'quote (list tm-example))))))))
(define fut2-tm (int mix `(,mix ,mix-division ,(make-immutable-hash (list (cons 'program (cons 'quote (list tm-int))) (cons 'division (cons 'quote (list tm-int-division))))))))

(define fut1-fc (int mix `(,fc-int ,fc-int-division ,(make-immutable-hash (list (cons 'program (cons 'quote (list find-name))))))))
(define fut2-fc (int mix `(,mix ,mix-division ,(make-immutable-hash (list (cons 'program (cons 'quote (list fc-int))) (cons 'division (cons 'quote (list fc-int-division))))))))

(define fut3 (int mix `(,mix ,mix-division ,(make-immutable-hash (list (cons 'program (cons 'quote (list mix))) (cons 'division (cons 'quote (list mix-division))))))))

(pretty-print-columns 100)

(println "FIRST PROJECTION, TM:")
(pretty-print fut1-tm)

(println "SECOND PROJECTION, TM:")
(pretty-print fut2-tm)

(println "FIRST PROJECTION, FC:")
(pretty-print fut1-fc)

(println "SECOND PROJECTION, FC:")
(pretty-print fut2-fc)

(println "THIRD PROJECTION:")
(pretty-print fut3)

(println "CHECK THAT FIRST PROJECTION GENERATES CORRECT CODE:")
(println (equal? '(1 1 0 1) (int fut1-tm '((1 1 1 0 1 0 1)))))
(println (equal? 'val2 (int fut1-fc '(c (a b c d) (val0 val1 val2 val3)))))

(println "CHECK THAT SECOND PROJECTION GENERATES COMPILER:")
(println (equal? fut1-tm (int fut2-tm `(,(make-immutable-hash (list (cons 'Q (cons 'quote (list tm-example)))))))))
(println (equal? fut1-fc (int fut2-fc `(,(make-immutable-hash (list (cons 'program (cons 'quote (list find-name)))))))))

(println "CHECK THAT THIRD PROJECTION GENERATES COMPGEN:")
(println (equal? fut1-tm (int (int fut3 `(,(make-immutable-hash (list (cons 'program (cons 'quote (list tm-int))) (cons 'division (cons 'quote (list tm-int-division))))))) `(,(make-immutable-hash (list (cons 'Q (cons 'quote (list tm-example)))))))))
(println (equal? fut1-fc (int (int fut3 `(,(make-immutable-hash (list (cons 'program (cons 'quote (list fc-int))) (cons 'division (cons 'quote (list fc-int-division))))))) `(,(make-immutable-hash (list (cons 'program (cons 'quote (list find-name)))))))))
