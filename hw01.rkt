#lang racket
(define tm-example '((0 if 0 goto 3) (1 right) (2 goto 0) (3 write 1)))

(define car-or-zero
  (lambda (tape)
    (if (empty? tape)
        '0
        (car tape))))

(define cdr-or-empty
  (lambda (tape)
    (if (empty? tape)
        tape
        (cdr tape))))

(define tm-int-internal (lambda (program left right progtail)
                         (match (car progtail)
                            [`(,n if ,cond goto ,newinstr) (tm-int-internal program left right (if (equal? cond (car right)) (list-tail program newinstr) (cdr progtail)))]
                            [`(,n left) (tm-int-internal program (cdr-or-empty left) (cons (car-or-zero left) right) (cdr progtail))]
                            [`(,n right) (tm-int-internal program (cons (car-or-zero right) left) (cdr-or-empty right) (cdr progtail))]
                            [`(,n goto ,newinstr) (tm-int-internal program left right (list-tail program newinstr))]
                            [`(,n write ,x) (tm-int-internal program left (cons x (cdr right)) (cdr progtail))]
                            ['end right]
                            ))
  )

(define tm-int (lambda (program data)
                 (tm-int-internal (append program '(end)) '() data program)
                 ))

(tm-int tm-example '(1 1 1 0 1 0 1))