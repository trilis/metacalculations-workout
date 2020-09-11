#lang racket
(define tm-example '((0 if 0 goto 3) (1 right) (2 goto 0) (3 write 1)))

(define tm-int-internal (lambda (program left right progtail)
                         (match (car progtail)
                            [`(,n if ,cond goto ,newinstr) (tm-int-internal program left right (if (equal? cond (car right)) (list-tail program newinstr) (cdr progtail)))]
                            [`(,n left) (tm-int-internal program (cdr left) (cons '(car left) right) (cdr progtail))]
                            [`(,n right) (tm-int-internal program (cons '(car right) left) (cdr right) (cdr progtail))]
                            [`(,n goto ,newinstr) (tm-int-internal program left right (list-tail program newinstr))]
                            [`(,n write ,x) (tm-int-internal program left (cons x (cdr right)) (cdr progtail))]
                            ['end right]
                            ))
  )

(define tm-int (lambda (program data)
                 (tm-int-internal (append program '(end)) '() data program)
                 ))

(tm-int tm-example '(1 1 1 0 1 0 1))