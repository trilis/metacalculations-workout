#lang racket
(define ns (make-base-namespace))

(define int
  (lambda (program data)
    (define eval-expr
      (lambda (expr env)
        (if (and (list? expr) (equal? (car expr) 'quote))
            (cadr expr)
            (if (list? expr)
                (apply (eval (car expr) ns) (map (lambda (e) (eval-expr e env)) (cdr expr)))
                (hash-ref env expr))
        )))
    (define run-block
      (lambda (block labels env)
        (define run-command
          (lambda (instr new_env)
            (match instr
              [`(:= ,v ,expr) (hash-set new_env v (eval-expr expr new_env))]
              [`(return ,expr) (eval-expr expr new_env)]
              [`(goto ,label) (run-block (hash-ref labels label) labels new_env)]
              [`(if ,cond ,tbranch ,fbranch) (run-block (hash-ref labels (if (eval-expr cond new_env) tbranch fbranch)) labels new_env)]
            )))
        (foldl run-command env (cdr block))
        ))
    (run-block (cadr program) (make-immutable-hash (map cons (map car program) program)) (make-immutable-hash (map cons (cdar program) data)))))

(define tm-int
  '((read Q Right)
    (init (:= Qtail Q) (:= Left '()) (goto loop))
    (loop (if (equal? Qtail '()) stop cont))
    (cont (:= Instruction (car Qtail)) (:= Qtail (cdr Qtail)) (:= Operator (cadr Instruction)) (if (equal? Operator 'right) do-right cont1))
    (cont1 (if (equal? Operator 'left) do-left cont2))
    (cont2 (if (equal? Operator 'write) do-write cont3))
    (cont3 (if (equal? Operator 'goto) do-goto cont4))
    (cont4 (if (equal? Operator 'if) do-if error))
    (error (return (raise 'syntaxerror: Operator)))
    (stop (return Right))
    (do-right (:= Left (cons '(car Right) Left)) (:= Right (cdr Right)) (goto loop))
    (do-left (:= Left (cdr Left)) (:= Right (cons '(car Left) Right)) (goto loop))
    (do-write (:= Symbol (caddr Instruction)) (:= Right (cons Symbol (cdr Right))) (goto loop))
    (do-goto (:= NextLabel (caddr Instruction)) (goto jump))
    (do-if (:= Symbol (caddr Instruction)) (:= NextLabel (list-ref Instruction '4)) (if (equal? Symbol (car Right)) jump loop))
    (jump (:= Qtail (list-tail Q NextLabel)) (goto loop))
    )
  )

(define tm-example '((0 if 0 goto 3) (1 right) (2 goto 0) (3 write 1)))

(int tm-int `(,tm-example (1 1 1 0 1 0 1)))
