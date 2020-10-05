#lang racket

(require "utils.rkt")
(provide (all-defined-out))

(define int
  (lambda (program data)
    (define run-block
      (lambda (block labels env)
        (define run-command
          (lambda (instr new_env)
            (match instr
              [`(:= ,v ,expr) (update-env new_env v (eval-expr expr new_env))]
              [`(return ,expr) (eval-expr expr new_env)]
              [`(goto ,label) (run-block (hash-ref labels label) labels new_env)]
              [`(if ,cond ,tbranch ,fbranch) (run-block (hash-ref labels (if (eval-expr cond new_env) tbranch fbranch)) labels new_env)]
            )))
        (foldl run-command env (cdr block))
        ))
    (run-block (cadr program) (create-label-map program) (create-env-map (cdar program) data))))

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
    (do-right (:= Left (cons (car-or-zero Right) Left)) (:= Right (cdr-or-empty Right)) (goto loop))
    (do-left (:= Left (cdr-or-empty Left)) (:= Right (cons (car-or-zero Left) Right)) (goto loop))
    (do-write (:= Symbol (caddr Instruction)) (:= Right (cons Symbol (cdr Right))) (goto loop))
    (do-goto (:= NextLabel (caddr Instruction)) (goto jump))
    (do-if (:= Symbol (caddr Instruction)) (:= NextLabel (list-ref Instruction '4)) (if (equal? Symbol (car Right)) jump loop))
    (jump (:= Qtail (list-tail Q NextLabel)) (goto loop))
    )
  )

(define fc-int
  '((read program data)
    (init (:= env (create-env-map (cdar program) data)) (:= labels (create-label-map program))
          (:= bb (cdadr program)) (goto loop))
    (loop (if (empty? bb) loop-end loop-body))
    (loop-body (:= command (car bb)) (:= bb (cdr-or-empty bb)) (goto case1))
    (case1 (if (equal? (car command) ':=) do-assign case2))
    (case2 (if (equal? (car command) 'goto) do-goto case3))
    (case3 (if (equal? (car command) 'if) do-if case4))
    (case4 (if (equal? (car command) 'return) do-return error))
    (do-goto (:= bb (cdr (hash-ref labels (cadr command)))) (goto loop))
    (do-if (if (eval-expr (cadr command) env) do-if-true do-if-false))
    (do-if-true (:= bb (cdr (hash-ref labels (caddr command)))) (goto loop))
    (do-if-false (:= bb (cdr (hash-ref labels (cadddr command)))) (goto loop))
    (do-assign (:= env (update-env env (cadr command) (eval-expr (caddr command) env))) (goto loop))
    (do-return (return (eval-expr (cadr command) env)))
    (loop-end (return '()))
    (error (return (raise 'syntaxerror: command)))
    )
  )