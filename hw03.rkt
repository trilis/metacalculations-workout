#lang racket
(define-namespace-anchor a)
(define ns (namespace-anchor->namespace a))

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

(define eval-expr
  (lambda (expr env)
    (if (and (list? expr) (equal? (car expr) 'quote))
        (cadr expr)
        (if (list? expr)
            (apply (eval (car expr) ns) (map (lambda (e) (eval-expr e env)) (cdr expr)))
            (if (symbol? expr)
                (hash-ref env expr)
                expr))
        )))

(define reduce
  (lambda (expr vs)
    (if (and (list? expr) (equal? (car expr) 'quote))
        expr
        (if (list? expr)
            (cons (car expr) (map (lambda (e) (reduce e vs)) (cdr expr)))
            (hash-ref vs expr expr))
        )))

(define lookup
  (lambda (label program)
    (if (equal? label (caar program))
        (cdar program)
        (lookup label (cdr program)))
    ))

(define is-static
  (lambda (expr division)
    (if (and (list? expr) (equal? (car expr) 'quote))
        '#t
        (if (list? expr)
            (andmap (lambda (e) (is-static e division)) (cdr expr))
            (member expr division))
        )))

(define update-pending
  (lambda (pending key marked)
    (if (member key marked)
        pending
        (cons key pending))
    ))

(define get-dynamic-args
  (lambda (program division)
    (filter (lambda (k) (not (is-static k division))) (cdar program))))

(define improve-labels
  (lambda (program)
  (define change-labels
    (lambda (block h)
      (if (hash-has-key? h block)
          (hash-ref h block)
          (if (list? block)
              (map (lambda (b) (change-labels b h)) block)
              block))))
    (change-labels program (make-immutable-hash (map cons (map car (cdr program)) (build-list (length (cdr program)) (lambda (i) (string->symbol (string-append "lab" (number->string i))))))))
    ))

(define int
  (lambda (program data)
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
    (do-right (:= Left (cons (car-or-zero Right) Left)) (:= Right (cdr-or-empty Right)) (goto loop))
    (do-left (:= Left (cdr-or-empty Left)) (:= Right (cons (car-or-zero Left) Right)) (goto loop))
    (do-write (:= Symbol (caddr Instruction)) (:= Right (cons Symbol (cdr Right))) (goto loop))
    (do-goto (:= NextLabel (caddr Instruction)) (goto jump))
    (do-if (:= Symbol (caddr Instruction)) (:= NextLabel (list-ref Instruction '4)) (if (equal? Symbol (car Right)) jump loop))
    (jump (:= Qtail (list-tail Q NextLabel)) (goto loop))
    )
  )

(define mix
  '((read program division vs0)
    (init (:= pending (list (cons (caadr program) vs0))) (:= marked (list (cons (caar pending) (cdar pending))))
          (:= residual (list (cons 'read (get-dynamic-args program division)))) (goto loop))
    (loop (if (empty? pending) stop loop-body))
    (loop-body (:= pp (caar pending)) (:= vs (cdar pending)) (:= pending (cdr-or-empty pending)) 
               (:= bb (lookup pp program)) (:= code (list (cons pp vs))) (goto inner-loop))
    (inner-loop (if (empty? bb) loop-end inner-loop-body))
    (inner-loop-body (:= command (car bb)) (:= bb (cdr-or-empty bb)) (goto case1))
    (case1 (if (equal? (car command) ':=) do-assign case2))
    (case2 (if (equal? (car command) 'goto) do-goto case3))
    (case3 (if (equal? (car command) 'if) do-if case4))
    (case4 (if (equal? (car command) 'return) do-return error))
    (do-assign (if (is-static (cadr command) division) do-assign-static do-assign-dynamic))
    (do-assign-static (:= vs (hash-set vs (cadr command) (eval-expr (caddr command) vs))) (goto inner-loop))
    (do-assign-dynamic (:= code (cons (list ':= (cadr command) (reduce (caddr command) vs)) code)) (goto inner-loop))
    (do-goto (:= bb (lookup (cadr command) program)) (goto inner-loop))
    (do-if (if (is-static (cadr command) division) do-if-static do-if-dynamic))
    (do-if-static (if (eval-expr (cadr command) vs) do-if-static-true do-if-static-false))
    (do-if-static-true (:= bb (lookup (caddr command) program)) (goto inner-loop))
    (do-if-static-false (:= bb (lookup (cadddr command) program)) (goto inner-loop))
    (do-if-dynamic (:= pending (update-pending (update-pending pending (cons (caddr command) vs) marked) (cons (cadddr command) vs) marked))
                   (:= marked (cons (cons (caddr command) vs) marked)) (:= marked (cons (cons (cadddr command) vs) marked))
                   (:= code (cons (list 'if (reduce (cadr command) vs) (cons (caddr command) vs) (cons (cadddr command) vs)) code)) (goto inner-loop))
    (do-return (:= code (cons (list 'return (reduce (cadr command) vs)) code)) (goto inner-loop))
    (loop-end (:= residual (cons (reverse code) residual)) (goto loop))
    (stop (return (improve-labels (reverse residual))))
    (error (return (raise 'syntaxerror: command)))
    )
  )

(define tm-example '((0 if 0 goto 3) (1 right) (2 goto 0) (3 write 1)))

(int mix `(,tm-int ,(list 'Q 'Qtail 'Instruction 'Operator 'Symbol 'NextLabel) ,(make-immutable-hash (list (cons 'Q tm-example)))))

(int (int mix `(,tm-int ,(list 'Q 'Qtail 'Instruction 'Operator 'Symbol 'NextLabel) ,(make-immutable-hash (list (cons 'Q tm-example))))) '((1 1 1 0 1 0 1)))