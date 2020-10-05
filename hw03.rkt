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

(define (subst env expr)
      (match expr
        [`(quote ,x) expr]
        [`(,x . ,y) `(,(subst env x) . ,(subst env y))]
        [`,x (if (hash-has-key? env x) (hash-ref env x) x)]))

(define eval-expr
  (lambda (expr env)
    (eval (subst env expr) ns)))


(define reduce
  (lambda (expr vs)
    (define reduce-rec
      (lambda (ex)
         (match ex
      [`(,x . ,y) (with-handlers ([exn:fail? (lambda (exn)
                                               `(,x . ,(map (lambda (e) (reduce-rec e)) y)))]) (cons 'quote (list (eval `(,x . ,y) ns))))]
      [`,x x])))
    (reduce-rec (subst vs expr))))
   

(define lookup
  (lambda (label program)
    (dict-ref program label)))

(define next-label-after
  (lambda (label blocks-in-pending)
    (if (empty? (cdr blocks-in-pending))
        (car blocks-in-pending)
        (if (equal? label (car blocks-in-pending))
            (cadr blocks-in-pending)
            (next-label-after label (cdr blocks-in-pending)))
    )))

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
    (if (or (member key pending) (member key marked))
        pending
        (cons key pending))
    ))

(define create-blocks-in-pending
  (lambda (program division)
    (define create-blocks-in-pending-command
      (lambda (comm)
        (if (and (equal? (car comm) 'if) (not (is-static (cadr comm) division)))
            (list (caddr comm) (cadddr comm))
            '())
        ))
    (define create-blocks-in-pending-bb
      (lambda (bb)
        (flatten (map create-blocks-in-pending-command (cdr bb)))
        ))
    (remove-duplicates (cons (caar program) (flatten (map create-blocks-in-pending-bb program))))
    ))

(define get-dynamic-args
  (lambda (program division)
    (filter (lambda (k) (not (is-static k division))) (cdar program))))

(define create-label-map
  (lambda (program)
     (make-immutable-hash (map cons (map car program) program))
    )
  )

(define update-env
  (lambda (env x v)
    (hash-set env x (cons 'quote (list v)))))

(define create-env-map
  (lambda (names data)
    (foldl (lambda (t env) (update-env env (car t) (cdr t))) #hash() (map cons names data))
    )
  )

(define remove-env
  (lambda (program)
    (define true-names #f)
    (define remove-env-rec-filter
      (lambda (ex1 ex2)
        (let ([res1 (remove-env-rec ex1)] [res2 (remove-env-rec ex2)]) (if (equal? (void) res1) res2 (if (equal? (void) res2) res1 `(,res1 . ,res2))))))
    (define remove-env-rec
      (lambda (ex)
        (match ex
          [`(quote ,x) ex]
          [`(eval-expr ,val env) (eval val)]
          [`(:= env (create-env-map ,names data)) (set! true-names (eval names))]
          [`(:= env (update-env env ,name ,value)) `(:= ,(eval name) ,(remove-env-rec value))]
          [`(,x . ,y) (remove-env-rec-filter x y)]
          (`,x x))))
    (let ([tail (map remove-env-rec (cdr program))]) (if true-names (cons `(read ,true-names) tail) program))))


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

(define find-name
  '((read name namelist valuelist)
    (search (if (equal? name (car namelist)) found cont))
    (cont (:= valuelist (cdr valuelist)) (:= namelist (cdr namelist)) (goto search))
    (found (return (car valuelist)))
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

(define mix
  '((read program division vs0)
    (init (:= pp0 (caadr program)) (:= pending (list (cons pp0 vs0))) (:= marked '()) (:= blocks-in-pending (create-blocks-in-pending (cdr program) division))
          (:= residual (list (cons 'read (get-dynamic-args program division)))) (:= bb '()) (:= command '()) (:= ppx pp0) (goto loop))
    (loop (if (empty? pending) stop loop-body))
    (loop-body (:= pp (caar pending)) (:= vs (cdar pending)) (:= pending (cdr-or-empty pending)) (:= marked (cons (cons pp vs) marked))
               (:= code (list (cons pp vs))) (goto lookup-loop))
    (inner-loop (if (empty? bb) loop-end inner-loop-body))
    (inner-loop-body (:= command (car bb)) (:= bb (cdr-or-empty bb)) (goto case1))
    (case1 (if (equal? (car command) ':=) do-assign case2))
    (case2 (if (equal? (car command) 'goto) do-goto case3))
    (case3 (if (equal? (car command) 'if) do-if case4))
    (case4 (if (equal? (car command) 'return) do-return error))
    (do-assign (if (is-static (cadr command) division) do-assign-static do-assign-dynamic))
    (do-assign-static (:= vs (update-env vs (cadr command) (eval-expr (caddr command) vs))) (goto inner-loop))
    (do-assign-dynamic (:= code (cons (list ':= (cadr command) (reduce (caddr command) vs)) code)) (goto inner-loop))
    (do-goto (:= bb (lookup (cadr command) program)) (goto inner-loop))
    (do-if (if (is-static (cadr command) division) do-if-static do-if-dynamic))
    (do-if-static (if (eval-expr (cadr command) vs) do-if-static-true do-if-static-false))
    (do-if-static-true (:= bb (lookup (caddr command) program)) (goto inner-loop))
    (do-if-static-false (:= bb (lookup (cadddr command) program)) (goto inner-loop))
    (do-if-dynamic (:= pending (update-pending (update-pending pending (cons (caddr command) vs) marked) (cons (cadddr command) vs) marked))
                   (:= code (cons (list 'if (reduce (cadr command) vs) (cons (caddr command) vs) (cons (cadddr command) vs)) code)) (goto inner-loop))
    (do-return (:= code (cons (list 'return (reduce (cadr command) vs)) code)) (goto inner-loop))
    (loop-end (:= residual (cons (reverse code) residual)) (:= bb '()) (:= command '()) (goto loop))
    (stop (return (remove-env (improve-labels (reverse residual)))))
    (error (return (raise 'syntaxerror: command)))
    (lookup-loop (if (equal? pp ppx) lookup-end lookup-body))
    (lookup-body (:= ppx (next-label-after ppx blocks-in-pending)) (goto lookup-loop))
    (lookup-end (:= bb (lookup ppx program)) (:= ppx pp0) (goto inner-loop))
    )
  )

(define tm-example '((0 if 0 goto 3) (1 right) (2 goto 0) (3 write 1)))

(define tm-int-division (list 'Q 'Qtail 'Instruction 'Operator 'Symbol 'NextLabel))
(define fc-int-division (list 'program 'labels 'bb 'command))
(define mix-division (list 'program 'division 'bb 'command 'pp0 'ppx 'blocks-in-pending))

;;(define fut1 (int mix `(,tm-int ,tm-int-division ,(make-immutable-hash (list (cons 'Q (cons 'quote (list tm-example))))))))
;;(define fut2 (int mix `(,mix ,mix-division ,(make-immutable-hash (list (cons 'program (cons 'quote (list tm-int))) (cons 'division (cons 'quote (list tm-int-division))))))))
(define fut3 (int mix `(,mix ,mix-division ,(make-immutable-hash (list (cons 'program (cons 'quote (list mix))) (cons 'division (cons 'quote (list mix-division))))))))
;;(define fut1-fc (int mix `(,fc-int ,fc-int-division ,(make-immutable-hash (list (cons 'program (cons 'quote (list find-name))))))))
;;(define fut2-fc (int mix `(,mix ,mix-division ,(make-immutable-hash (list (cons 'program (cons 'quote (list fc-int))) (cons 'division (cons 'quote (list fc-int-division))))))))

(pretty-print-columns 100)
;;(pretty-print fut1-fc)

;;(pretty-print (int (int fut3 `(,(make-immutable-hash (list (cons 'program (cons 'quote (list tm-int))) (cons 'division (cons 'quote (list tm-int-division))))))) `(,(make-immutable-hash (list (cons 'Q (cons 'quote (list tm-example))))))))
(pretty-print (int (int fut3 `(,(make-immutable-hash (list (cons 'program (cons 'quote (list fc-int))) (cons 'division (cons 'quote (list fc-int-division))))))) `(,(make-immutable-hash (list (cons 'program (cons 'quote (list find-name))))))))

;;(define res1 (int fut2 `(,(make-immutable-hash (list (cons 'Q (cons 'quote (list tm-example))))))))
;;(define res2 (int fut1 '((1 1 1 0 1 0 1))))
;;(pretty-print (int fut2-fc `(,(make-immutable-hash (list (cons 'program (cons 'quote (list find-name))))))))