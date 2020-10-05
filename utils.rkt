#lang racket

(provide (all-defined-out))

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
    (let ([tail (map remove-env-rec (cdr program))]) (if true-names (cons `(read . ,true-names) tail) program))))


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
