#lang racket
(require (for-syntax syntax/parse syntax/readerr)
         racket/fixnum)
(module+ test (require rackunit))

(provide (rename-out [b:assert assert]
                     [b:datum #%datum]
                     [b:define define]
                     [b:module module]
                     [b:define-inline define-inline]
                     [thread-start! thread-start-joinable!]
                     [open-input-bytes open-input-string]
                     [call-with-output-bytes call-with-output-string]
                     [b:call-with-input-string call-with-input-string]
                     [b:string=? string=?]
                     [read-string read-chars])
         isa?
         correct-arity?
         with-handler
         instantiate::pthread
         thread-start!
         synchronize
         make-mutex
         socket-input
         socket-output
         socket-close
         socket-down?
         make-client-socket
         input-port-timeout-set!
         multiple-value-bind
         include/bigloo
         bit-rsh
         with-trace
         trace-item
         tprint
         thread-join!
         unwind-protect
         reverse!
         pregexp
         string-index)

;; renamings
(provide (rename-out [fx* *fx]
                     [fx+ +fx]
                     [fx- -fx]
                     [fx= =fx]
                     [fx> >fx]
                     [fx>= >=fx]
                     [fxremainder remainderfx]
                     [bitwise-and bit-and]
                     [bitwise-ior bit-or]
                     [arithmetic-shift bit-lsh]
                     [flush-output flush-output-port]
                     [display display-string]
                     [b:pregexp-match pregexp-match]
                     [string-index string-char-index]
                     [list* cons*]
                     ))

(struct bigloo-object (ht struct: maker pred))
(struct mutex (name sem))
(struct socket (input output))

(define (make-mutex/proc name)
  (mutex name (make-semaphore 1)))

(define-syntax (make-mutex stx)
  (syntax-parse stx
    [(_) #`(make-mutex/proc #,(format "~a:~a" (syntax-source stx) (syntax-line stx)))]
    [(_ name) #`(make-mutex/proc name)]))

(define (bit-rsh n m)
  (arithmetic-shift n (- m)))

(define-for-syntax (read-syntax-#!var a b)
  (define rt
    (make-readtable
     (current-readtable) #\! 'dispatch-macro
     (λ (char port src line col pos)
       (define allowed "key")
       (for ([i (in-range (string-length allowed))])
         (define c (read-char port))
         (unless (equal? c (string-ref allowed i))
           ((if (eof-object? c)
                raise-read-eof-error
                raise-read-error)
            (format "expected `~a`" (string-ref allowed i))
            src line col pos 1)))
       '#:key)))
  (parameterize ([current-readtable rt])
    (read-syntax a b)))

(define-syntax (include/bigloo stx)
  (syntax-parse stx
    [(_ fn)
     (datum->syntax stx
                    `(include/reader ,#'fn ,#'read-syntax-#!var)
                    stx stx)]))

(begin-for-syntax
  (define-syntax-class bigloo-kwd-formal-arg
    #:attributes ([racket-arg 1])
    (pattern arg:id
      #:attr (racket-arg 1) (list #'(arg #f)))
    (pattern [arg:id default:expr]
      #:attr (racket-arg 1) (list #`#,(string->keyword (symbol->string (syntax-e #'arg)))
                                  #'[arg default])))

  (define-syntax-class bigloo-annotated-id
    #:attributes (id)
    (pattern arg:id
      #:when (regexp-match? #rx"::" (symbol->string (syntax-e #'arg)))
      #:attr id (datum->syntax #'arg
                               (let ([m (regexp-match #rx"^([^:]*)::" (symbol->string (syntax-e #'arg)))])
                                 (string->symbol (list-ref m 1)))
                               #'arg
                               #'arg))
    (pattern arg:id
      #:when (not (regexp-match? #rx"::" (symbol->string (syntax-e #'arg))))
      #:attr id #'arg)))

(define-syntax (b:define stx)
  (syntax-parse stx
    [(_ (fname:bigloo-annotated-id mandatory:bigloo-annotated-id ... #:key kwd-arg:bigloo-kwd-formal-arg ...)
        body1 body2 ...)
     #'(define (fname.id mandatory.id ... kwd-arg.racket-arg ... ...)
         body1 body2 ...)]
    [(_ (fname:bigloo-annotated-id mandatory:bigloo-annotated-id ...)
        body1 body2 ...)
     #'(define (fname.id mandatory.id ...)
         body1 body2 ...)]))

(define (extend-object ht k+vs class-name)
  (define-values (struct: maker pred _ref _set)
    (if ht
      (if class-name
        (make-struct-type class-name (bigloo-object-struct: ht) 0 0)
        (values (bigloo-object-struct: ht)
                (bigloo-object-maker ht)
                (bigloo-object-pred ht)
                #f
                #f))
      (if class-name
        (make-struct-type class-name struct:bigloo-object 0 0)
        (values struct:bigloo-object
                bigloo-object
                bigloo-object?
                #f
                #f))))
  (define the-result
    (cond
      [(not ht) (make-hash)]
      [(bigloo-object? ht) (hash-copy (bigloo-object-ht ht))]
      [else (error 'extend-object "internal error ~s" ht)]))
  (for ([pr (in-list k+vs)])
    (match-define (cons k v) pr)
    (hash-set! the-result k v))
  (maker the-result struct: maker pred))

(begin-for-syntax
  ;(define-syntax-class field-prop
  ;  #:datum-literals (read-only default)
  ;  #:attributes (init-expr)
  ;  (pattern read-only #:attr init-expr #f)
  ;  (pattern (default d:expr) #:attr init-expr #'d))
  (define (extract-type id-stx)
    (let* ([full-name (symbol->string (syntax-e id-stx))]
           [m (regexp-match #rx"::(.*)$" full-name)])
      (and m
           (datum->syntax id-stx (string->symbol (list-ref m 1)) id-stx id-stx))))
  (define (strip-type id-stx)
    (let* ([full-name (symbol->string (syntax-e id-stx))]
           [plain-name (regexp-replace #rx"::.*$" full-name "")])
      (datum->syntax id-stx (string->symbol plain-name) id-stx id-stx)))
  (define-syntax-class field
    #:datum-literals (read-only default)
    #:attributes (name init-expr)
    (pattern n:identifier #:attr name (strip-type #'n) #:attr init-expr #''())
    (pattern (n:identifier read-only) #:attr name (strip-type #'n) #:attr init-expr #''())
    (pattern (n:identifier (default d:expr))
      #:attr name (strip-type #'n) #:attr init-expr #`(list (cons '#,(strip-type #'n) d)))
    (pattern (n:identifier read-only (default d:expr))
      #:attr name (strip-type #'n) #:attr init-expr #`(list (cons '#,(strip-type #'n) d)))
    (pattern (n:identifier (default d:expr) read-only)
      #:attr name (strip-type #'n) #:attr init-expr #`(list (cons '#,(strip-type #'n) d))))
  (define (make-method-name method class-stx)
    (let* ([full-name (symbol->string (syntax-e class-stx))]
           [class-name (regexp-replace #rx"::.*$" full-name "")]
           [method-name (string-append method class-name)])
      (datum->syntax class-stx
                     (string->symbol method-name)
                     class-stx
                     class-stx)))
  (define (make-selector-id class-name field-name)
    (datum->syntax field-name
                   (string->symbol (string-append (symbol->string (syntax-e class-name)) "-" (symbol->string (syntax-e field-name))))
                   field-name
                   field-name))
  (define (make-mutator-id class-name field-name)
    (datum->syntax field-name
                   (string->symbol (string-append "set-" (symbol->string (syntax-e class-name)) "-" (symbol->string (syntax-e field-name)) "!"))
                   field-name
                   field-name))
  (define (with-access-transformer name-stx fields)
    (define struct-name (strip-type name-stx))
    (lambda (stx)
      (syntax-parse stx
        [(_ pk:expr (field-ids:id ...) body:expr ...)
         #`(let ([x pk])
             (let-syntax ([field-ids (make-set!-transformer
                                      (lambda (stx)
                                        (syntax-parse stx
                                          #:literals (set!)
                                          [id:id #'(hash-ref (bigloo-object-ht x) 'id)]
                                          [(set! id:id expr:expr) #'(hash-set! (bigloo-object-ht x) 'id expr)])))] ... )
               body ...)) ])))
  (define-syntax-class class
    #:literals (class)
    #:attributes ((exports 1) (definitions 1))
    (pattern (class name:id f:field ...)
             #:attr (exports 1)
             (list (make-method-name "with-access::" #'name)
                   (make-method-name "instantiate::" #'name)
                   (strip-type #'name))
             #:attr (definitions 1)
             (list #`(define #,(strip-type #'name)
                       (extend-object #,(or (extract-type #'name) #'#f)
                                      (append f.init-expr ...)
                                      '#,(strip-type #'name)))
                   #`(define-syntax #,(make-method-name "with-access::" #'name)
                       (with-access-transformer #'name (list #'f ...)))
                   #`(define-syntax #,(make-method-name "instantiate::" #'name)
                       (lambda (stx)
                         (syntax-parse stx
                           [(_ (fname:id fexpr:expr) (... ...))
                            #`(extend-object #,(strip-type #'name)
                                             (list (cons 'fname fexpr)
                                                   (... ...))
                                             #f)]))))))
  (define-syntax-class export-clause
    #:attributes ((export 1) (code 0))
    #:datum-literals (inline)
    (pattern x:id
      #:attr code #'(void)
      #:attr (export 1) (list (strip-type #'x)))
    (pattern (inline x:id _ ...)
      #:attr code #'(void)
      #:attr (export 1) (list (strip-type #'x)))
    (pattern (x:id y:id ... (~optional (~seq #:key _ ...)))
      #:attr code #'(void)
      #:attr (export 1) (list (strip-type #'x)))
    (pattern cls:class
      #:attr code #'(b:define-class cls)
      #:attr (export 1) (syntax->list #'(cls.exports ...))))
  (define-syntax-class module-clause
    #:datum-literals (export import library __mqtt_common)
    (pattern (import (~and __mqtt_common id))
      #:attr code (datum->syntax #'id '(require "common.rkt") #'id #'id))
    (pattern (library _ ...)
      #:attr code #'(void))
    (pattern (export clause:export-clause ...)
      #:attr code #'(begin clause.code ... (provide clause.export ... ...)))))

(define-syntax (b:define-class stx)
  (syntax-parse stx
    [(_ cls:class ...)
      #`(begin cls.definitions ... ...)]))

(define-syntax (b:define-and-provide-class stx)
  (syntax-parse stx
    [(_ cls:class ...)
      #`(begin cls.definitions ... ... (provide cls.exports ... ...))]))

(module+ test
  (b:define-class
    (class class-name
      (f1::byte read-only)
      (f2 read-only)
      (f-w-default (default -1))))
  (check-equal? (bigloo-object-ht (instantiate::class-name (f1 1) (f2 2)))
                (make-hash (list (cons 'f1 1)
                                 (cons 'f2 2)
                                 (cons 'f-w-default -1))))
  (check-equal? (bigloo-object-ht (instantiate::class-name (f2 2) (f1 1)))
                (make-hash (list (cons 'f1 1)
                                 (cons 'f2 2)
                                 (cons 'f-w-default -1))))
  (check-equal? (bigloo-object-ht
                 (instantiate::class-name (f2 2) (f1 1) (f-w-default 11)))
                (make-hash (list (cons 'f1 1)
                                 (cons 'f2 2)
                                 (cons 'f-w-default 11))))
  (check-equal? (bigloo-object-ht
                 (instantiate::class-name (f-w-default 11) (f2 2) (f1 1)))
                (make-hash (list (cons 'f1 1)
                                 (cons 'f2 2)
                                 (cons 'f-w-default 11))))

  (check-equal? #t (isa? (instantiate::class-name (f1 1) (f2 2)) class-name))
  (check-equal? #f (isa? 1 class-name))

  (b:define-class
    (class sub-class-name::class-name
      (f3 read-only)
      (f-w-default2 (default -2))))
  (check-equal? (bigloo-object-ht (instantiate::sub-class-name (f2 2) (f1 1) (f3 3)))
                (make-hash (list (cons 'f1 1)
                                 (cons 'f2 2)
                                 (cons 'f3 3)
                                 (cons 'f-w-default -1)
                                 (cons 'f-w-default2 -2))))

  (check-equal? #t (isa? (instantiate::sub-class-name (f1 1) (f2 2)) class-name))

  (check-equal?
   (with-access::class-name (instantiate::class-name (f2 2) (f1 1) (f-w-default 11))
     (f2)
     f2)
   2)
  (check-equal?
   (with-access::class-name (instantiate::class-name (f2 2) (f1 1) (f-w-default 11))
     (f1 f2 f-w-default)
     (list f1 f2 f-w-default))
   (list 1 2 11))
  (check-equal?
   (with-access::sub-class-name (instantiate::sub-class-name (f2 2) (f1 1) (f3 3))
     (f3)
     f3)
   3)
  (check-equal?
   (with-access::sub-class-name (instantiate::sub-class-name (f2 2) (f1 1) (f3 3))
     (f1 f2 f3 f-w-default f-w-default2)
     (list f1 f2 f3 f-w-default f-w-default2))
   (list 1 2 3 -1 -2))
  )

(define-syntax (b:module stx)
  (syntax-parse stx
    [(_ name:identifier clause:module-clause ...)
     #'(begin clause.code ...)]))

(define-syntax (b:define-inline stx)
  (syntax-parse stx
    [(_ (name:id) e:expr)
     #'(define (name) e)]))

(define-syntax (b:assert stx)
  (syntax-parse stx
    [(_ _ condition)
     #`(unless condition #,(syntax/loc stx (error "assert failed" (quote condition))))]))

(define-syntax (with-trace stx)
  (syntax-parse stx
    [(_ level label . body)
     #'(let () . body)]))

(define-syntax (trace-item stx)
  #'(void))
(define-syntax (tprint stx)
  (with-syntax ([file (syntax-source stx)]
                [line (syntax-line stx)])
    (syntax-parse stx
      [(_ a ...)
       #'(tprint/proc 'file line a ...)])))
(define (tprint/proc file line . more)
  (printf "~a:~a:" file line)
  (for ([e (in-list more)])
    (display e))
  #t)

(define-syntax (unwind-protect stx)
  (syntax-parse stx
    [(_ expr protect)
     #'(dynamic-wind
        void
        (λ () expr)
        (λ () protect))]))

(define-syntax-rule (multiple-value-bind (id ...) expr body ...)
  (call-with-values (lambda () expr) (lambda (id ...) body ...)))

(define-syntax (reverse! stx)
  (syntax-parse stx
    [(_ arg)
     (printf "suspicious: replacing reverse! with reverse ~a:~a\n" (syntax-source stx) (syntax-line stx))
     #`(reverse arg)]))

(define (b:pregexp-match reg str)
  (unless (pregexp? reg)
    (error 'b:pregexp-match "expected a pregexp"))
  (regexp-match reg str))

(define (string-index s ch)
  (define reg
    (cond
      [(string? ch) (regexp (regexp-quote ch))]
      [else (regexp (regexp-quote (string ch)))]))
  (define p (regexp-match-positions reg s))
  (and p (car (list-ref p 0))))

(module+ test
  (check-equal? (string-index "abc" #\a) 0)
  (check-equal? (string-index "abc" #\b) 1)
  (check-equal? (string-index "abc" "a") 0)
  (check-equal? (string-index "abc" "b") 1)
  (check-equal? (string-index "abbc" "bc") 2))

(define (b:call-with-input-string str proc)
  (proc (open-input-bytes str)))

(define (b:string=? x y)
  (define (to-bytes n)
    (cond
      [(bytes? n) n]
      [else (error 'b:string=? "bad args ~s ~s" x y)]))
  (bytes=? (to-bytes x)
           (to-bytes y)))

(define-syntax (b:datum stx)
  (syntax-parse stx
    [(_ . x)
     (define u (syntax-e #'x))
     (cond
       [(string? u) #`(#%datum . #,(string->bytes/utf-8 u))]
       [else #`(#%datum . x)])]))

(define (synchronize/proc lock thunk)
  (dynamic-wind
   (lambda () (semaphore-wait (mutex-sem lock)))
   thunk
   (lambda () (semaphore-post (mutex-sem lock)))))

(define-syntax (synchronize stx)
  (syntax-parse stx
    [(_ lock:expr body:expr ...)
     #'(synchronize/proc lock (lambda () body ...)) ]))

(define (socket-close s)
  (close-input-port (socket-input s))
  (close-output-port (socket-output s)))

(define (socket-down? s)
  (define p (socket-input s))
  (eof-object? (with-handlers ([exn:fail? (lambda (x) eof)])
                 (peek-byte p))))

(define (make-client-socket host port)
  (define-values (in out) (tcp-connect (bytes->string/utf-8 host) port))
  (socket in out))

(define (input-port-timeout-set! port)
  (void))

(struct pthread (name body [thread #:mutable]))

(define-syntax (instantiate::pthread stx)
  (syntax-parse stx
    #:datum-literals (name body)
    [(_ (~optional (name x:str) #:defaults ([x #'#f])) (body thunk:expr))
     #`(pthread x thunk #f)]))

(define (thread-start! pthread)
  (let ([th (thread (pthread-body pthread))])
    (set-pthread-thread! pthread th)
    pthread))

(define (thread-join! pthread)
  (thread-wait (pthread-thread pthread)))

(define (with-handler/proc handler thunk)
  (with-handlers ([exn:fail? handler]) (thunk)))

(define-syntax (with-handler stx)
  (syntax-parse stx
    [(_ handler body) #`(with-handler/proc handler (lambda () body))]))

(define (correct-arity? fn n)
  (equal? n (procedure-arity fn)))

(define (isa? object class)
  ((bigloo-object-pred class) object))

(b:define-and-provide-class
 (class &exception
   (fname read-only (default #f))
   (location read-only (default #f)))

 (class &error::&exception
   (proc read-only)
   (msg read-only)
   (obj read-only))

 (class &io-error::&error) )
