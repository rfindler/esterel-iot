#lang racket
(require (for-syntax syntax/parse syntax/readerr)
         racket/fixnum racket/hash)

(provide (rename-out [b:assert assert]
                     [b:define define]
                     [b:module module]
                     [b:define-inline define-inline]
                     [read-string read-chars])
         multiple-value-bind
         include/bigloo
         bit-rsh
         with-trace
         trace-item
         tprint
         unwind-protect)

;; renamings
(provide (rename-out [fx* *fx]
                     [fx+ +fx]
                     [fx= =fx]
                     [fx> >fx]
                     [fx>= >=fx]
                     [fxremainder remainderfx]
                     [bitwise-and bit-and]
                     [bitwise-ior bit-or]
                     [arithmetic-shift bit-lsh]
                     [flush-output flush-output-port]
                     [display display-string]))

(struct bigloo-object
  (ht))

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
      #:attr (racket-arg 1) (list #'arg))
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


(begin-for-syntax
  (define-syntax-class field-prop
    #:datum-literals (read-only default)
    #:attributes (init-expr)
    (pattern read-only #:attr init-expr #f)
    (pattern (default d:expr) #:attr init-expr #'d))
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
    #:attributes (name init-expr)
    (pattern n:identifier #:attr name (strip-type #'n) #:attr init-expr #''())
    (pattern (n:identifier fp:field-prop)
             #:attr name (strip-type #'n)
             #:attr init-expr (if (attribute fp.init-expr) #`(list (cons '#,(strip-type #'n) fp.init-expr)) #''())))
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
                   (make-method-name "instantiate::" #'name))
             #:attr (definitions 1)
             (list #`(define #,(strip-type #'name)
                       (hash-union! #,(or (extract-type #'name) (make-hash))
                                    (make-hash (append f.init-expr ...))))
                   #`(define-syntax #,(make-method-name "with-access::" #'name)
                       (with-access-transformer #'name (list #'f ...)))
                   #`(define-syntax #,(make-method-name "instantiate::" #'name)
                       (lambda (stx)
                         (syntax-parse stx
                           [(_ (fname:id fexpr:expr) (... ...))
                            #`(hash-union! #,(strip-type #'name)
                                           (make-hash (list (cons 'fname fexpr) (... ...))))]))))))
  (define-syntax-class export-clause
    #:attributes ((export 1) (code 0))
    #:datum-literals (inline)
    (pattern x:id
      #:attr code #'(void)
      #:attr (export 1) (list #'x))
    (pattern (inline x:id arg:id ...)
      #:attr code #'(void)
      #:attr (export 1) (list #'x))
    (pattern (x:id arg:id ...)
      #:attr code #'(void)
      #:attr (export 1) (list #'x))
    (pattern cls:class
      #:attr code #'(b:define-class cls)
      #:attr (export 1) (syntax->list #'(cls.exports ...))))
  (define-syntax-class module-clause
    #:datum-literals (export)
    (pattern (export clause:export-clause ...)
      #:attr code #'(begin clause.code ... (provide clause.export ... ...)))))

;; TODO: remove
(require racket/pretty)
(define-for-syntax (trace-stx x)
  ((dynamic-require 'racket/pretty 'pretty-write) (syntax->datum x)) x)

(define-syntax (b:define-class stx)
  (syntax-parse stx
    [(_ cls:class)
     (trace-stx
      #`(begin cls.definitions ...))]))

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
     #'(unless condition (error "assert failed"))]))

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
