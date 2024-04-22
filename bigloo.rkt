#lang racket
(require (for-syntax syntax/parse syntax/readerr)
         racket/fixnum)

(provide (rename-out [b:assert assert]
                     [b:define define]
                     [b:module module]
                     [b:define-inline define-inline]
                     [read-string read-chars])
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
                     [fxremainder remainderfx]
                     [bitwise-and bit-and]
                     [bitwise-ior bit-or]
                     [arithmetic-shift bit-lsh]
                     [flush-output flush-output-port]
                     [display display-string]))

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
    [(_ (fname:id mandatory:bigloo-annotated-id ... #:key kwd-arg:bigloo-kwd-formal-arg ...)
        body1 body2 ...)
     #'(define (fname mandatory.id ... kwd-arg.racket-arg ... ...)
         body1 body2 ...)]
    [(_ (fname:id mandatory:bigloo-annotated-id ...)
        body1 body2 ...)
     #'(define (fname mandatory.id ...)
         body1 body2 ...)]))

(begin-for-syntax
  (define-syntax-class field-prop
    #:datum-literals (read-only default)
    (pattern read-only)
    (pattern (default d:expr)))
  (define-syntax-class field
    (pattern n:identifier)
    (pattern (n:identifier fp:field-prop)))
  (define-syntax-class class
    #:literals (class)
    #:attributes (exports)
    (pattern (class name:id (~optional constructor) f:field ...)
      #:attr exports #'(name)))
  (define-syntax-class export-clause
    #:datum-literals (inline)
    (pattern x:id
      #:attr export #'x)
    (pattern (inline x:id arg:id ...)
      #:attr export #'x)
    (pattern (x:id arg:id ...)
      #:attr export #'x)
    (pattern cls:class
      #:attr export #'cls.exports))
  (define-syntax-class module-clause
    (pattern (export clause:export-clause ...)
      #:attr code #'(provide clause.export ...))))

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
