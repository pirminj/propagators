
(use-modules (srfi srfi-1)
	     (srfi srfi-9)
	     (srfi srfi-9 gnu)
	     (srfi srfi-69)
	     (oop goops)
	     (ice-9 match)
	     (ice-9 pretty-print)
	     (ice-9 optargs))


(define (square x) (* x x))


(define-record-type <default-object>
  (make-default-object)
  default-object?)

(define *predicate-table* (make-hash-table))
(define (predicate? x) (hash-table-exists? *predicate-table* x))
(define (get-predicate-metadata x) (hash-table-ref *predicate-table* x))
(define (set-predicate-metadata! predicate metadata)
  (hash-table-set! *predicate-table* predicate metadata))

(define predicate-name get-predicate-metadata)
(define (predicate-description predicate)
  (if (predicate? predicate)
      (object->string (predicate-name predicate))
      (string-append "object" (object->string predicate))))

(define (register-predicate! predicate name)
  (set-predicate-metadata! predicate name)
  predicate)
(define (register-compound-predicate! predicate type components)
  (register-predicate! predicate
		       (cons type
			     (map predicate-name components))))
(define (maybe-register-compound-predicate! predicate operator operands)
  (if (every predicate? operands)
      (register-compound-predicate! predicate operator operands)
      predicate))

(define (any-object? object) #t)

(register-predicate! any-object? 'any-object)
(register-predicate! number? 'number)
(register-predicate! symbol? 'symbol)
(register-predicate! boolean? 'boolean)

(define* (guarantee predicate object #:optional caller)
  (if (not (predicate object))
      (error:not-a predicate object caller)
      object))

(define* (error:not-a predicate object #:optional caller)
  (error object
         (predicate-description predicate)
         caller))

(define (list-of-type? list predicate)
  (or (null? list)
      (and (predicate (car list))
           (list-of-type? (cdr list) predicate))))

(define* (guarantee-list-of predicate object #:optional caller)
  (if (not (list-of-type? object predicate))
      (error:not-a-list-of predicate object caller)
      object))

(define* (error:not-a-list-of predicate object #:optional caller)
  (error object
         (string-append
          "list of "
          (predicate-description predicate))
         caller))

(define (complement predicate)
  (maybe-register-compound-predicate!
   (lambda (object) (not (predicate object)))
   'complement (list predicate)))

(define (disjoin . predicates) (disjoin* predicates))
(define (disjoin* predicates)
  (maybe-register-compound-predicate!
   (lambda (object)
     (any (lambda (predicate) (predicate object))
	  predicates))
   'disjoin predicates))

(define (conjoin . predicates) (conjoin* predicates))
(define (conjoin* predicates)
  (maybe-register-compound-predicate!
   (lambda (object)
     (every (lambda (predicate) (predicate object))
	    predicates))
   'conjoin predicates))

(define (equality-predicate-maker name =)
  (lambda (object)
    (let ((predicate
           (lambda (object*)
             (= object object*))))
      (register-predicate! predicate (list name =))
      predicate)))

(define eq-predicate
  (equality-predicate-maker 'eq? eq?))
(define eqv-predicate
  (equality-predicate-maker 'eqv? eqv?))
(define equal-predicate
  (equality-predicate-maker 'equal? equal?))



(define (applicability? object)
  (and (list? object)
       (every (lambda (pattern)
                (and (list? pattern)
                     (every procedure? pattern)))
              object)
       (or (not (pair? object))
           (let ((arity (length (car object))))
             (every (lambda (pattern)
                      (= arity (length pattern)))
                    (cdr object))))))

(define (applicability-arity applicability)
  (guarantee applicability? applicability)
  (if (pair? applicability)
      (length (car applicability))
      0))

(define (is-applicable? applicability args)
  (any (lambda (and-clause)
         (predicates-match? and-clause args))
       applicability))

(define (predicates-match? predicates args)
  (and (= (length predicates) (length args))
       (every (lambda (predicate arg)
		(predicate arg))
              predicates
              args)))

(define (all-sequences-of arity zero one)
  (map (lambda (index)
         (index->choices index arity zero one))
       (iota (expt 2 arity))))

(define (index->choices index arity zero one)
  (let loop ((i 0) (index index) (choices '()))
    (if (< i arity)
        (loop (+ i 1)
              (quotient index 2)
              (cons (if (odd? index) one zero)
                    choices))
        choices)))

(define (match-args . predicates)
  (list predicates))

(define (all-args arity predicate)
  (list (make-list arity predicate)))

(define (any-arg arity predicate base-predicate)
  (if (= 0 arity)
      (list)
      (cdr (all-sequences-of arity base-predicate predicate))))

(define (applicability-union . applicabilities)
  (applicability-union* applicabilities))

(define (applicability-union* applicabilities)
  (apply lset-union equal? applicabilities))





;;;; Operation abstraction

(define (operator? object)
  (assq object %arithmetic-operator-alist))

(define (operator-arity operator)
  (length (operator-domains operator)))

(define (operator-domains operator)
  (cadr (%operator-entry operator)))

(define (operator-codomain operator)
  (caddr (%operator-entry operator)))


(define (operator-installable? operator)
  #t)


(define (operator->procedure-name operator)
  (let ((p (assq operator internal-operators)))
    (if p
        (cdr p)
        operator)))

(define internal-operators
  '((negate . -)
    (invert . /)))

(define (constant-names)
  '(additive-identity multiplicative-identity))

(define (operator-names)
  (map car %arithmetic-operator-alist))

(define (%operator-entry operator)
  (or (assq operator %arithmetic-operator-alist)
      (error "Unknown operator:" operator)))

(define (operator-signature operator domain)
  (let ((mapper
         (lambda (indicator)
           (case indicator
             ((domain) domain)
             ((boolean) boolean?)
             ((number) number?)
             (else (error "Unknown domain:" indicator))))))
    (values (map mapper (operator-domains operator))
            (mapper (operator-codomain operator)))))

(define %arithmetic-operator-alist
  '((* (domain domain) domain)
    (+ (domain domain) domain)
    (- (domain domain) domain)
    (/ (domain domain) domain)
    (< (domain domain) boolean)
    (<= (domain domain) boolean)
    (= (domain domain) boolean)
    (> (domain domain) boolean)
    (>= (domain domain) boolean)
    (abs (domain) domain)
    (acos (domain) domain)
    (angle (domain) domain)
    (asin (domain) domain)
    (atan (domain) domain)
    (ceiling (domain) domain)
    (cos (domain) domain)
    (exp (domain) domain)
    (expt (domain number) domain)
    (floor (domain) domain)
    (imag-part (domain) domain)
    (invert (domain) domain)
    (log (domain) domain)
    (magnitude (domain) domain)
    (make-polar (domain domain) domain)
    (make-rectangular (domain domain) domain)
    (max (domain domain) domain)
    (min (domain domain) domain)
    (negate (domain) domain)
    (negative? (domain) boolean)
    (positive? (domain) boolean)
    (real-part (domain) domain)
    (remainder (domain domain) domain)
    (round (domain) domain)
    (sin (domain) domain)
    (square (domain) domain)
    (sqrt (domain) domain)
    (tan (domain) domain)
    (truncate (domain) domain)
    (zero? (domain) boolean)))







;;; operation

(define (operation? object)
  (and (list? object)
       (= 4 (length object))
       (eq? 'operation (car object))
       (operator? (cadr object))
       (applicability? (caddr object))
       (procedure? (cadddr object))))

(define (make-operation operator applicability procedure)
  (list 'operation operator applicability procedure))

;;; API
(define (operation-operator operation)
  (cadr operation))

;;; API
(define (operation-applicability operation)
  (caddr operation))

;;; API
(define (operation-procedure operation)
  (cadddr operation))

;;; API
(define (apply-operation operation args)
  (apply (operation-procedure operation) args))

;;; API
(define (make-installable-operation-procedure procedure
                                              new-procedure)
  new-procedure)

;;; API
(define (operation-components operation)
  (list operation))

;;; API !!! hacked on
(define (constant-union name . constants)
  (let ((unique
         (remove default-object?
                 (delete-duplicates constants eqv?))))
    (if (pair? unique)
        (car unique)
        (make-default-object))))

;;; API
(define (operation-union operator . operations)
  (operation-union* operator operations))

;;; API
(define (operation-union* operator operations)
  (make-operation operator
                  (applicability-union*
                   (map operation-applicability operations))
                  (lambda args
                    (operation-union-dispatch operator
                                              operations
                                              args))))

;; helper to make book description clearer
(define (operation-union-dispatch operator operations args)
  (let ((operation
         (find (lambda (operation)
                 (is-operation-applicable? operation args))
               operations)))
    (if (not operation)
        (error "Inapplicable operation:" operator args))
    (apply-operation operation args)))

;; helper to make book description clearer
(define (is-operation-applicable? operation args)
  (is-applicable? (operation-applicability operation) args))

;;; API
(define (simple-operation operator predicate procedure)
  (make-operation operator
                  (all-args (operator-arity operator)
                            predicate)
                  procedure))

;;; API
(define (simple-operation-procedure operation)
  (operation-procedure operation))

;;; API
(define (transform-operation-procedure procedure operation)
  (make-operation (operation-operator operation)
                  (operation-applicability operation)
                  (procedure (operation-procedure operation))))
















;;;; Arithmetic abstraction

(define-record-type <arithmetic>
  (%make-arithmetic name bases domain-predicate constant-alist
                    operation-alist)
  arithmetic?
  (name arithmetic-name)
  (bases arithmetic-bases)
  (domain-predicate arithmetic-domain-predicate)
  (constant-alist arithmetic-constant-alist)
  (operation-alist arithmetic-operation-alist))

(define (make-arithmetic name
                         domain-predicate
                         bases
                         get-constant
                         get-operation)
  (guarantee predicate? domain-predicate)
  (guarantee-list-of arithmetic? bases)
  (%make-arithmetic
   (cons name (map arithmetic-name bases))
   bases
   domain-predicate
   ;; TODO(cph): Eliding these calls when the number of results
   ;; doesn't equal the number of bases is arbitrary and should
   ;; be reconsidered.
   (filter-map (lambda (name)
                 (let ((base-constants
                        (arithmetic-constants-for name bases)))
                   (and (= (length bases)
                             (length base-constants))
                        (cons name
                              (apply get-constant
                                     name
                                     base-constants)))))
               (arithmetic-constant-names-for bases))
   (filter-map (lambda (operator)
                 (let ((base-operations
                        (arithmetic-operations-for operator
                                                   bases)))
                   (and (= (length bases)
                             (length base-operations))
                        (cons operator
                              (apply get-operation
                                     operator
                                     base-operations)))))
               (arithmetic-operators-for bases))))

(define (arithmetic-constant-names-for bases)
  (if (pair? bases)
      (apply lset-union eq?
             (map arithmetic-constant-names bases))
      (constant-names)))

(define (arithmetic-constants-for name bases)
  (remove default-object?
          (map (lambda (base)
                 (find-arithmetic-constant name base))
               bases)))

(define (arithmetic-operators-for bases)
  (if (pair? bases)
      (apply lset-union eq?
             (map arithmetic-operators bases))
      (operator-names)))

(define (arithmetic-operations-for operator bases)
  (filter-map (lambda (base)
                (find-arithmetic-operation operator base))
              bases))

(define (arithmetic-constant-names arithmetic)
  (map car (arithmetic-constant-alist arithmetic)))

(define (arithmetic-constant name arithmetic)
  (let ((constant (find-arithmetic-constant name arithmetic)))
    (if (default-object? constant)
        (error "Unknown constant name:" name arithmetic))
    constant))

;; For use only by generic arithmetic.
(define (arithmetic-constant-binding name arithmetic)
  (let ((binding
         (assq name (arithmetic-constant-alist arithmetic))))
    (if (not binding)
        (error "Unknown constant name:" name arithmetic))
    binding))

(define (find-arithmetic-constant name arithmetic)
  (let ((p (assq name (arithmetic-constant-alist arithmetic))))
    (if p
        (cdr p)
        (make-default-object))))

(define (arithmetic-operators arithmetic)
  (map car (arithmetic-operation-alist arithmetic)))

(define (arithmetic-operation operator arithmetic)
  (let ((operation
         (find-arithmetic-operation operator arithmetic)))
    (if (not operation)
        (error "Unknown operator:" operator))
    operation))

(define (arithmetic-procedure operator arithmetic)
  (operation-procedure
   (arithmetic-operation operator arithmetic)))

(define (find-arithmetic-operation operator arithmetic)
  (let ((p (assq operator
                 (arithmetic-operation-alist arithmetic))))
    (and p
         (cdr p))))

(define (add-arithmetics . arithmetics)
  (add-arithmetics* arithmetics))

(define (add-arithmetics* arithmetics)
  (if (null? (cdr arithmetics))
      (car arithmetics)
      (make-arithmetic 'add
                       (disjoin*
                        (map arithmetic-domain-predicate
                             arithmetics))
                       arithmetics
                       constant-union
                       operation-union)))

(define (extend-arithmetic extender base-arithmetic)
  (add-arithmetics base-arithmetic (extender base-arithmetic)))

(define (install-arithmetic! arithmetic)
    (install-package! (arithmetic->package arithmetic)))

;; (define (with-arithmetic arithmetic thunk)
;;   (with-installed-package! (arithmetic->package arithmetic)
;;                            thunk))

(define (arithmetic->package arithmetic)
  (make-package (arithmetic-name arithmetic)
    (arithmetic->bindings arithmetic
                          (+-like '+ 'additive-identity)
                          (--like '- 'negate)
                          (+-like '* 'multiplicative-identity)
                          (--like '/ 'invert)
                          (comparator '<)
                          (comparator '=)
                          (comparator '>)
                          (comparator '<=)
                          (comparator '>=)
                          (min-like 'min)
                          (min-like 'max))))

(define (arithmetic->bindings arithmetic . modifications)
  (let ((overrides
         (filter-map (lambda (modification)
                       (and modification
                            (modification arithmetic)))
                     modifications)))
    (map (lambda (operator)
           (cons operator
                 (make-installable-procedure operator
                                             arithmetic
                                             overrides)))
         (filter operator-installable?
                 (arithmetic-operators arithmetic)))))

(define *arithmetic-procedure-table* (make-hash-table))
(define (arithmetic-procedure? x) (hash-table-exists? *arithmetic-procedure-table* x))
(define (arithmetic-procedure-metadata x) (hash-table-ref *arithmetic-procedure-table* x))
(define (set-arithmetic-procedure-metadata! arithmetic-procedure metadata)
  (hash-table-set! *arithmetic-procedure-table* arithmetic-procedure metadata))

(define (make-installable-procedure operator arithmetic
                                    overrides)
  (let* ((operation
          (arithmetic-operation operator arithmetic))
         (procedure (operation-procedure operation)))
    (let ((override
	   (assq operator overrides)
           ;; (and (not (eqv? (get-implementation-value operator)
           ;;                 procedure))
           ;;      (assq operator overrides))
	   ))
      (if override
          (let ((procedure*
                 (make-installable-operation-procedure
                  procedure
                  (cdr override))))
            (set-arithmetic-procedure-metadata! procedure*
                                                procedure)
            procedure*)
          procedure))))

(define (+-like operator identity-name)
  (lambda (arithmetic)
    (let ((binary-operation
           (find-arithmetic-operation operator arithmetic)))
      (and binary-operation
           (let ((binary
                  (operation-procedure binary-operation))
                 (get-identity
                  (identity-name->getter identity-name
                                         arithmetic)))
             (cons operator
                   (lambda args
                     (case (length args)
                       ((0) (get-identity))
                       ((1) (car args))
                       (else (pairwise binary args))))))))))

(define (identity-name->getter identity arithmetic)
  (let ((constant
         (find-arithmetic-constant identity arithmetic)))
    (if (default-object? constant)
        (lambda ()
          (error "No identity for this arithmetic:" identity))
        (lambda ()
          constant))))

(define (--like operator inversion-operator)
  (lambda (arithmetic)
    (let ((binary-operation
           (find-arithmetic-operation operator arithmetic))
          (unary-operation
           (find-arithmetic-operation inversion-operator
                                      arithmetic)))
      (and binary-operation
           unary-operation
           (let ((binary
                  (operation-procedure binary-operation))
                 (unary
                  (operation-procedure unary-operation)))
             (cons operator
                   (lambda (arg . args)
                     (if (null? args)
                         (unary arg)
                         (pairwise binary
                                   (cons arg args))))))))))

(define (comparator operator)
  (lambda (arithmetic)
    (let ((operation
           (find-arithmetic-operation operator arithmetic)))
      (and operation
           (let ((binary
                  (operation-procedure operation)))
             (cons operator
                   (lambda args
                     (or (< (length args) 2)
                         (let loop ((args args))
                           (and (binary (car args) (cadr args))
                                (or (not (pair? (cddr args)))
                                    (loop (cdr args)))))))))))))

(define (min-like operator)
  (lambda (arithmetic)
    (let ((operation
           (find-arithmetic-operation operator arithmetic)))
      (and operation
           (let ((binary (operation-procedure operation)))
             (cons operator
                   (lambda (arg . args)
                     (if (null? args)
                         arg
                         (pairwise binary
                                   (cons arg args))))))))))

(define (pairwise binary args)
  (let loop
      ((args (cddr args))
       (result (binary (car args) (cadr args))))
    (if (null? args)
        result
        (loop (cdr args)
              (binary result (car args))))))

(use-modules (system repl repl))

(define (get-implementation-value name)
  (let* ((module (resolve-module '(guile)))
         (var (module-variable module name)))
    (if var
        (variable-ref var)
        (error "Variable not found" name))))

(define (get-value name)
  (let ((current-module (current-module))
        (guile-module (resolve-module '(guile))))
    (cond
     ((module-defined? current-module name)
      (module-ref current-module name))
     ((module-variable guile-module name) =>
      (lambda (var) (variable-ref var)))
     (else
      (error "Variable not found" name)))))

(define numeric-arithmetic
  (make-arithmetic 'numeric number? (list)
		   (lambda (name)
		     (case name
		       ((additive-identity) 0)
		       ((multiplicative-identity) 1)
		       (else (make-default-object))))
		   (lambda (operator)
		     (simple-operation operator
				       number?
				       (get-value
					(operator->procedure-name operator))))))

(define boolean-arithmetic
  (make-arithmetic 'boolean boolean? '()
    (lambda (name)
      (case name
        ((additive-identity) #f)
        ((multiplicative-identity) #t)
        (else (make-default-object))))
    (lambda (operator)
      (let ((procedure
             (case operator
               ((+) (lambda (b1 b2) (or b1 b2)))
               ((*) (lambda (b1 b2) (and b1 b2)))
               ((-) (lambda (b1 b2) 
                      (error "Boolean binary - not defined"
                             b1 b2)))
               ((<) (lambda (b1 b2) (and (not b1) b2)))
               ((<=) (lambda (b1 b2) (or (not b1) b2)))
               ((=) (lambda (b1 b2) (eq? b1 b2)))
               ((>=) (lambda (b1 b2) (or b1 (not b2))))
               ((>) (lambda (b1 b2) (and b1 (not b2))))
               ((positive?) (lambda (b) b))
               ((zero?) (lambda (b) (not b)))
               ((max) (lambda (b1 b2) (or b1 b2)))
               ((min) (lambda (b1 b2) (and b1 b2)))
               ((negate) (lambda (b) (not b)))
               (else (lambda args
                       (error "Operator undefined in Boolean"
                              operator args))))))
        (and procedure
             (simple-operation operator boolean? procedure))))))






(define-record-type <package>
  (make-package name bindings-alist)
  package?
  (name package-debug-name)
  (bindings-alist package-bindings))

(define (package-names package)
  (map car (package-bindings package)))

(define (package-value package name)
  (let ((p (assq name (package-bindings package))))
    (if p
        (cdr p)
        (error "Unknown binding name:" name))))

;; (define (similar-packages? p1 p2)
;;   (lset= eq? (package-names p1) (package-names p2)))

(define (package-installer module)
  (lambda (package)
    (map (lambda (binding)
           (match binding
             ((name . value)
              (let ((old-value
                     (if (module-variable module name)
                         (module-ref module name)
                         #f)))
                (module-define! module name value)
                (cons name old-value)))))
         (package-bindings package))))

(define install-package! (package-installer (current-module)))








;;; data model

(define-record-type <nothing>
  (make-nothing)
  %nothing?)
(define (print-nothing nothing port)
  (display "#<nothing>" port))
(set-record-type-printer! <nothing> print-nothing)
(define nothing (make-nothing))
(define (nothing? x) (eq? x nothing))

(define-record-type <contradiction>
  (make-contradiction details)
  contradiction?
  (details contradiction-details))

(define (print-contradiction contradiction port)
  (format port "#<contradiction ~a>"
          (contradiction-details contradiction)))

(set-record-type-printer! <contradiction> print-contradiction)

(define contradiction (make-contradiction nothing))

;; (define get-base-value
;;   (simple-generic-procedure 'get-base-value 1 base-layer-value))


(define (~<? x y) (and (< x y) (not (~=? x y))))
(define (~>? x y) (and (> x y) (not (~=? x y))))
(define (~=? x y)
  (if (and (exact? x) (exact? y))
      (= x y)
      (< (magnitude (- x y)) 1e-10)))

(define (equivalent? object1 object2)
  (or (equal? object1 object2)
      (g:equivalent? object1 object2)))

(define-generic g:equivalent?)
(define-method (g:equivalent? a b) #f)
(define-method (g:equivalent? (a <number>) (b <number>))
  (~=? a b))

(define-generic value-implies?)
(define value-implies? eqv?)

(define-generic strongest-value)
(define (strongest-value object) object)

(define-generic cell-merge)
(define-method (cell-merge content increment)
  (cond ((nothing? content) increment)
	((nothing? increment) content)
	((contradiction? content) content)
	((contradiction? increment) increment)
	((equivalent? content increment) content)
	(else (make-contradiction (format #f "~a couldn't merge with ~a" content increment)))))

;; ;; Like merge but only on added layers.
;; (define (merge-metadata content increment)
;;   (declare (ignore increment))
;;   content)

;; ;; Like merge-layered but only on added layers.
;; (define merge-metadata-layered
;;   (make-layered-procedure 'merge-metadata 2 merge-metadata))

;;; Intervals
(use-modules (oop goops))

(define-class <interval> ()
  (low #:init-keyword #:low
       #:accessor interval-low)
  (high #:init-keyword #:high
        #:accessor interval-high))

(define-method (display (obj <interval>) (port <port>))
  (format port "[~a, ~a]" (interval-low obj) (interval-high obj)))

(define-method (write (obj <interval>) (port <port>))
  (format port "#<<interval> ~a>" (with-output-to-string
                                    (lambda ()
                                      (display obj)))))
(define-method (initialize (obj <interval>) initargs)
  (next-method)
  (unless (and (slot-bound? obj 'low)
               (slot-bound? obj 'high))
    (error "Both low and high must be provided")))

(define (make-interval low high)
  (make <interval> #:low low #:high high))

(define (interval? obj)
  (is-a? obj <interval>))

(register-predicate! interval? 'interval)

(define (->interval x)
  (if (interval? x) x (make-interval x x)))

(define (empty-interval? x)
  (> (interval-low x) (interval-high x)))

(define (intersect-intervals x y)
  (make-interval
   (max (interval-low x) (interval-low y))
   (min (interval-high x) (interval-high y))))

(define (subinterval? interval-1 interval-2)
  (and (>= (interval-low interval-1)
             (interval-low interval-2))
       (<= (interval-high interval-1)
             (interval-high interval-2))))

(define (within-interval? number interval)
  (<= (interval-low interval) number (interval-high interval)))



(define (add-interval x y)
  (make-interval (+ (interval-low x) (interval-low y))
                 (+ (interval-high x) (interval-high y))))

(define (sub-interval x y)
  (make-interval (- (interval-low x) (interval-high y))
                 (- (interval-high x) (interval-low y))))

(define (mul-interval x y)
  (let ((ll (* (interval-low x) (interval-low y)))
        (lh (* (interval-low x) (interval-high y)))
        (hl (* (interval-high x) (interval-low y)))
        (hh (* (interval-high x) (interval-high y))))
    (make-interval (min ll lh hl hh)
                   (max ll lh hl hh))))

(define (div-interval x y)
  (mul-interval x
                (make-interval (/ 1.0 (interval-high y))
                               (/ 1.0 (interval-low y)))))

(define (square-interval x)
  (make-interval (square (interval-low x))
                 (square (interval-high x))))

(define (sqrt-interval x)
  (make-interval (sqrt (interval-low x))
                 (sqrt (interval-high x))))

;;; exp log sin cos tan
(define (exp-interval x)
  (make-interval (exp (interval-low x))
                 (exp (interval-high x))))

(define (log-interval x)
  (if (<= (interval-low x) 0)
      (error "Bad range log interval" x))
  (make-interval (log (interval-low x))
                 (log (interval-high x))))

;; Fix this!  These ranges are safe for examples, but really
;; should be worked out carefully.

(define :pi/2 (acos 0))
(define :pi (* 2 :pi/2))
(define :-pi/2 (- :pi/2))

(define (sin-interval x)
  (if (not (and (<= :-pi/2 (interval-low x) :pi/2)
                (<= :-pi/2 (interval-high x) :pi/2)))
      (error "Bad range sin interval" x))
  (make-interval (sin (interval-low x))
                 (sin (interval-high x))))

(define (asin-interval x)
  (if (not (and (<= -1 (interval-low x) +1)
                (<= -1 (interval-high x) +1)))
      (error "Bad range asin interval" x))
  (make-interval (asin (interval-low x))
                 (asin (interval-high x))))

(define (cos-interval x)
  ;; Fix this!
  (if (not (and (<= 0 (interval-low x) :pi)
                (<= 0 (interval-high x) :pi)))
      (error "Bad range cos interval" x))
  (make-interval (cos (interval-high x))
                 (cos (interval-low x))))

(define (acos-interval x)
  (if (not (and (<= -1 (interval-low x) +1)
                (<= -1 (interval-high x) +1)))
      (error "Bad range acos interval" x))
  (make-interval (acos (interval-high x))
                 (acos (interval-low x))))

(define (tan-interval x)
  (if (not (and (< :-pi/2 (interval-low x) :pi/2)
                (< :-pi/2 (interval-high x) :pi/2)))
      (error "Bad range tan interval" x))
  (make-interval (tan (interval-low x))
                 (tan (interval-high x))))

(define (atan-interval x)
  (make-interval (atan (interval-low x))
                 (atan (interval-high x))))

(define (sign x) (if (positive? x) 1 -1))

(define (sign-interval x)
  (let ((sl (sign (interval-low x)))
        (sh (sign (interval-high x))))
    (cond ((and (= sl 1) (= sh 1)) 1)
          ((and (= sl -1) (= sh -1)) -1)
          (else 0))))

(define (negate-interval y)
  (make-interval (- 0.0 (interval-high y))
                 (- 0.0 (interval-low y))))

(define (invert-interval y)
  (make-interval (/ 1.0 (interval-high y))
                 (/ 1.0 (interval-low y))))

(define (abs-interval x)
  (let ((al (abs (interval-low x)))
        (ah (abs (interval-high x))))
    (make-interval (min al ah) (max al ah))))

(define (interval=? x y)
  (and (= (interval-high x) (interval-high y))
       (= (interval-low x) (interval-low y))))

(define (interval<? x y)
  (< (interval-high x) (interval-low y)))

(define (interval>? x y)
  (> (interval-low x) (interval-high y)))

(define (interval<=? x y)
  (<= (interval-high x) (interval-low y)))

(define (interval>=? x y)
  (>= (interval-low x) (interval-high y)))

(define (interval-extender base-arithmetic)
  (make-arithmetic 'interval interval? (list numeric-arithmetic)
		   (lambda (name base-constant)
		     (make-default-object))
		   (lambda (operator base-operation)
		     (let ((operation
			    (case operator
			      ((+) add-interval)
			      ((-) sub-interval)
			      ((*) mul-interval)
			      ((/) div-interval)
			      ((=) interval=?)
			      ((<) interval<?)
			      ((>) interval>?)
			      ((<=) interval<=?)
			      ((>=) interval>=?)
			      ((square) square-interval)
			      ((sqrt) sqrt-interval)
			      ((sign) sign-interval)
			      ((negate) negate-interval)
			      ((invert) invert-interval)
			      ((abs) abs-interval)
			      ((exp) exp-interval)
			      ((log) log-interval)
			      ((sin) sin-interval)
			      ((asin) asin-interval)
			      ((cos) cos-interval)
			      ((acos) acos-interval)
			      ((tan) tan-interval)
			      ((atan) atan-interval)
			      (else #f))))
		       (and operation
			    (make-operation operator
					    (any-arg (operator-arity operator)
						     interval?
						     real?)
					    (lambda args
					      (apply operation
						     (map ->interval
							  args)))))))))


(define (+->interval value delta)
  (make-interval (- value delta) (+ value delta)))

(define (interval>+- interval)
  (let ((center
         (/ (+ (interval-high interval)
                   (interval-low interval))
              2)))
    `(+- ,center
         ,(- (interval-high interval) center))))


;; (define-method (atan (x <interval>))
;;   (make-interval (atan (interval-low x))
;;                  (atan (interval-high x))))

;; (define-method (+ (x <interval>) (y <interval>))
;;   (make-interval (+ (interval-low x) (interval-low y))
;;                  (+ (interval-high x) (interval-high y))))

;; (define-method (- (x <interval>) (y <interval>))
;;   (make-interval (- (interval-low x) (interval-high y))
;;                  (- (interval-high x) (interval-low y))))

;; (define-method (* (x <interval>) (y <interval>))
;;   (let ((ll (* (interval-low x) (interval-low y)))
;;         (lh (* (interval-low x) (interval-high y)))
;;         (hl (* (interval-high x) (interval-low y)))
;;         (hh (* (interval-high x) (interval-high y))))
;;     (make-interval (min ll lh hl hh)
;;                    (max ll lh hl hh))))

;; (define-method (/ (x <interval>) (y <interval>))
;;   (mul-interval x
;;                 (make-interval (/ 1.0 (interval-high y))
;;                                (/ 1.0 (interval-low y)))))

;; (define-method (/ (x <real>) (y <interval>))
;;   (make-interval (/ x (interval-low y))
;; 		 (/ x (interval-high y))))

;; (define-method (* (x <real>) (y <interval>))
;;   (make-interval (* x (interval-low y))
;; 		 (* x (interval-high y))))


;; (define-method (/ (x <interval>) (y <real>))
;;   (make-interval (/ y (interval-low x))
;; 		 (/ y (interval-high x))))

;; (define-method (* (x <interval>) (y <real>))
;;   (make-interval (* y (interval-low x))
;; 		 (* y (interval-high x))))



(define-method (cell-merge (interval <interval>) (x <real>))
  (if (within-interval? x interval)
      x
      (make-contradiction 1)))

(define-method (cell-merge (content <interval>) (increment <interval>))
  (let ((new-range (intersect-intervals content increment)))
    (cond ((interval=? new-range content) content)
          ((interval=? new-range increment) increment)
          ((empty-interval? new-range) (make-contradiction "empty interval"))
          (else new-range))))

(define-method (cell-merge (content <real>) (increment <interval>))
  (if (within-interval? content increment)
      content
      (make-contradiction (format #f "content ~a couln't merge with interval ~a" content increment))))









(define-record-type <relations>
  (%make-relations name parent children)
  relations?
  (name relations-name)
  (parent relations-parent)
  (children relations-children set-relations-children!))

(define (print-relations relations port)
  (match relations
    (($ <relations> name parent children)
     (format port "#<relations ~a ↑ ~a ↓ ~a >"
             name parent children))))
(set-record-type-printer! <relations> print-relations)

(define current-parent (make-parameter #f))

(define (make-relations name)
  (%make-relations name (current-parent) '()))

(define (add-child! parent child)
  (when parent
    (set-relations-children! parent (cons child (relations-children parent)))))

(define-record-type <propagator>
  (%make-propagator relations inputs outputs activate)
  propagator?
  (relations propagator-relations)
  (inputs propagator-inputs)
  (outputs propagator-outputs)
  (activate propagator-activate))

(define (print-propagator propagator port)
  (match propagator
    (($ <propagator> ($ <relations> name) inputs outputs)
     (display "#<propagator " port)
     (display name port)
     (display " " port)
     (display inputs port)
     (display " -> " port)
     (display outputs port)
     (display ">" port))))
(set-record-type-printer! <propagator> print-propagator)

(define (default-find-strongest content) content)
(define (default-handle-contradiction cell) (values))


(define-record-type <cell>
  (%make-cell relations neighbors content strongest
              equivalent? merge find-strongest handle-contradiction)
  cell?
  (relations cell-relations)
  (neighbors cell-neighbors set-cell-neighbors!)
  (content cell-content set-cell-content!)
  (strongest cell-strongest set-cell-strongest!)
  ;; Dispatch table:
  (equivalent? cell-equivalent?)
  (merge cell-merge-procedure)
  (find-strongest cell-find-strongest)
  (handle-contradiction cell-handle-contradiction))

(define (print-cell cell port)
  (match cell
    (($ <cell> ($ <relations> name) _ _ strongest)
     (display "#<cell " port)
     (display name port)
     (display " " port)
     (display strongest port)
     (display ">" port))))
(set-record-type-printer! <cell> print-cell)

(define* (make-cell name #:key
                    (equivalent? equivalent?)
                    (merge cell-merge)
                    (find-strongest default-find-strongest)
                    (handle-contradiction default-handle-contradiction))
  (let ((cell (%make-cell (make-relations name) '() nothing nothing
                          equivalent? merge find-strongest
                          handle-contradiction)))
    (add-child! (current-parent) cell)
    (set! *all-cells* (cons cell *all-cells*))
    cell))

(define (cell-name cell)
  (relations-name (cell-relations cell)))

(define (add-cell-neighbor! cell neighbor)
  (set-cell-neighbors! cell (lset-adjoin eq? (cell-neighbors cell) neighbor)))

(define (add-cell-content! cell new)
  (let* ((content (cell-content cell))
	 (merge (cell-merge-procedure cell))
	 (content* (merge content new)))
    (set-cell-content! cell content*)
    (test-cell-content! cell)))

(define (test-cell-content! cell)
  (match cell
    (($ <cell> _ neighbors content strongest equivalent? merge
        find-strongest handle-contradiction)
     (let ((strongest* (find-strongest content)))
       (cond
        ;; New strongest value is equivalent to the old one.  No need
        ;; to alert propagators.
        ((equivalent? strongest strongest*)
         (set-cell-strongest! cell strongest*))
        ;; Uh oh, a contradiction!  Call handler.
        ((contradiction? strongest*)
         (set-cell-strongest! cell strongest*)
         (handle-contradiction cell))
        ;; Strongest value has changed.  Alert the propagators!
        (else
	 (set-cell-strongest! cell strongest*)
         (for-each alert-propagator! neighbors)))))))

(define (ensure-cell name value)
  (if (cell? value)
      value
      (let ((new-cell (make-cell name)))
        (add-cell-content! new-cell value)
        new-cell)))


(define (make-propagator name inputs outputs activate)
  (let ((propagator (%make-propagator (make-relations name)
                                      inputs outputs activate)))
    (add-child! (current-parent) propagator)
    (for-each (lambda (cell)
                (add-cell-neighbor! cell propagator))
              inputs)
    (alert-propagator! propagator)
    propagator))

(define (unusable-value? x)
  (or (nothing? x) (contradiction? x)))

(define (primitive-propagator name f)
  (match-lambda*
    ((inputs ... output)
     (define (activate)
       (let ((args (map cell-strongest inputs)))
         (unless (any unusable-value? args)
           (add-cell-content! output (apply f args)))))
     (make-propagator name inputs (list output) activate))))

(define (compound-propagator name inputs outputs build)
  (let ((built? #f))
    (define (maybe-build)
      (unless (or built?
                  (and (not (null? inputs))
                       (every unusable-value? (map cell-strongest inputs))))
        (parameterize ((current-parent (propagator-relations propagator)))
          (build)
	  (set! built? #t))))
    (define propagator (make-propagator name inputs outputs maybe-build))
    propagator))

(define (constraint-propagator name cells build)
  (compound-propagator name cells cells build))










(define-record-type <premise>
  (make-premise name believed? nogoods roots)
  premise?
  (name premise-name)
  (believed? premise-believed?)
  (nogoods premise-nogoods set-premise-nogoods!)
  (roots premise-roots set-premise-roots!))

(define (premise-add-root! premise root)
  (set-premise-roots! premise
		      (lset-adjoin eqv? (premise-roots premise) root)))

(define *premise-table* (make-hash-table))

(define (register-premise! name root)
  (let ((premise (make-premise name #t '() '())))
    (premise-add-root! premise root)
    (hash-table-set! *premise-table* name premise)
    name))


(define *scheduled-propagators* '())
(define (clear-scheduled-propagators!)
  (set! *scheduled-propagators* '()))
(define (add-scheduled-propagator! propagator)
  (set! *scheduled-propagators*
	(lset-adjoin eq? *scheduled-propagators* propagator)))
(define (scheduled-propagators-empty?) (null? *scheduled-propagators*))
(define (scheduled-propagators) (list-copy *scheduled-propagators*))
(define (exhaust-scheduled-propagators)
  (let ((propagators *scheduled-propagators*))
    (clear-scheduled-propagators!)
    (reverse propagators)))

(define propagators-ever-alerted '())
(define all-amb-propagators '())
(define *all-cells* '())
(define *number-of-calls-to-fail* 10)
(define *last-value-of-run*)

(define (initialize-scheduler)
  (clear-scheduled-propagators!)
  (set! propagators-ever-alerted '())
  (set! all-amb-propagators '())
  ;; (clear-relatable-hierarchy!)
  (set! *premise-table* (make-hash-table))
  (set! *last-value-of-run* #f)
  (set! *all-cells* '())
  (set! *number-of-calls-to-fail* 0)
  'ok)

(define (alert-propagator! propagator)
  (guarantee propagator? propagator 'alert-propagators!)
  (add-scheduled-propagator! propagator)
  (set! propagators-ever-alerted
        (lset-adjoin eq? propagators-ever-alerted propagator)))

(define (alert-propagators! propagators)
  (for-each alert-propagator! propagators))



(define *abort-process*
  (make-parameter
   (lambda (value)
     (set! *last-value-of-run* value)
     value)))

(define (abort-process value)
  ((*abort-process*) value))

(define (run)
  (if (not (scheduled-propagators-empty?))
      (set! *last-value-of-run*
            (call/cc
             (lambda (k)
               (parameterize ((*abort-process* k))
                 (run-scheduled))))))
  *last-value-of-run*)

(define (run-scheduled)
  (for-each (lambda (propagator)
	      ((propagator-activate propagator)))
            (exhaust-scheduled-propagators))
  (if (scheduled-propagators-empty?)
      'done
      (run-scheduled)))





(define (print-run-result result)
  (display result))

(define (tell! cell information . premises)
  (guarantee cell? cell 'tell!)
  (for-each (lambda (premise)
              (register-premise! premise cell))
            premises)
  (set! *last-value-of-run* 'done)
  (add-cell-content! cell
		     (if (null? premises)
			 information
			 information
			 ;; (supported information
			 ;; 	    (make-support-set premises)
			 ;; 	    'i-told-you-so)
			 ))
  (print-run-result (run)))




;;; Sugar

(define-syntax define-cell
  (syntax-rules ()
    ((define-cell symbol form)
     (define symbol
       (ensure-cell 'symbol form)))
    ((define-cell symbol)
     (define symbol
       (make-cell 'symbol)))))


(define-syntax let-cells
   (syntax-rules ()
     ((let-cells ((name expr) ...)
        form ...)
      (let ((name (ensure-cell 'name expr)) ...)
        form ...))
     ((let-cells (name ...)
        form ...)
      (let-cells ((name (make-cell 'name))...)
        form ...))))



(install-arithmetic! (extend-arithmetic interval-extender numeric-arithmetic))




(define :2pi (* 4 (acos 0)))
(define (degrees->radians degrees)
  (* (/ :2pi 360) degrees))
(define (radians->degrees radians)
  (* (/ 360 :2pi) radians))
(define (radians->dms radians)
  (d->dms (radians->degrees radians)))
(define (xms->x xms)
  (+ (car xms)
     (/ (cadr xms) 60)
     (/ (caddr xms) 3600)))
(define (x->xms x)
  (let* ((d (truncate x))
         (dd (- x d))
         (m (truncate (* 60 dd)))
         (ddm (- dd (/ m 60)))
         (s (* 3600 ddm)))
    (list d m s)))
(define dms->d xms->x)
(define d->dms x->xms)
(define (dms->radians dms)
  (degrees->radians (dms->d dms)))
(define (mas->radians mas)
  (dms->radians (list 0 0 (/ mas 1000))))
(define (radians->mas rad)
  (let ((dms (radians->dms rad)))
    (* 1000 (caddr dms))))
(define AU-in-meters 149597870700)
(define parsec-in-meters (/ AU-in-meters (tan (dms->radians (list 0 0 1)))))
(define (meters->parsecs m) (/ m parsec-in-meters))
(define (parsecs->meters pc) (* pc parsec-in-meters))

(define AU-in-parsecs
  (/ AU-in-meters parsec-in-meters))


(define p:tan (primitive-propagator 'p:tan tan))
(define p:atan (primitive-propagator 'p:atan atan))
(define p:* (primitive-propagator 'p:* *))
(define p:/ (primitive-propagator 'p:/ /))

(define (c:* x y product)
  (constraint-propagator 'c:*
			 (list x y product)
			 (lambda ()
			   (p:* x y product)
			   (p:/ product x y)
			   (p:/ product y x))))

(define (c:tan x y)
  (constraint-propagator 'c:tan
			 (list x y)
			 (lambda ()
			   (p:tan x y)
			   (p:atan y x))))


(define (c:parallax<->distance parallax distance)
  (constraint-propagator 'c:parallax<->distance
			 (list parallax distance)
			 (lambda ()
			   (let-cells (t)
				      (let-cells ((AU AU-in-parsecs))
						 (c:tan parallax t)
						 (c:* t distance AU))))))






(initialize-scheduler)
(define-cell Vega-parallax-distance)
(define-cell Vega-parallax)
(define p1 (c:parallax<->distance Vega-parallax Vega-parallax-distance))
(tell! Vega-parallax
       (+->interval (mas->radians 125)
                    (mas->radians 50))
       'FGWvonStruve1837)
(cell-content Vega-parallax-distance)
(interval>+- (cell-content Vega-parallax-distance))
;; (get-premises Vega-parallax-distance)
;; 'expect-value: '(support-set fgwvonstruve1837)





;; (define-cell in)
;; (define-cell out)
;; (initialize-scheduler)
;; (define p1 (c:tan in out))
;; (tell! in 1)
;; (cell-content out)

(initialize-scheduler)
(define-cell in)
(define-cell out)
(initialize-scheduler)
(define p1 (c:tan in out))
(tell! in 2)
(cell-content out)

(initialize-scheduler)
(define-cell in)
(define-cell out)
(define-cell times 3)
(initialize-scheduler)
(define p1 (p:* in times out))
(tell! in (make-interval 1 2))
(cell-content out)


;;; Kallax fitting

(define (kallax-width-from-count count)
  (let ((border 50)
	(inner-border 10)
	(fach 500))
    (+ (* 2 border)
       (* count fach)
       (* (1- count) inner-border))))

(map kallax-width-from-count (iota 5 1))

;; vorhanden width
;; kallax-width
;; fach-count


(initialize-scheduler)
(define-cell in1 1.1)
(define-cell in2)
(define-cell out)

(p:* in1 in2 out)
(tell! in2 3)
(cell-content out)



(cell-merge
 23
 (make-interval 20 30))

