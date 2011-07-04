#lang racket/base

(require srfi/1)
(require racket/pretty)

(require "graph.rkt")

(require (planet tonyg/ometa))
(require (only-in planet/resolver resolve-planet-path))
(require (only-in racket/path path-only))
(ometa-library-path (path-only (resolve-planet-path (list "ometa-boot.g" 'tonyg/ometa))))
(displayln (ometa-library-path))
(define-namespace-anchor mixfix)
(ometa-namespace-getter (lambda () (namespace-anchor->namespace mixfix)))

;; An Associativity is one of
;;  - 'left
;;  - 'right
;;  - 'non

;; An Operator is an (operator Associativity ListOf<Piece>)
(struct operator (associativity pieces) #:transparent)

;; A Piece is one of
;;  - '_
;;  - a Symbol (other than '_), referring to a terminal
;;  - a String, referring to a terminal
;;  - a (list Symbol), referring to a nonterminal

;; A GroupName is a Symbol

;; A Grouping is a (grouping GroupName ListOf<Operator>)
(struct grouping (name operators)
	#:omit-define-syntaxes
	#:transparent
	#:constructor-name grouping*)

(define (grouping name . operators)
  (grouping* name operators))

;; A Precedence is a (precedence GroupName GroupName)
(struct precedence (high low) #:transparent)

;; A Grammar is a (grammar Symbol ListOf<Grouping> ListOf<Precedence>)
(struct grammar (start-symbol groupings grouping-names precedence-graph)
	#:omit-define-syntaxes
	#:transparent
	#:constructor-name grammar*)

(define-syntax Left (syntax-rules () ((_ piece ...) (operator 'left (list 'piece ...)))))
(define-syntax Right (syntax-rules () ((_ piece ...) (operator 'right (list 'piece ...)))))
(define-syntax Non (syntax-rules () ((_ piece ...) (operator 'non (list 'piece ...)))))
(define-syntax Prefix (syntax-rules () ((_ piece) (operator 'right (list 'piece '_)))))
(define-syntax Postfix (syntax-rules () ((_ piece) (operator 'left (list '_ 'piece)))))

;; terminal? : Piece -> Boolean
(define (terminal? piece)
  (not (eq? piece '_)))

(define (operator-fixity-predicate first-terminal last-terminal)
  (lambda (o)
    (and (eqv? first-terminal (terminal? (first (operator-pieces o))))
	 (eqv? last-terminal (terminal? (last (operator-pieces o)))))))

(define operator-closed? (operator-fixity-predicate #t #t))
(define operator-prefix? (operator-fixity-predicate #t #f))
(define operator-postfix? (operator-fixity-predicate #f #t))
(define operator-infix? (operator-fixity-predicate #f #f))

(define (operator-associativity-predicate value)
  (lambda (o)
    (and (operator-infix? o)
	 (eq? value (operator-associativity o)))))

(define operator-non? (operator-associativity-predicate 'non))
(define operator-left? (operator-associativity-predicate 'left))
(define operator-right? (operator-associativity-predicate 'right))

(define (operator-pieces/trim o)
  (let ((p (operator-pieces o)))
    (when (eq? (first p) '_)
      (set! p (cdr p)))
    (when (eq? (last p) '_)
      (set! p (drop-right p 1)))
    p))

(define (variant** name group-name)
  (string->symbol (string-append (symbol->string group-name) "::" name)))

(define (grouping->productions g group-name)
  (let ((grouping (find (lambda (gr) (eq? group-name (grouping-name gr)))
			(grammar-groupings g)))
	(tighter-groups (let ((upstream (graph-edges-from (grammar-precedence-graph g) group-name)))
			  (filter (lambda (n) (memq n upstream)) (grammar-grouping-names g))))
	(start-symbol (grammar-start-symbol g)))
    (define (make-or alts)
      (cond
       ((null? alts) '(FAIL))
       ((null? (cdr alts)) (car alts))
       (else `(or ,@alts))))
    (define (make-seq ps)
      (cond
       ((null? ps) '(FAIL))
       ((null? (cdr ps)) (car ps))
       (else `(seq ,@ps))))
    (define (op-clause pred)
      (map (lambda (o)
	     (make-seq (map (lambda (piece)
			      (cond
			       ((eq? piece '_) `(apply ,start-symbol))
			       ((and (list? piece) (null? (cdr piece))) `(apply ,(car piece)))
			       (else `(exactly ,piece))))
			    (operator-pieces/trim o))))
	   (filter pred (grouping-operators grouping))))
    (define (variant* name [group-name group-name])
      (variant** name group-name))
    (define (variant name [group-name group-name])
      `(apply ,(variant* name group-name)))
    (let ((up-alts (map (lambda (other-group) (variant "hat" other-group))
			tighter-groups))
	  (closed-alts (op-clause operator-closed?))
	  (non-alts (op-clause operator-non?))
	  (prefix-alts (op-clause operator-prefix?))
	  (right-alts (op-clause operator-right?))
	  (postfix-alts (op-clause operator-postfix?))
	  (left-alts (op-clause operator-left?)))
      (define (care alt condition)
	(if condition
	    (list alt)
	    '()))
      (define (v? alts)
	(pair? alts))
      (let ((want-right (and (v? up-alts)
			     (or (v? prefix-alts)
				 (v? right-alts))))
	    (want-left (and (v? up-alts)
			    (or (v? postfix-alts)
				(v? left-alts))))
	    (want-non (and (v? up-alts)
			   (v? non-alts))))
	`((,(variant* "hat") ,(make-or (append (care (make-seq (list (variant "op-closed")))
						     (v? closed-alts))
					       (care (make-seq (list (variant "up")
								     (variant "op-non")
								     (variant "up")))
						     want-non)
					       (care (make-seq (list `(many1 ,(variant "right"))
								     (variant "up")))
						     want-right)
					       (care (make-seq (list (variant "up")
								     `(many1 ,(variant "left"))))
						     want-left))))
	  ,@(care `(,(variant* "right") ,(make-or (append (care (variant "op-pre")
								(v? prefix-alts))
							  (care (make-seq
								 (list (variant "up")
								       (variant "op-right")))
								(v? right-alts)))))
		  want-right)
	  ,@(care `(,(variant* "left") ,(make-or (append (care (variant "op-post")
							       (v? postfix-alts))
							 (care (make-seq 
								(list (variant "op-left")
								      (variant "up")))
							       (v? left-alts)))))
		  want-left)
	  ,@(care `(,(variant* "up") ,(make-or up-alts)) (v? up-alts))
	  ,@(care `(,(variant* "op-closed") ,(make-or closed-alts)) (v? closed-alts))
	  ,@(care `(,(variant* "op-non") ,(make-or non-alts)) want-non)
	  ,@(care `(,(variant* "op-pre") ,(make-or prefix-alts)) (v? prefix-alts))
	  ,@(care `(,(variant* "op-right") ,(make-or right-alts)) (v? right-alts))
	  ,@(care `(,(variant* "op-post") ,(make-or postfix-alts)) (v? postfix-alts))
	  ,@(care `(,(variant* "op-left") ,(make-or left-alts)) (v? left-alts)))))))

(define (grammar->ometa g)
  `((,(grammar-start-symbol g) (or ,@(map (lambda (grouping)
					    `(apply ,(variant** "hat"
								(grouping-name grouping))))
					  (grammar-groupings g))))
    ,@(append-map (lambda (grouping) (grouping->productions g (grouping-name grouping)))
		  (grammar-groupings g))))

(define (grammar start-symbol groupings precedences)
  (let* ((graph (make-graph (map (lambda (p) (list (precedence-low p)
						   (precedence-high p)))
				 precedences)))
	 (sorted-grouping-names (graph-topological-sort graph)))
    (grammar* start-symbol
	      (map (lambda (n) (find (lambda (gr) (eq? n (grouping-name gr))) groupings))
		   sorted-grouping-names)
	      sorted-grouping-names
	      graph)))

;;---------------------------------------------------------------------------

(define G
  (grammar 'expr
	   (list (grouping 'and
			   (Right _ ^ _))
		 (grouping 'eq
			   (Non _ == _))
		 (grouping 'add
			   (Left _ + _)
			   (Left _ - _))
		 (grouping 'not
			   (Postfix !))
		 (grouping 'top
			   (Non (variable))
			   (Non (literal))
			   (Non "(" _ ")"))
		 (grouping 'if
			   (Non if _ then _ else _)))
	   (list (precedence 'top 'if)
		 (precedence 'top 'and)
		 (precedence 'top 'not)
		 (precedence 'top 'eq)
		 (precedence 'top 'add)
		 (precedence 'not 'eq)
		 (precedence 'add 'eq)
		 (precedence 'eq 'and))))

(pretty-print (grammar->ometa G))

(simple-ometa-driver `((variable (seq (bind n (anything))
				      (action (if (symbol? n)
						  n
						  (error 'expected 'variable)))))
		       (literal (seq (bind n (anything))
				     (action (if (number? n)
						 n
						 (error 'expected 'literal)))))
		       ,@(grammar->ometa G))
		     'expr
		     '(1 - 2 + 3 == 2 + 0)
		     (lambda (sv tail err)
		       (pretty-print `((sv ,sv)
				       (tail ,(input-stream->list tail))
				       (err ,(format-ometa-error err)))))
		     report-ometa-error)
