#lang racket/base

(require srfi/1)
(require racket/pretty)

;; An Associativity is one of
;;  - 'left
;;  - 'right
;;  - 'non

;; An Operator is an (operator Associativity ListOf<Piece>)
(struct operator (associativity pieces) #:transparent)

;; A Piece is one of
;;  - '_
;;  - a Symbol (other than '_)

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
(struct grammar (start-symbol groupings precedences) #:transparent)

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

(define (grouping->productions g group-name)
  (let ((grouping (find (lambda (gr) (eq? group-name (grouping-name gr)))
			(grammar-groupings g)))
	(tighter-groups (map precedence-high
			     (filter (lambda (pr) (eq? group-name (precedence-low pr)))
				     (grammar-precedences g))))
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
			      (if (eq? piece '_)
				  start-symbol
				  `(t ,piece)))
			    (operator-pieces/trim o))))
	   (filter pred (grouping-operators grouping))))
    (let ((up-alts (map (lambda (other-group)
			  `(hat ,other-group))
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
	`((def (hat ,group-name) ,(make-or (append (care (make-seq (list `(op-closed ,group-name)))
							 (v? closed-alts))
						   (care (make-seq (list `(up ,group-name)
									 `(op-non ,group-name)
									 `(up ,group-name)))
							 want-non)
						   (care (make-seq (list `(-> ,group-name)
									 `(up ,group-name)))
							 want-right)
						   (care (make-seq (list `(up ,group-name)
									 `(<- ,group-name)))
							 want-left))))
	  ,@(care `(def (-> ,group-name) ,(make-or (append (care `(op-prefix ,group-name)
								 (v? prefix-alts))
							   (care (make-seq
								  (list `(up ,group-name)
									`(op-right ,group-name)))
								 (v? right-alts)))))
		  want-right)
	  ,@(care `(def (<- ,group-name) ,(make-or (append (care `(op-postfix ,group-name)
								 (v? postfix-alts))
							   (care (make-seq 
								  (list `(op-left ,group-name)
									`(up ,group-name)))
								 (v? left-alts)))))
		  want-left)
	  ,@(care `(def (up ,group-name) ,(make-or up-alts))
		  (v? up-alts))
	  ,@(care `(def (op-closed ,group-name) ,(make-or (op-clause operator-closed?)))
		  (v? closed-alts))
	  ,@(care `(def (op-non ,group-name) ,(make-or (op-clause operator-non?)))
		  want-non)
	  ,@(care `(def (op-prefix ,group-name) ,(make-or (op-clause operator-prefix?)))
		  (v? prefix-alts))
	  ,@(care `(def (op-right ,group-name) ,(make-or (op-clause operator-right?)))
		  (v? right-alts))
	  ,@(care `(def (op-postfix ,group-name) ,(make-or (op-clause operator-postfix?)))
		  (v? postfix-alts))
	  ,@(care `(def (op-left ,group-name) ,(make-or (op-clause operator-left?)))
		  (v? left-alts)))))))

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
			   (Non b)
			   (Non n)
			   (Non OPAREN _ CPAREN))
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

(for-each (lambda (grouping)
	    (pretty-print (grouping->productions G (grouping-name grouping))))
	  (grammar-groupings G))
