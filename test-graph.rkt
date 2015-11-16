#lang racket/base
;; Copyright 2011 Tony Garnock-Jones <tonyg@leastfixedpoint.com>
;;
;; Licensed under the Apache License, Version 2.0 (the "License");
;; you may not use this file except in compliance with the License.
;; You may obtain a copy of the License at
;;
;;     http://www.apache.org/licenses/LICENSE-2.0
;;
;; Unless required by applicable law or agreed to in writing, software
;; distributed under the License is distributed on an "AS IS" BASIS,
;; WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
;; See the License for the specific language governing permissions and
;; limitations under the License.

(require rackunit)
(require "graph.rkt")
(require srfi/1)

;; Short loop
(check-exn exn:fail? (lambda () (graph-topological-sort (make-graph '((a a))))))

;; Longer loop
(check-exn exn:fail?
	   (lambda ()
	     (graph-topological-sort (make-graph '((c d) (a b) (d a) (b c) (a d) (e d))))))

;; Loop and no loop
(check-exn exn:fail?
	   (lambda ()
	     (graph-topological-sort (make-graph '((a b) (b c) (c d) (e f) (f g) (g e))))))

(define (topological-sort-valid edges)
  (let ((s (graph-topological-sort (make-graph edges))))
    (define (precedes? x y)
      (< (list-index (lambda (v) (eq? v x)) s)
	 (list-index (lambda (v) (eq? v y)) s)))
    (map (lambda (e) (precedes? (car e) (cadr e)))
	 edges)))

;; Disjoint graph
(check-equal? (topological-sort-valid '((a b) (b c) (c d) (e f) (f g) (g h)))
	      (make-list 6 #t))

(check-equal? (topological-sort-valid '((c d) (a b) (b c) (a d) (e d)))
	      (make-list 5 #t))

(check-equal? (graph-topological-sort (make-graph '())) '())
