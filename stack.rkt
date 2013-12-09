#lang racket

(require racket/mpair)

(provide Retrieve-stack)
(provide Push-stack)
(provide Push-void)
(provide Modify-stack)

;domain: any list, non-negative integer
;range: any/c
(define (Retrieve-stack stk n) 
  ((lambda(stack ref)(list-ref stack ref)) stk n))

; Retrieve-stack tester
;;;(Retrieve-stack (list 4 5 6) 2)


;domain: any list, any value
;returns any list
(define (Push-stack stk v)
  ((lambda(stack value) (cons value stack)) stk v))

; Push-stack tester
; use (void 0) to push void into the stack
;;;(Push-stack (list 10 11 12) (void 0))


(define (Push-void stk n)
  (cond
    [(eq? n 0) stk]
    [else
     (Push-void (cons (void 0) stk) (- n 1))]))

; Push-void tester
;;;(Push-void (list 1 2 3) 1)




;Modify Stack : converts the list into mutable list
;domain : any list, non-negative integer, any/c
;range : any list
(define (Modify-stack stk n v)
  (cond
    [(eq? n 0)
     (define mstk (list->mlist stk))
     (set-mcar! mstk v) ;Changes the mutable pair mstk so that its first element is v.
     (mlist->list mstk)]
    [else 
     (cons (car stk)
                (Modify-stack (cdr stk) (- n 1) v))]))

;Modify Tester
;;;(Modify-stack (list 1 2 3 4 5) 3 "hello")


