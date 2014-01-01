#lang racket

;; 0CFA inspired by David Van Horn and Matthew Might's paper:
;; "Systematic abstraction of abstract machines."
;; Journal of Functional Programming. 2012.

;; CESK style interpretation inspired by Matthew Might's 
;; concrete interpreter : http://matt.might.net/articles/cesk-machines/

;; Abstract interpretation inspired by Matthew Might's 
;; abstract interpreter : http://matt.might.net/articles/intro-static-analysis/

;; Author: Mayur Maheshwari 
;;        (mayurm@cs.utah.edu)


; Auxiliary functions:

; Global mutable hash-map for store
(define store-map (make-hash))

; Initial version to the store
(hash-set! store-map 'version 0)

; Finds a #t value in a list of booleans
; got-true : [value ...] -> boolean 
(define (got-true? lst)
    (and (not (null? lst))
         (or (eq? #t (car lst))
             (got-true? (cdr lst)))))


; Weak updates to store
; Updates are joined
; Duplicate update values are eliminated
; update-store : addr value -> Updated global store-map
(define (update-store x y)
  (cond
    [(hash-has-key? store-map x)
     (define old (hash-ref store-map x))
     (cond
       [(list? y)
        (if (or (eqv? (car y) 'Ar)
                (eqv? (car y) 'letk)
                (eqv? (car y) 'Fn)
                (eqv? (car y) 'if))
            (cond
            [(not (member y old))
             (set! old (cons y old))])
            (for ([new y])
              (cond
                [(not (member new old))
                 (set! old (cons new old))])))
        (hash-set! store-map x old)]
       [else
        (cond
          [(not (member y old))
           (set! old (cons y old))
           (hash-set! store-map x old)])])]
    [else (hash-set! store-map x (list y))]))



; A-Normal Form:

; <lam> ::= (λ (<var>) <exp>)

; <aexp> ::= <integer>
;         |  <var>
;         |  #t | #f
;         |  (<prim> <aexp> ...)

; <cexp> ::= (if <aexp> <exp> <exp>)
;         |  (letrec ([<var> <aexp>] ...) <exp>)
;         |  (<aexp> <aexp> ...)

; <exp> ::= <cexp>
;        |  <aexp>
;        |  (let ([<var> <exp>]) <exp>)


; add a while construct to Racket:
(define-syntax while 
  (syntax-rules ()
    [(_ cond body ...)
     ;=>
     (letrec [(loop (λ ()
                      (when cond
                        body ...
                        (loop))))]
       (loop))]))


; atom? : exp -> boolean?
(define (atom? exp)
  (match exp
    [`(λ ,_ ,_)   #t]
    [(? symbol?)    #t]
    [(? boolean?)   #t]
    [(? integer?)   #t]
    [(cons (? prim?) _)  #t]
    [else           #f]))

; prim? : symbol? -> boolean?
(define (prim? exp)
  (case exp
    [(+ - * = void) #t]
    [else      #f]))


; CESK machine state:
(struct astate {control        ; exp
                store-version  ; store version
                continuation}  ; kont
  #:transparent) ; enable low-level access to struct fields


; σ : store version

; value = list of (integer + boolean + clo)

; clo ::= (clo <lam>)

; κ : kont ::= (letk <var> <exp> <kont-addr>)
;           |  (Ar <exp> <kont-addr>)
;           |  (Fn <exp> <kont-addr>)
;           |  (if <exp0> <exp1> <kont-addr> )
;           |  halt

; addr = Variable names to store list 
;        of values flowing into them ;
;        Application (e0 e1) to store 
;        kontinuations at call sites ;
;        Unique symbols using gensym to 
;        store continuations created w/ if and let stmts.



; apply-kont : kont [value ...] store-version 
; -> 
;   (display answer)
; | [astates ...]
(define (apply-kont κ value σ)
  (match κ
    ; Apply the halt continuation:
    ['halt
     (display `(answer ,value ,σ))]
    
    
    ; Apply the if continuation and branch
    [`(if ,e0 ,e1 ,a)
     (if(got-true? value)
        (for*/list ([κ (hash-ref store-map a)])
          (astate e0 σ κ))
        (for*/list ([κ (hash-ref store-map a)])
          (astate e1 σ κ)))]

    
    ; Apply the argument continuation
    [`(Ar ,e ,a)
     (for*/list ([v value])
       (astate e σ `(Fn ,v ,a)))]
    
    
    ; Apply the procedure continuation
    [`(Fn ,f ,a)
     (apply-proc f value σ a)]
    
    
    ; Resume execution:
    [`(letk ,v ,e ,a)
     
     (update-store v value)
     
     ;update store version
     (define new-ver (+ (hash-ref store-map 'version) 1))
     (hash-set! store-map 'version new-ver)
     
     (for*/list ([κ (hash-ref store-map a)])
       (astate e new-ver κ))]))


; prim->proc : symbol? -> procedure?
(define (prim->proc prim)
  (match prim
    ['+    +]
    ['-    -]
    ['*    *]
    ['=    =]
    ['void void]))

(define (math opr)
  (λ(s) (apply (prim->proc opr) s)))


                   
; eval-atom : aexp 
; -> 
; value | [value ...]
(define (eval-atom atom)
  (match atom
    [(? symbol?)    (hash-ref store-map atom)]
    [(? boolean?)   atom]
    [(? integer?)   atom]
    
    ; Apply primary operations on [value ...] 
    ; Use permutation on the lists
    ; Assumption: Input of 2 variables (2 lists of values)
    [(cons (and prim (? prim?)) rest)
     ; =>
     (let ([args (map (eval-atom/curry) rest)])
       (define new-args (for/list ([a args])
                          (if (list? a)
                              a
                              (list a))))
       (define args-list (for*/list ([p (car new-args)]
                                     [q (second new-args)])
                           (list p q)))
       (map (math prim) args-list))]
       
    [`(λ ,_ ,_) 
     ; =>
     `(clo ,atom)]
    
    [else           (error "unknown atom")]))

; eval-atom/curry :-> aexp -> value
(define (eval-atom/curry)
  (λ (atom)
    (eval-atom atom)))



; ainject : exp -> astate
(define (ainject exp)
  (astate exp 0 'halt))

; apply-proc : value [value ...] store-version kont-addr -> [astate ...]
(define (apply-proc proc args σ a)
    
    (match proc
      ; apply a closure:
      [`(clo (λ ,vars ,body))
       ; =>    
       ; Assumption : Single formal parameter
       (update-store (car vars) args)
     
       ;update store version
       
       ;update store version
       (define new-ver (+ (hash-ref store-map 'version) 1))
       (hash-set! store-map 'version new-ver)
       
       (for*/list ([κ (hash-ref store-map a)])
         (astate body new-ver κ))]))


; step : astate -> (astate + answer)
(define (astep ς)
  (match ς
    
    ; return:
    [(astate (and atom (? atom?)) σ κ)
     ; =>
     ; evaluate the return value:
     (define return-value (eval-atom atom))
       
     (apply-kont κ return-value σ)]
        
    ; conditional evaluation:
    [(astate `(if ,cond ,cons ,alt) σ κ)
     ; =>
     (define kont-addr (gensym 'kont))
     (update-store kont-addr κ)
     
     ;update store version
     (define new-ver (+ (hash-ref store-map 'version) 1))
     (hash-set! store-map 'version new-ver)
     
     (list (astate cond new-ver `(if ,cons ,alt ,kont-addr)))]

    
    [(astate `(letrec ([,vars ,aexps] ...) ,body) σ κ)
     ; =>     
     ; evaluate the expressions
     (define values (map (eval-atom/curry) aexps))
     
     ; update the store with list of variables and values
     (for ([vr vars]
           [vl values])
       (update-store vr vl))
     
     ;update store version
     (define new-ver (+ (hash-ref store-map 'version) 1))
     (hash-set! store-map 'version new-ver)
     
     (list (astate body new-ver κ))]
    
    
    ; let-binding:
    [(astate `(let ([,v ,exp]) ,body) σ κ)
     ; =>
     ;Store continuation into store.
     (define kont-addr (gensym 'letk))
     (update-store kont-addr κ)
     
     ;update store version
     (define new-ver (+ (hash-ref store-map 'version) 1))
     (hash-set! store-map 'version new-ver)
     
     (list (astate exp new-ver `(letk ,v ,body ,kont-addr)))]
    
    
    ; function application:
    [(astate `(,f . ,es) σ κ)
     ; => 
     (define addr (append (list f) es))
     (update-store addr κ)
     
     
     ;update store version
     (define new-ver (+ (hash-ref store-map 'version) 1))
     (hash-set! store-map 'version new-ver)
     
     ; considering only 1 argument.
     (define e (car es))
     (list (astate f new-ver `(Ar ,e ,addr)))]))
    


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; analyze : exp -> answer
(define (analyze prog)
  
  ; the initial abstract astate:
  (define astate0 (ainject prog))
  
  ; the set of all astates ever seen:
  (define visited (set))
  
  ; the neighbor maps
  (define neighbors (make-hasheq))
  
  ; mark the neigbors of a astate:
  (define (mark-neighbors! astate succs)
    (hash-set! neighbors astate succs))
  
  ; marks a state as seen:
  (define (mark-seen! astate)
    (set! visited (set-add visited astate)))
  
  ; checks if a state is seen:
  (define (seen? astate)
    (set-member? visited astate))
  
  ; states to explore next:
  (define todo (list astate0))
  
  ; adds states to be explored:
  (define (push-todos astates)
    (set! todo (append astates todo)))
  
  ; grabs the next state to be explored:
  (define (pop-todo)
    (define next (car todo))
    (set! todo (cdr todo))
    next)
  
  (while (not (null? todo))
         (display (set-count visited))
         (display store-map)
         (display "

****************************************
")
         
    (define curr (pop-todo))
    (when (not (seen? curr))
      (mark-seen! curr)
      (define succs (astep curr))
      (display "
CURR : ")
         (display curr)
         (display "

SUCCS : ")
      (display succs)
      (display "

")
      (when (list? succs)
        (mark-neighbors! curr succs)
        (push-todos succs))))
  
  ; return all visited states:
  (make-graph-file neighbors visited))


; FILE I/O
; make-graph-file : neighbors visited -> graph.dot
; Prints the graph Depth-First
(define (make-graph-file neighbors visited)
  
  (define out (open-output-file "graph.dot" #:exists 'update))
  (display "digraph control_flow {
	node [shape = circle];" out)
(define label 0)
(define label-hash (make-hash))
(define visited-list (set->list visited))

(for ([v visited-list])
  (hash-set! label-hash v label)
  (set! label (+ label 1)))

;(display label-hash)
(display "
")
(for ([key (hash-keys label-hash)])
  (write (hash-ref label-hash key) out)
  (display " [tooltip = \"" out)
  (write key out)
  (display "\"]
" out))

(define keys (hash-keys neighbors))

(for ([k keys])
  (for ([v (hash-ref neighbors k)])
    (write (hash-ref label-hash k) out)
    (display " -> " out)
    (write (hash-ref label-hash v) out)
    (display ";
" out)))

(display "}" out)
(close-output-port out))



; example
(define fact-prog
  '(letrec ([f (λ (n)
                 (if (= n 0)
                     1
                     (let ([n-1! (f (- n 1))])
                       (* n n-1!))))])
     (f 5)))

(analyze fact-prog)
  
