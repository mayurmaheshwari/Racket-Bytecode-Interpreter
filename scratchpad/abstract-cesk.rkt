#lang racket


; Auxiliary functions:

; update : (a -> b) a b -> (a -> b)
(define (update f x y)
  (λ (x*)
    (if (equal? x x*)
        y
        (f x*))))

(define store-map (make-hash))

; weak updates to store hash-map
; values are stored as list
; values for same key are appended
; Duplicate updates for same key are filtered
(define (update-store x y)
   (if(hash-has-key? store-map x)
      (hash-set! store-map x 
                 (if (member y (hash-ref store-map x))
                     (hash-ref store-map x)
                     (if (list? y)
                         (append y (hash-ref store-map x))
                         (append (list y) (hash-ref store-map x)))))
      (hash-set! store-map x (list y)))
   (λ (x*)
     (hash-ref store-map x*)))
 

; update* : (a -> b) [a] [b] -> (a -> b)
(define (update* f xs ys)
  (match* (xs ys)
    [['() '()]    f]
    [[(cons x xs*) (cons y ys*)]
     (update* (update-store x y) xs* ys*)]))



; A-Normal Form:

; <lam> ::= (λ (<var> ...) <exp>)

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
                store          ; store
                continuation}  ; kont
  #:transparent) ; enable low-level access to struct fields


; σ : store = addr -> list of values

; value = integer + boolean + clo + kont

; clo ::= (clo <lam>)

; κ : kont ::= (letk <var> <exp> <kont>)
;           |  (Ar <exp> <kont-addr>)
;           |  (Fn <clo> <kont-addr>)
;           |  halt

; addr = a set of addresses;
;        variable symbols 'symbol to store values
;        applications (e0 e1) to store Kont



; apply-kont : kont value store -> (state + answer)
(define (apply-kont κ value σ)
  (match κ
    ; Apply the halt continuation:
    ['halt
     (display `(answer ,value ,σ))]
    
    ; Note: value is a list of closures.
    ; Output: List of states parameterized by 
    ; different closure values flowing into the functions.
    [`(Ar ,e ,a)
     (for*/list ([v value])
       (astate e σ `(Fn ,v ,a)))]
    
    ; Note: value is a list of args that could 
    ; flow into the param of function.
    [`(Fn ,f ,a)
     (apply-proc f value σ a)]
    
    ; Resume execution:
    [`(letk ,v ,e ,κ)
     
     (list (astate e (update-store v value) κ))]))


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


                   
; eval-atom : aexp env store -> value
(define (eval-atom atom σ)
  (match atom
    [(? symbol?)    (σ atom)] ;outputs a list of values.
    [(? boolean?)   atom]
    [(? integer?)   atom]
    
    [(cons (and prim (? prim?)) rest)
     ; =>
     (let ([args (map (eval-atom/curry σ) rest)])
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


; eval-atom/curry : env store -> aexp -> value
(define (eval-atom/curry σ)
  (λ (atom) 
    (eval-atom atom σ)))


; store0 is the initial (empty) store
(define store0 (λ (addr) (error (format "unbound address: ~a" addr))))

; ainject : exp -> astate
(define (ainject exp)
  (astate exp store0 'halt))

; apply-proc : value [value] store kont -> (astate + answer)
(define (apply-proc proc args σ a)
    
    (match proc
      ; apply a closure:
      [`(clo (λ ,vars ,body))
       ; =>
       ; weak-update the store: currently supporting only 1 formal param.
       ; TBD Remove carring for multi-argument support.
       (define σ* (update-store (car vars) args))
     
       (for*/list ([κ (σ* a)])
         (astate body σ* κ))]))
  
; step : astate -> (astate + answer)
(define (astep ς)
  (match ς
    
    ; return:
    [(astate (and atom (? atom?)) σ κ)
     ; =>
     ; evaluate the return value:
     ; Note: It is a list of value/s
     (define return-value (eval-atom atom σ))
       
     (apply-kont κ return-value σ)]
        
    ; conditional evaluation:
    [(astate `(if ,cond ,cons ,alt) σ κ)
     ; =>
     ;(if (eval-atom cond σ)
         (list (astate cons σ κ)
         (astate alt σ κ))]

    
    [(astate `(letrec ([,vars ,aexps] ...) ,body) σ κ)
     ; =>
     ; allocate fresh addresses:
     (define addrs (map gensym vars))
     
     ; evaluate the expressions with the *new* env:
     (define values (map (eval-atom/curry σ) aexps))
     
     ; update the store:
     (define σ* (update* σ vars values))
     
     (list (astate body σ* κ))]
    
    
    ; let-binding:
    [(astate `(let ([,v ,exp]) ,body) σ κ)
     ; =>
     (list (astate exp σ `(letk ,v ,body ,κ)))]
    
    ; function application:
    [(astate `(,f . ,es) σ κ)
     ; =>
     
     (define addr (append (list f) es))
     (define σ* (update-store addr κ))
     ; considering only 1 argument.
     (define e (car es))
     (list (astate f σ* `(Ar ,e ,addr)))]))
    


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; run : exp -> answer
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
****************************************

")
      (when (list? succs)
        (mark-neighbors! curr succs)
        (push-todos succs))))
  
  ; return all visited states:
  (make-graph-file neighbors visited))

(define (make-graph-file neighbors visited)
  ; FILE I/O
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
" out)
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
  
