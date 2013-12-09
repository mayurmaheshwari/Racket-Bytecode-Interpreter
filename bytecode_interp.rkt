#lang racket

(require "stack.rkt")

; Auxiliary functions:

; update : (a -> b) a b -> (a -> b)
(define (update f x y)
  (λ (x*)
    (if (equal? x x*)
        y
        (f x*))))

; Assertion:
; if x != x'
; then (f x) == ((update f x' y) x)

; Assertion:
; ((update f x y) x) == y

; update* : (a -> b) [a] [b] -> (a -> b)
(define (update* f xs ys)
  (match* (xs ys)
    [['() '()]    f]
    [[(cons x xs*) (cons y ys*)]
     (update* (update f x y) xs* ys*)]))



; atom? : exp -> boolean?
(define (atom? exp)
  (match exp
    ;[`(λ ,_ ,_)   #t]
    [(? symbol?)    #t]
    [(? boolean?)   #t]
    [(? integer?)   #t]
    [(? box?)       #t]
    [(cons (? prim?) _)  #t]
    [else           #f]))


; prim? : symbol? -> boolean?
(define (prim? exp)
  (case exp
    [(+ - * = void) #t]
    [else      #f]))

(define (undefined)
  (define x x)
  x)

; CSHK machine state:
(struct state {control        ; exp
               stack          ; stk
               heap           ; heap
               continuation}) ; kont



; apply-kont : kont value stack store -> (state + answer)
; TBD remove ρ* from the signature.
; It is here to provide the state of final env.
(define (apply-kont κ value ρ* σ)
  (match κ
    ; Apply the halt continuation:
    ['halt
     `(answer ,value ,ρ* ,σ)]
    
    ; Resume execution:
    [`(letk ,n ,e ,ρ ,κ)
     
     ;(define a* (gensym 'a)) ; fresh address
     ;(display n)
     (state e (Modify-stack ρ n value) σ κ)]
    
    [`(letk-box ,n ,e ,ρ ,κ)
     ;installs a value into a boxed cell.
     ;that is why the boxed address is already present in the stack.
     (define addr (unbox (list-ref ρ n)))
     (state e ρ (update σ addr value) κ)]
))

; prim->proc : symbol? -> procedure?
(define (prim->proc prim)
  (match prim
    ['+    +]
    ['-    -]
    ['*    *]
    ['=    =]
    ['void void]))

                   
; eval-atom : aexp stk heap -> value
(define (eval-atom atom ρ σ)
  (match atom
    [(? symbol?)    atom]
    [(? boolean?)   atom]
    [(? integer?)   atom]
    [(? box?) (σ (unbox atom))]
    
    [(cons (and prim (? prim?)) rest)
     ; =>
     (let ([args (map (eval-atom/curry ρ σ) rest)])
       (apply (prim->proc prim) args))]
    
    [`(lam (,fv-location ...) ,body)
     ;`(clo (lam fv body) )
     (define clos-addrs (map (λ(x)(Retrieve-stack ρ x)) fv-location))
     ;(define clos-addrs (map unbox clos-list))
     ;(write clos-list)
     `(clos (lam ,clos-addrs ,body) ,ρ)]
    
    [`(loc ,n)
     ; =>
     (Retrieve-stack ρ n)]
    
    [`(loc-box ,n)
     ; =>
     (σ(Retrieve-stack ρ n))]
    [else           (error "unknown atom")]))


; eval-atom/curry : env store -> aexp -> value
(define (eval-atom/curry ρ σ)
  (λ (atom) 
    (eval-atom atom ρ σ)))


; stk0 is the initial (empty) stack implemented as a list.
(define stk0 empty)

; heap0 is the initial (empty) heap
(define heap0 (λ (addr) (error (format "unbound address: ~a" addr))))

; inject : exp -> state
(define (inject exp)
  (state exp stk0 heap0 'halt))

(define (apply-proc proc ρ σ κ)
  (match proc
    
    ; apply a closure:
    [`(clos (lam ,clos-addrs ,body) ,ρ**)
     ; =>
     ; allocate fresh addresses:
     ;(define addrs (map gensym vars)) 
     
     ; update the environment:
     (define ρ* (append clos-addrs ρ))
     
     ; update the store:
     ;(define σ* (update* σ addrs args))
     
     (state body ρ* σ κ)]))


; step : state -> (state + answer)
(define (step ς)
  (match ς
    
    ; Return
    [(state (and atom (? atom?)) ρ σ κ)
     ; =>
     ; evaluate the return value:
     (define return-value (eval-atom atom ρ σ))
     ; TBD remove the stk from the call to apply-kont  
     (apply-kont κ return-value ρ σ)]  
    
    ; conditional evaluation:
    [(state `(if ,cond ,cons ,alt) ρ σ κ)
     ; =>
     (if (eval-atom cond ρ σ)
         (state cons ρ σ κ)
         (state alt ρ σ κ))]
    
    ; (LAM (T ...) (n ...) e)
    ;[(state `(lam (,n) ,body) ρ σ κ)
     ; =>
     ; TBD function to retrieve a value at loc n.
     ; (retrieve stack n)
     
     ; TBD function to push the retrieved value onto the stack.
     ; (push-on-stack stack value)
     ;(state body ρ σ κ)]
    
    
    ; (LOC n) fetch the value from location n on stack.
    ; It applies continuation
    [(state `(loc ,n) ρ σ κ)
     (define value (Retrieve-stack ρ n))
     (state value ρ σ κ)]
  
    ; (LOC-BOX n)
    [(state `(loc-box ,n) ρ σ κ)
     (define box-pointer (Retrieve-stack ρ n))
     ;(define value (σ box-pointer))
     (state box-pointer ρ σ κ)]
   
    ; New Let
     ; (LET-VOID n e)
    [(state `(let-void ,n1 (install-value ,n2 ,exp ,e)) ρ σ κ)
     (define ρ* (Push-void ρ n1))
     (state exp ρ* σ `(letk ,n2 ,e ,ρ* ,κ))]
   
    ; New Let-Box
    ; (LET-VOID-BOX n e)
    [(state `(let-void-box ,n1 (install-value-box ,n2 ,exp ,e)) ρ σ κ)
     ; generate n fresh addresses
     (define addrs (map gensym (make-list n1 'a)))
     ; generate n fresh values
     (define values (make-list n1 (undefined)))
     ; convert addrs to box type
     (define box-ptr-list (map box addrs))
     ; update the stack
     (define ρ* (append  box-ptr-list ρ))
     ;update the heap
     (define σ* (update* σ addrs values))
     (state exp ρ* σ* `(letk-box ,n2 ,e ,ρ* ,κ))]
    
    
    #| Old Let
    ; (LET-VOID n e)
    [(state `(let-void ,n ,exp) ρ σ κ)
     (define ρ* (Push-void ρ n))
     (state exp ρ* σ κ)]
   |#
    ; (INSTALL-VALUE n e e)
    [(state `(install-value ,n ,exp ,e) ρ σ κ)
     (state exp ρ σ `(letk ,n ,e ,ρ ,κ))]

    ; (INSTALL-VALUE-BOX n e e)
    [(state `(install-value-box ,n ,exp ,e) ρ σ κ)
     (state exp ρ σ `(letk-box ,n ,e ,ρ ,κ))]
    
    
    ; (LET-REC (l...) e)
    [(state `(let-void ,n (let-rec (,lm ...) ,body)) ρ σ κ)
     
     ; update stack
     (define addrs (map gensym (make-list n 'a)))
     (define box-addrs (map box addrs))
     (define ρ* (append box-addrs ρ))
     ; parse lams & close
     (define values (map (eval-atom/curry ρ* σ) lm))
     (define σ* (update* σ addrs values))
     (write values)
     (state body ρ* σ* κ)]
    
    
    
    ; function application
    ; only one argument is passed.
    ; e1 & e2 are aexps
    [(state `(application ,e1 ,e2) ρ σ κ)
     ;push n slots into the stack.
     ; n is the length of e2. It is 1 for now.
     (define ρ* (Push-void ρ 1))
     ; evaluate e2 and modify stack at 0;
     (define arg (eval-atom e2 ρ* σ))
     (define ρ**(Modify-stack ρ* 0 arg))
     ; evaluate proc
     (define proc (σ(unbox(eval-atom e1 ρ** σ))))
     ; applyproc
    (apply-proc proc ρ** σ κ)
     ;(state 1 ρ** σ κ)
     
     ]
    ))

    ; (BOXENV n e)
    

    


; step* : state -> answer
(define (step* ς)
  (if (state? ς)
      (step* (step ς))
      ς))

; run : exp -> answer
(define (run exp)
  (define ς0 (inject exp))
  (step* ς0))


;example
(define prog1
  '(let-void-box 2
                 (loc 1)))


; example
#|(define prog
  '(let-void-box 2
             (install-value-box 0 5
             ;(install-value-box 1 6
                            (loc-box 0))));)
|#

(define prog3
  '(let-void 1
             (let-void-box 1
                           (install-value-box 0 (install-value 1 5 (loc 1)) 
                            (loc-box 0)))))


(define prog2
  '(let-void 1
             (install-value 0 
                            (let-void 1
                                      (install-value 0 5 (loc 0))) 
                            (loc 0))))


; doesn't work
(define prog
  '(let-void 1 
             (install-value 0 10 #|'sym|# (loc 0))))


(define prog4
  '(let-void-box 3 
                 (install-value-box 0
                                    5
                                    (install-value-box 1
                                                       10
                                                       (install-value-box 2
                                                                          15
                                                                          (loc-box 2))))))

(define prog5
  '(let-void 1
             (let-rec ((lam ()
                           5)) 
              (application((loc 1) 10)))))

(define progdebug
  '(let-void 2
             (let-rec ((lam (1) 
                            (application (loc 1) (loc 2) )) 
                       (lam () 
                            (loc 0))) 
                      (application (loc 1) 2))))

(define fact
  '(let-void 1 (let-rec ((lam (0)
                              (if (= (loc 1) 0)
                                  1
                                  (let-void 1 (install-value 0
                                                             (application (loc 2) (- (loc 3) 1))
                                                             (* (loc 2) (loc 0))))))) 
                        (application (loc 1) 6))))

(run fact)
  