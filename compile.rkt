#lang racket

;; CIS531 Fall '25 Project 5
;; Compiling Functions (R4/5) -> x86-64
(require "irs.rkt") ;; Definition of each IR (please read)
(require "system.rkt") ;; System-specific details

(provide (all-defined-out)) ;; export everything for testing

;; The compiler is designed in passes, which go:
;;
;; --> R4/R5? -- Source program (R5 is extra credit)                                         <INPUT>
;; |
;; +-> shrunk-R5? -- Core R4/5 (removes syntactic sugar / extra forms)                       [shrink]
;; |
;; +-> unique-source-tree? -- Every bound identifier is written exactly once                 [uniqueify]
;; |
;; +-> revealed-functions-program? -- Makes all calls explicit via fun-ref and app           [reveal-functions]
;; |
;; +-> assignment-converted-program? -- Eliminates set!; variables become 1-slot vectors     [assignment-convert]
;; |
;; +-> closure-converted-program? -- Lift lambdas to top-level defines, allocate closures    [lift-lambdas]
;; |
;; +-> limited-arity-program? -- Rewrites >6-arg functions to pass the rest in a vector      [limit-functions]
;; |
;; +-> anf-program? -- A-Normal form (flattening nested expressions)                         [anf-convert]
;; |
;; +-> blocks-program? -- (Formerly C2) blocks of sequences of commands, if, gotos, calls    [explicate-control]
;; |
;; +-> locals-program? -- Uncovering local variables for each function                       [uncover-locals]
;; |
;; +-> instr-program? -- Pseudo-x86, flattened blocks of instructions over pseudo-vars       [select-instructions]
;; |
;; +-> homes-assigned-program? -- Assigns variables to stack locations (rbp-relative homes)  [assign-homes]
;; |
;; +-> patched-program? -- Patches illegal x86 forms (e.g., mem-mem moves, bad leaq forms)   [patch-instructions]
;; |
;; +-> x86-64? -- Final x86-64 IR with prologue/epilogue and printing logic                  [prelude-and-conclusion]
;; |
;; +-> string? -- Rendered as GAS assembly text suitable for writing to a .s file            [dump-x86-64]


;; Assume that p is of the form `(program (define (f x0 ...) e-b)
;; ... e-main). Lift `e-b` into a special function named
;; `(entry-symbol)`. Also ensure that new forms are handled.
(define (shrink p)
  (define (h e)
    (match e
      ;; other cases...
      [`(void) e]
      [(? symbol?) e]
      [(? number?) e]
      [#t #t]
      [#f #f]
      [`(read) '(read)]
      [`(not ,e0) `(not ,(h e0))]
      [`(+ ,e0 ,e1) `(+ ,(h e0) ,(h e1))]
      [`(- ,e0 ,e1) `(+ ,(h e0) (- ,(h e1)))]
      [`(- ,e) `(- ,(h e))]
      [`(and ,e0 ,e1) `(if ,(h e0) ,(h e1) #f)]
      [`(or ,e0 ,e1) `(if ,(h e0) #t ,(h e1))]
      [`(<= ,e0 ,e1) `(if (< ,(h e0) ,(h e1)) #t (eq? ,(h e0) ,(h e1)))]
      [`(> ,e0 ,e1) `(if (< ,(h e0) ,(h e1)) #f (not (eq? ,(h e0) ,(h e1))))]
      [`(>= ,e0 ,e1) `(if (< ,(h e0) ,(h e1)) #f #t)]
      [`(eq? ,e0 ,e1) `(eq? ,(h e0) ,(h e1))]
      [`(< ,e0 ,e1) `(< ,(h e0) ,(h e1))]
      [`(if ,e0 ,e1 ,e2) `(if ,(h e0) ,(h e1) ,(h e2))]
      [`(begin ,e0) (h e0)]
      [`(begin ,e0 ,e-rest ...) `(let ([_ ,(h e0)]) ,(h `(begin ,@e-rest)))]
      [`(set! ,x ,e) `(set! ,x ,(h e))]
      [`(let ([_ (while ,e-g ,e-b)]) ,e-r)
       `(let ([_ (while ,(h e-g) ,(h e-b))]) ,(h e-r))]
      [`(make-vector ,i) e]  
      [`(vector-ref ,e ,i) `(vector-ref ,(h e) ,i)]
      [`(vector-set! ,e ,i ,e-v) `(vector-set! ,(h e) ,i ,(h e-v))]
      [`(while ,e-g ,e-b) `(let ([_ (while ,(h e-g) ,(h e-b))]) (void))]
      [`(let ([,x ,e]) ,e-b) `(let ([,x ,(h e)]) ,(h e-b))]
      [`(let* ([,x ,e0]) ,e-b)
       `(let ([,x ,(h e0)]) ,(h e-b))] 
      [`(let* ([,x ,e0] ,rest ...) ,e-b)
       `(let ([,x ,(h e0)]) ,(h `(let* (,@rest) ,e-b)))]
      ;; new
      [`(lambda (,xs ...) ,e-b)
       `(lambda ,xs ,(h e-b))]
      [`(,e-f ,e-args ...)
       `(,(h e-f) ,@(map h e-args))]))
  (define (per-defn defn)
    (match defn
      [`(define (,f ,xs ...) ,e-b)
       `(define (,f ,@xs) ,(h e-b))]))
  (match p
    [`(program ,defns ... ,expr)
     `(program ,@(cons `(define (main) ,(h expr)) (map per-defn defns)))]))

;; Needs to be updated to map across definitions (I've done a bit of
;; this for you) and then to handle the new forms
(define (uniqueify p)
  (define (rename e assignment)
    (match e
      ;; 
      ;; old forms...
      ;;
      [(? fixnum? n) n]
      [(? boolean? b) b]
      ['(read) '(read)]
      [`(- ,x) `(- ,(rename x assignment))]
      [`(+ ,e1 ,e2) `(+ ,(rename e1 assignment) ,(rename e2 assignment))]
      [(? symbol? s) (hash-ref assignment s s)]
      [`(if ,e0 ,e1 ,e2) `(if ,(rename e0 assignment) ,(rename e1 assignment) ,(rename e2 assignment))]
      [`(,(? cmp? c) ,e0 ,e1) `(,c ,(rename e0 assignment) ,(rename e1 assignment))]
      [`(not ,e) `(not ,(rename e assignment))]
      [`(void) e]
      [`(let ([_ (while ,e-g ,e-b)]) ,e-r)
       `(let ([_ (while ,(rename e-g assignment) ,(rename e-b assignment))]) ,(rename e-r assignment))]
      [`(let ([,x ,e]) ,e-b)
       (if (hash-has-key? assignment x)
           (let* ([x+ (gensym x)]
                  [assignment+ (hash-set assignment x x+)])
             `(let ([,x+ ,(rename e assignment)]) ,(rename e-b assignment+)))
           (let ([assignment+ (hash-set assignment x x)])
             `(let ([,x ,(rename e assignment+)]) ,(rename e-b assignment+))))]
      [`(make-vector ,i) e]
      [`(vector-ref ,e ,i) `(vector-ref ,(rename e assignment) ,i)]
      [`(vector-set! ,e ,i ,e-v) `(vector-set! ,(rename e assignment) ,i ,(rename e-v assignment))]
      [`(set! ,x ,e) `(set! ,x ,(rename e assignment))]
      ;; NEW case: for any x ∈ xs, rename any one previously used...
      [`(lambda (,xs ...) ,e-b)
       'todo-transform-lambda]
      [`(,e-f ,e-args ...) `(,(rename e-f assignment) ,@(map (λ (arg) (rename arg assignment)) e-args))]))
  (define (per-defn def)
    (match def
      [`(define (,f ,xs ...) ,e-b)
       (let* ([fresh-xs (map gensym xs)]
              [assignment (for/hash ([x xs] [fx fresh-xs])
                          (values x fx))])
       `(define (,f ,@fresh-xs)
          ,(rename e-b assignment)))]))
  (match p
    [`(program ,defns ...)
     ;; empty info
     `(program ,@(map per-defn defns))]))


;; NEW: pass -- reveal-functions
;;
;; Analyze the syntax of p, and collect up a set of available
;; top-level functions. Then, we walk over each body expression, and
;; mark those usages as fnames. Also, ensure that application of
;; user-defined functions is made explicit via `app`.
;;
;; (define (f x) (+ x (g 1))) (define (g y) y) (f 23)
;; => (define (f x) (+ x (app (fun-ref g) 1)))
;;    (define (g y) y)
;;    (app (fun-ref f) 23)

(define (reveal-functions p)
  (match p
    [`(program (define (,names ,params ...) ,bodies) ...)
     ;; Collect all function names into a set
     (define name-set (list->set names))
     
     ;; Walk over expressions and rewrite function references
     (define (walk e)
       (match e
         [(? fixnum? n) n]
         [(? boolean? b) b]
         ['(read) e]
         ['(void) e]
         [`(- ,x) `(- ,(walk x))]
         [`(+ ,e1 ,e2) `(+ ,(walk e1) ,(walk e2))]
         
         ;; Key case: plain symbol that's a function name
         [(? symbol? s) 
          (if (set-member? name-set s)
              `(fun-ref ,s)
              s)]
         
         [`(if ,e1 ,e2 ,e3)
          `(if ,(walk e1) ,(walk e2) ,(walk e3))]
         
         [`(,(? cmp? c) ,e0 ,e1)
          `(,c ,(walk e0) ,(walk e1))]
         
         [`(not ,e) `(not ,(walk e))]
         
         [`(let ([_ (while ,e-g ,e-b)]) ,e-r)
          `(let ([_ (while ,(walk e-g) ,(walk e-b))])
             ,(walk e-r))]
         
         [`(let ([,x ,e]) ,e-b)
          `(let ([,x ,(walk e)])
             ,(walk e-b))]
         
         [`(make-vector ,i) `(make-vector ,(walk i))]
         
         [`(vector-ref ,e ,i)
          `(vector-ref ,(walk e) ,(walk i))]
         
         [`(vector-set! ,e ,i ,e-v)
          `(vector-set! ,(walk e) ,(walk i) ,(walk e-v))]
         
         [`(set! ,x ,e)
          `(set! ,x ,(walk e))]
         
         ;; Lambda - rewrite body but not parameters
         [`(lambda (,xs ...) ,e-b)
          `(lambda (,xs ...) ,(walk e-b))]
         
         ;; Application - rewrite to use `app`
         [`(,e-f ,e-args ...)
          `(app ,(walk e-f) ,@(map walk e-args))]))
     
     ;; Apply walk to each function body
     `(program ,@(map (λ (name params body)
                        `(define (,name ,@params) ,(walk body)))
                      names params bodies))]))


;; NEW: pass -- lift-lambdas
;;
;; Perform closure conversion on the program. Lift every lambda to a
;; top-level function. Basic approach: walk over each definition in
;; the program, accumulate a list of expressions associated with
;; each. A function, `walk-body`, will demand the lifting of body
;; expressions, which happens recursively.
;;
;; I recommend doing bottom-up closure conversion, which involves
;; writing a recursive function which traverses expressions. The
;; function returns `(,converted-expr ,lifted-defns), i.e., a
;; two-element list consisting of the lifted expression and also a set
;; of definitions which resulted from the lifting of lambdas.
(define (lift-lambdas p)
  (define emitted-defines (set))
  (define (emit-define! defn) (set! emitted-defines (set-add emitted-defines defn)))
  
  ;; calculate the free variables of an expression e...
  (define (free-vars e)
    (match e
      [(? fixnum? n) (set)]
      [(? boolean? b) (set)]
      [`(void) (set)]
      [`(read) (set)]
      [`(fun-ref ,f) (set)]
      [`(- ,e+) (free-vars e+)]
      [`(+ ,e0 ,e1) (set-union (free-vars e0) (free-vars e1))]
      [(? symbol? x) (set x)]
      [`(if ,e0 ,e1 ,e2) (set-union (free-vars e0) (free-vars e1) (free-vars e2))]
      [`(,(? cmp? c) ,e0 ,e1) (set-union (free-vars e0) (free-vars e1))]
      [`(and ,e0 ,e1) (set-union (free-vars e0) (free-vars e1))]
      [`(or ,e0 ,e1)  (set-union (free-vars e0) (free-vars e1))]
      [`(not ,e) (free-vars e)]
      [`(let ([_ (while ,e-g ,e-b)]) ,e-r)
       (set-union (free-vars e-g) (free-vars e-b) (free-vars e-r))]
      [`(let ([,x ,e]) ,e-b)
       (set-union (free-vars e) (set-remove (free-vars e-b) x))]
      [`(make-vector ,i) (free-vars i)]
      [`(vector-ref ,e ,i) (set-union (free-vars e) (free-vars i))]
      [`(vector-set! ,e ,i ,e-v) (set-union (free-vars e) (free-vars i) (free-vars e-v))]
      [`(set! ,x ,e) (set-union (set x) (free-vars e))]
      [`(lambda (,xs ...) ,e) (foldl (lambda (x acc) (set-remove acc x)) (free-vars e) xs)]
      [`(app ,e-f ,e-args ...) (foldl (lambda (s acc) (set-union s acc)) (free-vars e-f) (map free-vars e-args))]))
  
  ;; do lambda lifting on e, return the lifted expression
  (define (walk-expr e)
    (match e
      [(? fixnum? n) n]
      [(? boolean? b) b]
      [`(void) e]
      [`(read) e]
      [`(- ,e+) `(- ,(walk-expr e+))]
      [`(+ ,e0 ,e1) `(+ ,(walk-expr e0) ,(walk-expr e1))]
      [(? symbol? x) x]
      [`(if ,e0 ,e1 ,e2) 
       `(if ,(walk-expr e0) ,(walk-expr e1) ,(walk-expr e2))]
      [`(,(? cmp? c) ,e0 ,e1) 
       `(,c ,(walk-expr e0) ,(walk-expr e1))]
      [`(and ,e0 ,e1) `(and ,(walk-expr e0) ,(walk-expr e1))]
      [`(or ,e0 ,e1) `(or ,(walk-expr e0) ,(walk-expr e1))]
      [`(not ,e) `(not ,(walk-expr e))]
      [`(let ([_ (while ,e-g ,e-b)]) ,e-r)
       `(let ([_ (while ,(walk-expr e-g) ,(walk-expr e-b))])
          ,(walk-expr e-r))]
      [`(let ([,x ,e]) ,e-b)
       `(let ([,x ,(walk-expr e)])
          ,(walk-expr e-b))]
      [`(make-vector ,i) `(make-vector ,(walk-expr i))]
      [`(vector-ref ,e ,i) 
       `(vector-ref ,(walk-expr e) ,(walk-expr i))]
      [`(vector-set! ,e ,i ,e-v) 
       `(vector-set! ,(walk-expr e) ,(walk-expr i) ,(walk-expr e-v))]
      [`(set! ,x ,e) `(set! ,x ,(walk-expr e))]
      
      ;; Wrap function references in a closure (vector with fun-ref at index 0)
      [`(fun-ref ,f) e]
      
      ;; Lambda lifting: the main event!
      [`(lambda (,xs ...) ,e)
       ;; First, convert the body recursively
       (define converted-body (walk-expr e))
       
       ;; Calculate free variables
       (define fvs (set->list (free-vars e)))
       
       ;; Generate a fresh name for the lifted function
       (define lifted-name (gensym 'lambda))
       
       ;; Helper: generate a let-stack to unwrap free vars from env
       (define (letstack vars-in-order i body)
         (match vars-in-order
           [`() body]
           [`(,hd . ,tl)
            `(let ([,hd (vector-ref env ,i)])
               ,(letstack tl (+ i 1) body))]))
       
       ;; Create the lifted function definition with env parameter
       (define lifted-body (letstack fvs 1 converted-body))
       (define lifted-defn 
         `(define (,lifted-name env ,@xs) ,lifted-body))
       
       ;; Emit the lifted definition
       (emit-define! lifted-defn)
       
       ;; Create closure: vector with fun-ref at 0, free vars at 1..n
       (define closure-vec (gensym 'closure))
       (define (build-closure-sets i fvs-left)
         (match fvs-left
           [`() closure-vec]
           [`(,hd . ,tl)
            `(let ([_ (vector-set! ,closure-vec ,i ,(walk-expr hd))])
               ,(build-closure-sets (+ i 1) tl))]))
       
       `(let ([,closure-vec (make-vector ,(+ 1 (length fvs)))])
          (vector-set! ,closure-vec 0 (fun-ref ,lifted-name))
          ,(build-closure-sets 1 fvs))]
      
      ;; Application: extract function pointer and pass closure as first arg
      [`(app ,e-f ,e-args ...) 
       `(app ,(walk-expr e-f) ,@(map walk-expr e-args))]))
  
  (define (per-defn definition)
  (match definition
    [`(define (,fname ,formals ...) ,e-body)
     ;; Don't add env parameter when not doing closure conversion
     `(define (,fname ,@formals) ,(walk-expr e-body))]))
  
  (match p
    [`(program ,definitions ...)
     `(program ,@(map per-defn definitions) ,@(set->list emitted-defines))]))

;; NEW: pass -- limit-functions
;;
;; This pass rewrites functions of >6 arguments to pass the rest via a
;; vector, rather than the stack (as in x86-64 typically).
;;
;; At this point, we only have toplevel defines--all closures have
;; been eliminted (turned into vector operations) via closure
;; conversion / lambda lifting. Now, we face a bit of a tricky issue:
;; in x86-64, we can pass the first six arguments in registers, but
;; the rest have to go on the stack. Passing things on the stack can
;; complicate some other implementation details (e.g., efficient tail
;; calls via indirect jump), and so this pass indirects the rest
;; through a vector.
(define (limit-functions p)
  ;; I wrote a walk-expr function here which walks over all exprs and
  ;; identifies callsites with > 6 arguments to allocate / populate
  ;; vectors.
  (define (walk-expr e)
    (match e

    [(? fixnum? n) n]
    [(? boolean? b) b]
    ['(read) '(read)]
    [(? symbol? s) s]

   
    [`(- ,e1)
     `(- ,(walk-expr e1))]

    [`(+ ,e1 ,e2)
     `(+ ,(walk-expr e1) ,(walk-expr e2))]

    [`(not ,e1)
     `(not ,(walk-expr e1))]

    
    [`(,(? cmp? c) ,e0 ,e1)
     `(,c ,(walk-expr e0) ,(walk-expr e1))]

    
    [`(if ,e1 ,e2 ,e3)
     `(if ,(walk-expr e1)
          ,(walk-expr e2)
          ,(walk-expr e3))]

    
    [`(let ([_ (while ,e-g ,e-b)]) ,e-r)
     `(let ([_ (while ,(walk-expr e-g)
                      ,(walk-expr e-b))])
        ,(walk-expr e-r))]

    
    [`(let ([,x ,rhs]) ,body)
     `(let ([,x ,(walk-expr rhs)])
        ,(walk-expr body))]

    
    [`(set! ,x ,e1)
     `(set! ,x ,(walk-expr e1))]

    
    [`(make-vector ,i)
     `(make-vector ,i)]

    [`(vector-ref ,e1 ,i)
     `(vector-ref ,(walk-expr e1) ,i)]

    [`(vector-set! ,e1 ,i ,e2)
     `(vector-set! ,(walk-expr e1) ,i ,(walk-expr e2))]

    
    [`(,f ,args ...)
     ;; first recursively rewrite the function & all arguments
     (define f* (walk-expr f))
     (define args* (map walk-expr args))

     (if (<= (length args*) 6)
         `(,f* ,@args*)

         ;; >6 args → vector rewrite
         (let* ([prefix (take args* 6)]
                [extra  (drop args* 6)]
                [v (gensym 'v)]
                [n (length extra)])
           
           (define sets
             (for/list ([arg extra] [i (in-naturals 0)])
               `(vector-set! ,v ,i ,arg)))

           `(let ([,v (make-vector ,n)])
              ,@sets
              (,f* ,@prefix ,v))))]
))
  (define (per-defn definition)
    (match definition
      ;; > 6 formals: (f a0 a1 a2 a3 a4 a5 a-rest...)
      [`(define (,fname ,a0 ,a1 ,a2 ,a3 ,a4 ,a5 ,a-rest ...) ,e-body)
       (define prefix '(,a0 ,a1 ,a2 ,a3 ,a4 ,a5))
       (define extras a-rest)  ;; the extra formals
       (define v (gensym 'v))

       
       (define bindings
         (for/list ([x extras] [i (in-naturals 0)])
           `[,x (vector-ref ,v ,i)]))

       `(define (,fname ,@prefix ,v)
          (let* (,@bindings)
            ,(walk-expr e-body)))]  ;; start indexing at 0 (matches call-site)
      ;; ≤ 6 formals: unchanged except recursive walk
      [`(define (,fname ,formals ...) ,e-body)
       `(define (,fname ,@formals)
          ,(walk-expr e-body))]))
  (match p
    [`(program ,definitions ...)
     `(program ,@(map per-defn definitions))]))

;; New: map over all the definitions
;; Optimized assignment-convert, per-function:
;; - For each function, compute which vars are ever mutated with set!
;; - Only those vars are boxed in that function.
(define (assignment-convert p)
  ;; box-formals: helper function (use for defines and lambdas)
  ;; transform (lambda (x y z) ...) => (lambda (x123 y235 z523) (let ([x (vector x12)]) ...)
  ;; genformals and realformals are lists of symbols
  ;; e-body is an expression which will be used when no vars left
  (define (box-formals genformals realformals e-body)
    (match genformals
      ['() e-body]
      [`(,x . ,rst)
       `(let ([,(first realformals) (make-vector 1)])
          (let ([_ (vector-set! ,(first realformals) 0 ,x)])
            ,(box-formals rst (rest realformals) e-body)))]))
  (define (a-c e)
    (match e
      ;;
      ;; ... old forms ...
      ;;
      [(? boolean? b) e]
      [(? fixnum? n)  e]
      [`(read)        e]
      ['(void)        e]
      [`(- ,a) `(- ,(a-c a))]
      [`(+ ,a ,b) `(+ ,(a-c a) ,(a-c b))]
      [`(not ,a) `(not ,(a-c a))]
      [`(,(? cmp? c) ,a ,b) `(,c ,(a-c a) ,(a-c b))]
      [`(if ,g ,t ,f) `(if ,(a-c g) ,(a-c t) ,(a-c f))]
      
      [(? symbol? x) `(vector-ref ,x 0)] 
      [`(let ([_ (while ,e-g ,e-b)]) ,e-r)
       `(let ([_ (while ,(a-c e-g) ,(a-c e-b))]) ,(a-c e-r))]
      [`(let ([_ ,e]) ,e-b)
       `(let ([_ ,(a-c e)]) ,(a-c e-b))]
      [`(set! ,x ,e+)
       `(vector-set! ,x 0 ,(a-c e+))]
      [`(vector-ref ,e ,i)
       `(vector-ref ,(a-c e) ,i)]
      [`(vector-set! ,e ,i ,e-v)
       `(vector-set! ,(a-c e) ,i ,(a-c e-v))]
      [`(make-vector ,i) e]
      ;; new forms
      [`(fun-ref ,g) e]
      [`(app ,es ...) `(app ,@(map a-c es))]
      [`(lambda (,xs ...) ,e)
       'todo]
      ;; put original let last to avoid matching _
      [`(let ([,x ,e]) ,e-b)
       `(let ([,x (make-vector 1)]) (let ([_ (vector-set! ,x 0 ,(a-c e))]) ,(a-c e-b)))]))
  (define (per-defn definition)
    (match definition
      [`(define (,fname ,formals ...) ,e-body)
       ;; Generate fresh names and box all formals
       (define genformals (map (λ (_) (gensym)) formals))
       `(define (,fname ,@genformals) 
          ,(box-formals genformals formals (a-c e-body)))]))
  (match p
    [`(program ,defns ...)
     `(program ,@(map per-defn defns))]))

;; ANF Conversion--handle new cases, think carefully about if
(define (anf-convert p)
  (define (handle-rest e-rest as a0 k)
  (match e-rest
    ['()
     (let ([as (reverse as)]
           [x (gensym 'app)])
       `(let ([,x (app ,a0 ,@as)])
          ,(k x)))]

    [`(,hd . ,rest)
     (convert-expr
      hd
      (lambda (a)
        (handle-rest rest (cons a as) a0 k)))]))
  (define (convert-expr e k)
    (match e
      ;; 
      ;; ... old forms ...
      ;;
      [(? fixnum? n) (k n)]
      [(? boolean? b) (k b)]
      ['(read)
       (let ([x (gensym 'read)])
         `(let ([,x (read)]) ,(k x)))]
      [(? symbol? x) (k x)]
      ['(void) (k e)]
      [`(- ,e)
      (convert-expr e
                      (lambda (atom)
                               (let ([x (gensym)])
                                 `(let ([,x (- ,atom)]) ,(k x)))))]
      [`(not ,e) (convert-expr e (lambda (atom) (let ([x (gensym)]) `(let ([,x (not ,atom)]) ,(k x)))))]
      [`(,(? cmp? c) ,e0 ,e1)
       (convert-expr e0
                     (λ (a0)
                       (convert-expr e1
                                     (λ (a1)
                                       (let ([x (gensym)])
                                         `(let ([,x (,c ,a0 ,a1)]) ,(k x)))))))]
      [`(+ ,e0 ,e1)
       (convert-expr e0
                     (λ (a0)
                       (convert-expr e1
                                     (λ (a1)
                                       (let ([x (gensym '+)])
                                         `(let ([,x (+ ,a0 ,a1)]) ,(k x)))))))]
      [`(if ,e0 ,e1 ,e2)
       (convert-expr
        e0
        (λ (a-g)
          `(if ,a-g ,(convert-expr e1 k) ,(convert-expr e2 k))))]
      
      [`(let ([_ (vector-set! ,e0 ,idx ,e1)]) ,e-b)
       (convert-expr e0
                     (λ (a0)
                       (convert-expr e1
                                     (λ (a1)
                                       `(let ([_ (vector-set! ,a0 ,idx ,a1)])
                                          ,(convert-expr e-b k))))))]
      [`(let ([_ (while ,e-g ,e-b)]) ,e-r)
       
       `(let ([_ (while ,(convert-expr e-g (λ (a) a)) ,(convert-expr e-b (λ (a) a)))])
          ,(convert-expr e-r k))]
      
      [`(make-vector ,l)
       (convert-expr l
                     (λ (a-len)
                       (let ([x (gensym 'vec)])
                         `(let ([,x (make-vector ,a-len)]) ,(k x)))))]
      [`(vector-ref ,e0 ,e1)
       (convert-expr e0 (λ (a0) (define x (gensym)) `(let ([,x (vector-ref ,a0 ,e1)]) ,(k x))))]
      [`(vector-set! ,e0 ,i ,e1)
       (convert-expr e0 (λ (a0) (convert-expr e1 (λ (a1) `(let ([_ (vector-set! ,a0 ,i ,a1)]) ,(k '(void)))))))]
      [`(let ([,x ,e]) ,e-b)
       (convert-expr e (lambda (atom)
                         `(let ([,x ,atom]) ,(convert-expr e-b k))))]
      ;; new forms
      [`(app ,e0 ,e-rest ...)
       (convert-expr e0 (lambda (a0) (handle-rest e-rest '() a0 k)))]
      [`(fun-ref ,f) 
       (let ([x (gensym 'fref)])
         `(let ([,x (fun-ref ,f)])
      ,(k x)))]
      ))
  (define (per-defn definition)
    (match definition
      [`(define (,fname ,formals ...) ,e-body)
       `(define (,fname ,@formals) ,(convert-expr e-body (lambda (a) a)))]))
  (match p
    [`(program ,defns ...)
     `(program ,@(map per-defn defns))]))

;; Fairly easy pass: update to add the case described in the README.
(define (explicate-control p)
  ;; merge two hashes, assume no common keys
  (define (merge h0 h1)
    (foldl (λ (k0 h1) (hash-set h1 k0 (hash-ref h0 k0))) h1 (hash-keys h0)))
  (define (atom? a) (or (fixnum? a) (symbol? a) (boolean? a) (equal? a '(void))))
  (define (extend h label instruction)
    (hash-set h label `(seq ,instruction ,(hash-ref h label))))
  ;; basic idea: return a hash which maps blocks to a label name
  ;;
  ;; k is a continuation which gets called on the ultimate return value
  (define (expr->blocks e current-block k)
    (match e
      ;;
      ;; ... other cases...
      ;;;
      [`(if ,a ,e-t ,e-f)
       (define l-t (gensym 'lab))
       (define l-f (gensym 'lab))
       (define the-result-of-converting-the-true-branch-to-blocks (expr->blocks e-t l-t k)) 
       (define the-result-of-converting-the-false-branch-to-blocks (expr->blocks e-f l-f k))
       (define all-of-the-blocks-from-translating-both-branches
         (merge the-result-of-converting-the-true-branch-to-blocks
                the-result-of-converting-the-false-branch-to-blocks))
       (hash-set all-of-the-blocks-from-translating-both-branches
                 current-block ;; the current block's label
                 `(if (eq? ,a #f)
                      ;; take the false branch
                      (goto ,l-f)
                      ;; take the true branch...
                      (goto ,l-t)))]
      [`(let ([,x ,(? fixnum? n)]) ,e+)
       (extend (expr->blocks e+ current-block k) current-block `(assign ,x ,n))]
      [`(let ([,x ,(? boolean? b)]) ,e+)
       (extend (expr->blocks e+ current-block k) current-block `(assign ,x ,b))]
      [`(let ([,x ,(? symbol? y)]) ,e+)
       (extend (expr->blocks e+ current-block k) current-block `(assign ,x ,y))]
      [`(let ([,x (read)]) ,e+)
       (extend (expr->blocks e+ current-block k) current-block `(assign ,x (read)))]
      [`(let ([,x (- ,a)]) ,e+)
       (extend (expr->blocks e+ current-block k) current-block `(assign ,x (- ,a)))]
      [`(let ([,x (+ ,a0 ,a1)]) ,e+)
       (extend (expr->blocks e+ current-block k) current-block `(assign ,x (+ ,a0 ,a1)))]
      [`(let ([,x (< ,a0 ,a1)]) ,e+)
       (extend (expr->blocks e+ current-block k) current-block `(assign ,x (< ,a0 ,a1)))]
      [`(let ([,x (eq? ,a0 ,a1)]) ,e+)
       (extend (expr->blocks e+ current-block k) current-block `(assign ,x (eq? ,a0 ,a1)))]
      [`(let ([,x (not ,a1)]) ,e+)
       (extend (expr->blocks e+ current-block k) current-block `(assign ,x (not ,a1)))]
      
      
      [`(let ([,x (make-vector ,a)]) ,e+)
       (extend (expr->blocks e+ current-block k) current-block `(assign ,x (make-vector ,a)))]
      [`(let ([_ (vector-set! ,x ,i ,v)]) ,e+)
       (extend (expr->blocks e+ current-block k) current-block `(vector-set! ,x ,i ,v))]
      [`(let ([,x (void)]) ,e+)
       ;; I'll give you this one...
       (extend (expr->blocks e+ current-block k) current-block `(assign ,x (void)))]
      
      [`(let ([_ (while ,e-g ,e-b)]) ,e-r)
       ;; Basic idea: generate three new labels, l-rest, l-header, and l-body
       ;; then use expr->blocks pass a continuation 
       (define l-header (gensym 'lab))
       (define l-rest (gensym 'lab))
       (define l-body (gensym 'lab))
       ;; for example, as part of my solution I did....
       (define header-blocks
         (expr->blocks e-g
                       l-header
                       (λ (a-g) `(if (eq? ,a-g #f) (goto ,l-rest) (goto ,l-body)))))
       (define body-blocks (expr->blocks e-b l-body (lambda (a-b) `(goto ,l-header))))
       (define rest-blocks (expr->blocks e-r l-rest k))
       (define all (merge (merge header-blocks body-blocks) rest-blocks))
       (hash-set all current-block `(goto ,l-header))]
      [`(let ([,x (vector-ref ,e-v ,i)]) ,e+)
       (extend (expr->blocks e+ current-block k) current-block `(assign ,x (vector-ref ,e-v ,i)))]
      [`(vector-set! ,x ,i ,v)
       (hash current-block `(seq (vector-set! ,x ,i ,v) ,(k '(void))))]
      [(? atom? a)
       (hash current-block (k a))]
      ;; NEW
      [`(let ([,x (fun-ref ,f)]) ,e+)
       (extend (expr->blocks e+ current-block k) current-block `(assign ,x (fun-ref ,f)))]
      [`(let ([,x (app ,a-f ,a-args ...)]) ,e+)
       (extend (expr->blocks e+ current-block k) current-block `(assign ,x (app ,a-f ,@a-args)))]))
  (define (per-defn definition)
    (match definition
      [`(define (,fname ,formals ...) ,e-body)
       `(define (,fname ,@formals) ,(expr->blocks e-body fname (lambda (a) `(return ,a))))]))
  (match p
    [`(program ,defns ...)
     `(program ,@(map per-defn defns))]))

;; I'm giving to you this pass again...
(define (uncover-locals p)
  (define (h seq)
    (match seq
      [`(return ,_) (set)]
      [`(goto ,l) (set)]
      [`(if (,cmp ,a0 ,a1) (goto ,l0) (goto ,l1)) (set)]
      [`(set! ,_ ,_) (set)] ;; must be introduced by a let
      [`(seq (vector-set! ,x ,_ ,_) ,rest)
       (set-add (h rest) x)]
      [`(seq (assign ,x0 ,_) ,rest)
       (set-add (h rest) x0)]))
  (define (per-defn definition)
    (match definition
      [`(define (,fname ,formals ...) ,blocks)
       (define locals (set-union (list->set formals)
                                 (foldl (λ (block acc) (set-union acc (h (hash-ref blocks block))))
                                        (set)
                                        (hash-keys blocks))))
       `(define ,locals (,fname ,@formals) ,blocks)]))
  (match p
    [`(program ,definitions ...)
     `(program ,@(map per-defn definitions))]))

;; The output of this pass is almost x86, but there will still be an
;; issue: we won't be using *registers*, we'll keep using variables
;; for now.
;; 
;; NEW: need to handle fun-ref as an atom
(define (select-instructions p)
  ;; Translate ANF-ified C0 to a block of instructions
  (define (c1->block c1)
    (define (h-atom a)
      (match a
        ['(void)       `(imm ,(void-magic-value))]
        [(? fixnum? n) `(imm ,n)]
        [(? symbol? x) `(var ,x)]
        [(? boolean? b) `(imm ,(if b 1 0))]
        [_ (second a)]))
    (define (h seq)
      (match seq
        ;; returns--we leave out the final (ret), we will take care of
        ;; that in the epilogue
        [`(return ,a)
         `((movq ,(h-atom a) (reg rax))
           ;; now jump to the conclusion
           (jmp ,(conclusion-block-name)))]

        ;; 
        ;; other forms
        ;; 
        [`(seq (assign ,x (read)) ,rest)
         `((callq read_int64 0)
           (movq (reg rax) (var ,x))
           ,@(h rest))]
        [`(seq (assign ,x ,(? fixnum? n)) ,rest)
         `((movq (imm ,n) (var ,x))
           ,@(h rest))]
        [`(seq (assign ,x ,(? symbol? y)) ,rest)
         `((movq (var ,y) (var ,x))
           ,@(h rest))]
        [`(seq (assign ,x ,(? boolean? b)) ,rest)
         (cond
           [(equal? b #f) `((movq (imm 0) (var ,x)) ,@(h rest))]
           [else `((movq (imm 1) (var ,x)) ,@(h rest))])]
        [`(seq (assign ,x (- ,a)) ,rest)
         `((movq ,(h-atom a) (reg rax))
           (negq (reg rax))
           (movq (reg rax) (var ,x))
           ,@(h rest))]
        [`(seq (assign ,x (+ ,a0 ,a1)) ,rest)
         `((movq ,(h-atom a0) (reg rax))
           (addq ,(h-atom a1) (reg rax))
           (movq (reg rax) (var ,x))
           ,@(h rest))]
        [`(seq (assign ,x (not ,y)) ,rest)
         (cond
           [(equal? x y) `((xorq (imm 1) (var ,x)) ,@(h rest))]
           [(equal? y #f) `((movq (imm 0) (reg rax)) (xorq (imm 1) (reg rax)) (movq (reg rax) (var ,x)) ,@(h rest))]
           [else `((movq (imm 1) (reg rax)) (xorq (imm 1) (reg rax)) (movq (reg rax) (var ,x)) ,@(h rest))])]
        [`(seq (assign ,x (< ,a0 ,a1)) ,rst)
         `((cmpq ,(h-atom a1) ,(h-atom a0)) (set l (byte-reg al)) (movzbq (byte-reg al) (reg rax)) (movq (reg rax) (var ,x)) ,@(h rst))]
        [`(seq (assign ,x (eq? ,a0 ,a1)) ,rst)
         `((cmpq ,(h-atom a0) ,(h-atom a1)) (set e (byte-reg al)) (movzbq (byte-reg al) (reg rax)) (movq (reg rax) (var ,x)) ,@(h rst))]
        ;; cmp is {eq?, <}
        [`(if (,cmp ,a0 ,a1) (goto ,l0) (goto ,l1))
         (cond
           [(equal? cmp 'eq?) `((cmpq ,(h-atom a0) ,(h-atom a1)) (jmp-if e ,l0) (jmp ,l1))]
           [else `((cmpq ,(h-atom a1) ,(h-atom a0)) (jmp-if l ,l0) (jmp ,l1))])]

        
        [`(seq (assign ,x (void)) ,rest)
         ;; Advice: use (void-magic-value) in system.rkt
         `((movq ,(h-atom '(void)) (reg rax)) (movq (reg rax) (var ,x)) ,@(h rest))]
        [`(seq (assign ,x (make-vector ,i)) ,rest)
         ;; moveq i to %rdi, then callq make_vector (1 argument), then movq rax to x
         `((movq ,(h-atom i) (reg rdi)) (callq make_vector 1) (movq (reg rax) (var ,x)) ,@(h rest))]
        [`(seq (assign ,x (vector-ref ,a ,i)) ,rest)
         ;; movq a to rax, then movq OFF(%rax) to x (where OFF is (i+1)*8)
         `((movq ,(h-atom a) (reg rax)) (movq (deref (reg rax) ,(* (+ i 1) 8)) (var ,x)) ,@(h rest))]
        [`(seq (vector-set! ,a0 ,i ,a-v) ,rest)
         ;; movq a to rax, then move a-v to OFF(%rax), where OFF is (i+1)*8
         `((movq ,(h-atom a0) (reg rax)) (movq ,(h-atom a-v) (deref (reg rax) ,(* (+ i 1) 8))) ,@(h rest))]

        
        ['(void) '()] 
        [`(goto ,l)
         `((goto ,l))]
        ;; NEW
        [`(seq (assign ,x (fun-ref ,f)) ,rest)
         `((leaq (fun-ref ,f) (var ,x))
           ,@(h rest))]
        ;; non-tail application form:
        ;; - move each argument into a register in the order %rdi, %rsi, %rdx, %rcx, %r8, %r9
        ;; - Generate an `(indirect-callq ,fun) instruction (we will render this later)
        ;; - movq the result (left in rax) into the lhs
        [`(seq (assign ,lhs (app ,a-f ,args ...)) ,next)
         (define (copy-arguments remaining-args remaining-registers)
           (match remaining-args
             ['() `()]
             [`(,a . ,rst)
              `((movq ,(h-atom a) (reg ,(first remaining-registers))) ,@(copy-arguments rst (rest remaining-registers)))]))
         `(,@(copy-arguments args (argument-registers-list))
           (indirect-callq ,(h-atom a-f))
           (movq (reg rax) (var ,lhs))
           ,@(h next))]))
    (h c1))

  ;; per-defn here needs to build blocks+, the transformed blocks, and
  ;; also needs to add a little bit of code to the beginning of the
  ;; first block to copy the arguments from registers to their
  ;; respective locations
  (define (per-defn defn)
    (match-define `(define ,locals (,f ,args ...) ,blocks) defn)
     
    ;; basic idea:
    ;; - define blocks+, the new updated blocks (don't forget the conclusion block) 
    ;;
    (define transformed-blocks
      (for/hash ([(lbl instrs) (in-hash blocks)])
        (values lbl (c1->block instrs))))
    
    (define blocks+ (hash-set
                     transformed-blocks
                     (conclusion-block-name)
                     '((retq))))
    (define entry (hash-ref blocks+ f))
    ;; build a sequqence of `movq` instructions that move the argument registers into the variables
    (define move-sequence (for/list ([a args] [r (argument-registers-list)])`(movq (reg ,r) (var ,a))))
    ;; prepend the move sequence to the entry...
    (define blocks++ (hash-set blocks+ f (append move-sequence entry))) 
    `(define ,locals (,f ,@args) ,blocks++))
  ;; the input is C0: h is (hash 'start '(let ...))
  (match p
    [`(program ,defns ...)
      ;; also add an empty conclusion block
     `(program ,@(map per-defn defns))]))

;; Take variables into either the stack/registers
(define (assign-homes p)
  ;; traverse each instruction in the block to replace (var x) with
  ;; the appropriate stack position. Note: this will leave some
  ;; instructions
  (define (per-defn definition)
    (match-define `(define ,locals (,f ,args ...) ,blocks) definition)
    (define var->stackloc
      (let ([l (set->list locals)])
        (foldl (lambda (v i h) (hash-set h v (* -8 i))) (hash) l (range 1 (add1 (length l))))))
    ;; map (var x) to its home (an offset of rbp)
    (define (home a)
      (match a
        [`(var ,x) `(deref (reg rbp) ,(hash-ref var->stackloc x 'unknown))]
        [`(imm ,i) a]
        [`(reg ,r) a]
        [`(byte-reg ,al) a]
        [`(deref ,rest ...) a]
        [_ a]))    
    (define (h block)
      (match block
        ;; 
        ;; ... previous forms...
        ;; 
        [(cons `(movq ,a ,b) rest) (cons `(movq ,(home a) ,(home b)) (h rest))]
        [(cons `(negq ,a) rest) (cons `(negq ,(home a)) (h rest))]
        [(cons `(addq ,a ,b) rest) (cons `(addq ,(home a) ,(home b)) (h rest))]
        [(cons `(movzbq ,a ,b) rest) (cons `(movzbq ,(home a) ,(home b)) (h rest))]
        [(cons `(cmpq ,a ,b) rest) (cons `(cmpq ,(home a) ,(home b)) (h rest))]
        [(cons `(xorq ,a ,b) rest) (cons `(xorq ,(home a) ,(home b)) (h rest))]
        [(cons `(set ,a ,b) rest) (cons `(set ,a ,(home b)) (h rest))]
        [(cons `(pushq ,a) rest) (cons `(pushq ,(home a)) (h rest))]
        [(cons `(popq ,a) rest) (cons `(popq ,(home a)) (h rest))]
        ;; new
        [`((retq) ,rest ...)
         (cons '(retq) (h rest))]
        [`((indirect-callq ,a) ,rest ...)
         (cons `(indirect-callq ,(home a)) (h rest))]
        [`((callq ,f ,i) ,rest ...)
         (cons `(callq ,f ,i) (h rest))]
        [`((leaq (fun-ref ,f) ,a) ,rest ...)
         (cons `(leaq (fun-ref ,f) ,(home a)) (h rest))]
        ['() '()]
        [_ (cons (first block) (h (rest block)))]))
    (define blocks+ (foldl (λ (blk acc)
                           (hash-set acc blk (h (hash-ref blocks blk)))) blocks (hash-keys blocks)))
    `(define ,var->stackloc (,f ,@args) ,blocks+)) ;; end of per-defn
  (match p
    [`(program ,defns ...)
     `(program ,@(map per-defn defns))]))

;; new:
;; - the destination of leaq must be a register
;; - the argument of 
(define (patch-instructions p)
  (define (patch-tail block)
    (match block
      ['() '()]
      ;; 
      ;; ... older forms...
      ;;
      [`((movq (deref (reg ,r0) ,i0) (deref (reg ,r1) ,i1)) ,rest ...)
       (append `((movq (deref (reg ,r0) ,i0) (reg rcx)) (movq (reg rcx) (deref (reg ,r1) ,i1))) (patch-tail rest))]
      
      [`((movzbq (byte-reg ,r) (deref (reg ,r1) ,i1)) ,rest ...)
       (append `((movzbq (byte-reg ,r) (reg rcx)) (movq (reg rcx) (deref (reg ,r1) ,i1))) (patch-tail rest))]
      
      [`((cmpq ,a (deref (reg ,r1) ,i1)) ,rest ...)
       (append `((movq (deref (reg ,r1) ,i1) (reg rcx)) (cmpq ,a (reg rcx))) (patch-tail rest))]
     
      [`((cmpq ,a (imm ,d)) ,rest ...)
       (append `((movq (imm ,d) (reg rcx)) (cmpq ,a (reg rcx))) (patch-tail rest))]
      ;; NEW
      [`((leaq ,src (reg ,r)) ,rest ...)
       (append `(leaq ,src (reg ,r)) (patch-tail rest))]
      [`((leaq ,src ,dst) ,rest ...)
       (append `((leaq ,src (reg rax)) (movq (reg rax) ,dst)) (patch-tail rest))]
      [`(,instr ,rest ...)
       `(,instr ,@(patch-tail rest))]))
  (define (per-defn defn)
    (match-define `(define ,info (,f ,formals ...) ,blocks) defn)
    (define blocks+
      (foldl (lambda (k a) (hash-set a k (patch-tail (hash-ref blocks k))))
             (hash)
             (hash-keys blocks)))
    `(define ,info (,f ,@formals) ,blocks+))
  (match p
    [`(program ,defns ...)
     `(program ,@(map per-defn defns))]))

(define (prelude-and-conclusion p)
  (define (align16 n)
    (bitwise-and (+ n 15) (bitwise-not 15)))

  ;; walk over all blocks in a hash and replace '(jmp conclusion) to
  ;; `(jmp ,name)
  (define (rename-conclusion blocks name)
    ;; I'll let you write this one (if it's helpful...)
    (define (h instr)
      (match instr
        [`(jmp ,blk) #:when (equal? blk (conclusion-block-name))
         `(jmp ,name)]
        [i i]))
    (foldl (lambda (k acc) (hash-set acc k (map h (hash-ref blocks k))))
           (hash)
           (hash-keys blocks)))
  
  (define (per-defn p)
    (match p
      [`(define ,locals (,f ,args ...) ,blocks)
       ;; negative number, added to %rsp
       (define space-needed (if (empty? (hash-values locals))
                                0
                                (- (align16 (- (apply min (hash-values locals)))))))
       (define start-block (hash-ref blocks f))
       (define new-start-block
         `((pushq (reg rbp))
           (movq (reg rsp) (reg rbp))
           (addq (imm ,space-needed) (reg rsp))
           ,@start-block))
       (define conclusion-block
         (if (equal? f (entry-symbol))
             `(;; move result into %rdi and print_int64 it
               (movq (reg rax) (reg rdi))
               (callq print_int64 0)
               ;; 0 return value (to the terminal/system) into %rax
               (movq (imm 0) (reg rax))
               ;; reinstate stored %rbp
               (movq (reg rbp) (reg rsp))
               (popq (reg rbp))
               ;; transfer back to caller
               (retq))
             ;; else, just return...
             `((movq (reg rbp) (reg rsp))
               (popq (reg rbp))
               (retq))))
       (define my-conclusion-block (gensym 'conclusion))
       (define blocks+ 
         (rename-conclusion
          (hash-set (hash-remove (hash-set blocks f new-start-block)
                                (conclusion-block-name))
                   my-conclusion-block
                   conclusion-block)
          my-conclusion-block))
       ;; change the block name from (conclusion-block-name) to a
       ;; per-definition conclusion. Make sure you use hash-remove to
       ;; clear the previous key from the hash so that it is not
       ;; printed!
       `(define ,locals (,f ,@args) ,blocks+)]))
  (match p
    [`(program ,defns ...)
     `(program ,@(map per-defn defns))]))

;; Dump x86-64 code to GAS assmbler
(define (dump-x86-64 p)
  (define functions (set-add (list->set (match p [`(program ,_ (define ,_ (,fs ,_ ...) ,_) ...) fs])) 'main))
  (define (render-op op)
    (match op
      [`(imm ,i) (format "$~a" i)]
      [`(reg ,x) (format "%~a" (symbol->string x))]
      [`(byte-reg ,x) (format "%~a" (symbol->string x))]
      [`(deref (reg ,reg) ,i) (format "~a(%~a)" i (symbol->string reg))]
      [_ (symbol->string (rt-sym op))]))
  (define (render-instr instr)
    (match instr
      ;; 
      ;; ...older forms...
      ;; 
      [`(xorq ,src ,dst) (format "xorq ~a, ~a" (render-op src) (render-op dst))]
      [`(movzbq ,src ,dst) (format "movzbq ~a, ~a" (render-op src) (render-op dst))]
      [`(pushq ,dst) (format "pushq ~a" (render-op dst))]
      [`(popq ,dst) (format "popq ~a" (render-op dst))]
      [`(cmpq ,src ,dst) (format "cmpq ~a, ~a" (render-op src) (render-op dst))]
      [`(set ,c ,dst)
       (cond
         [(equal? c 'l) (format "setl ~a" (render-op dst))]
         [else (format "sete ~a" (render-op dst))])]
      [`(jmp ,o) (format "jmp ~a" (render-op o))]
      [`(jmp-if ,c ,dst)
       (cond
         [(equal? c 'l) (format "jl ~a" (render-op dst))]
         [else (format "je ~a" (render-op dst))])]
      [`(negq ,x) (format "negq ~a" (render-op x))]
      [`(movq ,x ,y)
       (format "movq ~a, ~a" (render-op x) (render-op y))]
      [`(addq ,x ,y)
       (format "addq ~a, ~a" (render-op x) (render-op y))]
      [`(callq ,(? label? l) ,(? nonnegative-integer? num-args))
       ;; must call rt-sym here!
       (format "callq ~a" (symbol->string (rt-sym l)))]
      ['(retq) "retq"]
      [`(goto ,l) (format "jmp ~a" (render-op l))]
      ['(leave) "leave"]
      ;; NEW forms
      [`(leaq (fun-ref ,f) ,dst) ;; make sure to call (rt-sym f) when rendering f here!
       (format "leaq ~a(%rip), ~a" (rt-sym f) (render-op dst))]
      [`(indirect-callq ,a) (format "callq *~a" (render-op a))]))
  (define (render-block block name)
    (define txt-label (if (set-member? functions name) (format "~a:\n" (rt-sym name)) (format "~a:\n" name)))
    (apply string-append
           (cons txt-label
                 (map (λ (instr) (format "    ~a\n" (render-instr instr))) block))))
  (define (per-defn defn)
    (match-define `(define ,_ (,f ,formals ...) ,blocks) defn)
    (foldl (lambda (k acc) (string-append acc (render-block (hash-ref blocks k) k)))
           ""
           (hash-keys blocks)))
  (match p
    [`(program ,defns ...)
     (string-append
      ;; Tells the ABI that we're OK with non-executable stacks (security enhancement)
      (format ".globl ~a\n" (rt-sym (entry-symbol)))
      ;; include these for sure
      (runtime-function-externs)
      (foldl (λ (defn acc) (string-append acc (per-defn defn)))
             ""
             defns))]))
