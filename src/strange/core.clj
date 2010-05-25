(ns strange.core)

;;; Take a VM approach first, and build up layers on top of that

(def instructions {})

(defmacro definstr
  [name [& args] & body]
  `(alter-var-root
    #'instructions
    assoc '~name
    (fn [[~@args] ~'state]
      ~@body)))

(defn do-enter
  [state n]
  (let [[vals data] (split-at n (:data state))
	regs (zipmap (range n) vals)]
    (assoc state
      :data data
      :regs regs)))

(definstr :get [n]
  (assoc state :data (conj (:data state) ((:regs state) n))))

(defn create-closure
  [code regs strict?]
  (atom {:code code, :regs regs, :strict? strict?}))

(definstr :closure [& code]
  (let [data (conj (:data state) (create-closure code (:regs state) false))]
    (assoc state :data data)))

(defn cook
  [state f]
  (if (= (:arity f) (count (:args f)))
    (create-closure `((:push ~@(:args f)) (:jumpg ~(:sc f))) nil (:strict? f))
    f))

(defn strict-eval
  [state]
  (let [[f & data] (:data state)]
    (if (and (instance? clojure.lang.Atom f) (map? @f))
      (if (:strict? @f)
	(let [code (concat '((:dup) (:eval) (:drop)) (:code state))]
	  (assoc state :code code))
	state)
      state)))

(definstr :pushsc [sym]
  (if (contains? (:cache state) sym)
    (assoc state :data (conj (:data state) ((:cache state) sym)))
    (let [[arity strict?] (first ((:env state) sym))
	  partial (cook state {:sc sym :arity arity :strict? strict?})
	  data (conj (:data state) partial)
	  cache (assoc (:cache state {}) sym partial)]
      (strict-eval (assoc state :data data :cache cache)))))

(definstr :curry [n]
  (let [fun (first (:data state))
	[args data] (split-at n (next (:data state)))
	args (concat (:args fun) args)
	res (cook state (assoc fun :args args))]
    (strict-eval (assoc state :data (conj data res)))))

(definstr :dup []
  (let [[v & data] (:data state)]
    (assoc state :data (conj data v v))))

(definstr :drop []
  (let [[v & data] (:data state)]
    (assoc state :data data)))

(defn do-jump
  [state f]
  (if (map? @f)
    (let [code (:code @f)
	  regs (:regs @f)]
      (assoc state
	:code code
	:regs regs))
    ((instructions :ret-val)
     nil
     (assoc state :data (conj (:data state) @f)))))

(definstr :jump []
  (let [[f & data] (:data state)]
    (do-jump (assoc state :data data) f)))

(definstr :jumpg [sym]
  (let [[n & code] ((:env state) sym)]
    (assoc (do-enter state (n 0))
      :code code)))

(definstr :update [closure]
  (let [val (first (:data state))]
    (reset! closure val)
    state))

(definstr :eval []
  ;;; Evaluate the closure on the top of the state, updating it as needed
  (let [[closure & data] (:data state)]
    (if (map? @closure)
      ;; push a continuation and jump to the closure
      (let [cont (create-closure `((:update ~closure) ~@(:code state))
				 (:regs state)
				 false)
	    cstack (conj (:cstack state) cont)]
	(do-jump (assoc state :data data :cstack cstack) closure))
      ;; unbox the cached value
      (let [data (conj data @closure)]
	(assoc state :data data)))))

(definstr :case [tag base & code]
  (let [[e & data] (:data state)]
    (cond
     (and (vector? e) (= (first e) tag))
     (let [nregs (zipmap (iterate inc base) (rest e))
	   regs (merge (:regs state) nregs)]
       (assoc state
	 :data data
	 :code code
	 :regs regs))

     (or (= e tag) (= tag :default))
     (let [regs (merge (:regs state) {base e})]
       (assoc state
	 :data data
	 :code code
	 :regs regs))

     :else
     state)))

(definstr :push [& items]
  (let [data (concat items (:data state))]
    (assoc state :data data)))

(definstr :push-lit [item]
  (let [data (conj (:data state) (atom item))]
    (assoc state :data data)))

(definstr :ret-val []
  ;; Pop a continuation and jump to it
  (let [[cont & cstack] (:cstack state)]
    (do-jump (assoc state :cstack cstack) cont)))

(definstr :cljcall [n sym]
  (let [[args data] (split-at n (:data state))
	val (apply @(resolve sym) args)
	data (conj data val)]
    (assoc state :data data)))

(definstr :pcons [type n]
  (let [[vals data] (split-at n (:data state))
	box (apply vector type vals)
	data (conj data box)]
    (assoc state :data data)))

(defn run-program
  [prog]
  (let [init {:code (concat (next (prog 'main))) :regs {} :env prog}]
    (loop [state init]
      (if (seq (:code state))
	(recur ((instructions (first (first (:code state))))
		(rest (first (:code state)))
		(assoc state :code (next (:code state)))))
	(first (:data state))))))

;;;; Compiler

(declare compile-form)

(defn compile-lit
  [env lit]
  `((:push-lit ~lit)))

(defn compile-symbol
  [env sym]
  (if (contains? env sym)
    `((:get ~(env sym)))
    `((:pushsc ~sym))))

(defn compile-app
  [env form]
  `(~@(mapcat #(compile-form env %)
	      (reverse form))
    (:curry ~(count (next form)))))

(defn compile-quote
  [env form]
  (compile-lit env (second form)))

(defn compile-case
  [env form]
  (let [[_ d & forms] form]
    `((:closure
       ~@(compile-form env d)
       (:eval)
       ~@(map (fn [[tag bindings body]]
		(let [base (count env)
		      nenv (zipmap bindings (iterate inc base))
		      env (merge env nenv)]
		  `(:case ~tag ~base ~@(compile-form env body) (:jump))))
	      (partition 3 forms))))))

(defn compile-pcons
  [env form]
  (let [[_ type & vals] form]
    `((:closure
       ~@(mapcat (fn [f] (compile-form env f)) (reverse vals))
       (:pcons ~type ~(count vals))
       (:ret-val)))))
  
(defn compile-form
  [env form]
  ((cond
    (symbol? form) compile-symbol
    (nil? form) compile-symbol
    (not (list? form)) compile-lit
    (= 'quote (first form)) compile-quote
    (= 'case (first form)) compile-case
    (= '%cons (first form)) compile-pcons
    :else compile-app)
   env form))

(defn args->env
  [args]
  (zipmap args (range)))

(defn compile-define
  [form]
  (let [[_ name args body] form]
    {name `([~(count args) false]
	    ~@(compile-form (args->env args) body)
	    ~(if (= name 'main) '(:eval) '(:jump)))}))

(defn compile-defstrict
  [form]
  (let [[_ name args body] form]
    {name `([~(count args) true]
	    ~@(compile-form (args->env args) body)
	    (:jump))}))

(defn compile-toplevel
  [form]
  ((cond
    (= 'define (first form)) compile-define
    (= 'defstrict (first form)) compile-defstrict
    :else (constantly {}))
   form))

(defn standalone-compile
  [program]
  (apply merge (map compile-toplevel program)))

(defn interop-compile
  [forms]
  (apply merge
	 (map (fn [[op n]]
		{op
		 `([~n true]
		   ~@(mapcat (fn [i] `((:get ~(- n 1 i)) (:eval)))
			     (range n))
		   (:cljcall ~n ~op)
		   (:ret-val))})
	      forms)))

(def stdlib
     (let [interop
	   (interop-compile
	    '[[+ 2] [- 2] [* 2] [/ 2] [zero? 1]])
	   stdfns
	   (standalone-compile
	    '((define if
		[pred t f]
		(case pred
		      true [] t
		      false [] f))
	      (defstrict nil
		[]
		(%cons nil))
	      (defstrict cons
		[first rest]
		(%cons cons first rest))
	      (define first
		[coll]
		(case coll
		      nil [] nil
		      cons [x xs] x))
	      (define rest
		[coll]
		(case coll
		      nil [] nil
		      cons [x xs] xs))
	      (define nth
		[coll n]
		(case coll
		      nil []
		      nil
		      
		      cons [x xs]
		      (if (zero? n) x (nth xs (- n 1)))))
	      (define nil?
		[coll]
		(case coll
		      nil [] true
		      cons [x xs] false))))]
       (apply merge interop stdfns)))
	   
(defn compile-program
  [prog]
  (merge stdlib (standalone-compile prog)))

(defn eval-program
  [prog]
  (run-program (compile-program prog)))

(def samp
     '((define main [] (square (+ 1 2)))
       (define square [n] (* n n))))

(def samp2
     '((define fib-loop
	 [n a b]
	 (if (zero? n)
	   b
	   (fib-loop (- n 1) b (+ a b))))
       (define fib
	 [n]
	 (fib-loop n 1 0))
       (define main [] (fib 5000))))

(def samp3
     '((define integers
	 [n]
	 (cons n (integers (+ n 1))))
       (define main [] (nth (integers 0) 5000))))

(def samp4
     '((define map2
	 [f coll1 coll2]
	 (case coll1
	       nil []
	       nil

	       cons [x xs]
	       (case coll2
		     cons [y ys]
		     (cons (f x y) (map2 f xs ys)))))
       (define fibs
	 []
	 (cons 0 (cons 1 (map2 + fibs (rest fibs)))))
       (define main [] (nth fibs 5000))))
