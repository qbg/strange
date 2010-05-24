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

(definstr :enter [n]
  (let [[vals data] (split-at n (:data state))
	regs (zipmap (range n) vals)]
    (assoc state
      :data data
      :regs regs)))

(definstr :get [n]
  (assoc state :data (conj (:data state) ((:regs state) n))))

(definstr :closure [& code]
  (let [data (:data state)
	f {:code code :regs (:regs state)
	   :result (atom ::init)}
	data (conj data f)]
    (assoc state :data data)))

(defn cook
  [state f]
  (if (= (:arity f) (count (:args f)))
    {:code `(~@(map (fn [v] `(:push ~v)) (reverse (:args f)))
	     (:jumpg ~(:sc f)))
     :result (atom ::init)}
    f))

(definstr :pushsc [sym]
  (if (contains? (:cache state) sym)
    (assoc state :data (conj (:data state) ((:cache state) sym)))
    (let [partial {:sc sym :arity (first ((:env state) sym))}
	  data (conj (:data state) partial)
	  cache (assoc (:cache state {}) sym partial)]
      (assoc state :data data))))

(definstr :curry [n]
  (let [fun (first (:data state))
	[args data] (split-at n (next (:data state)))
	args (concat (:args fun) args)
	res (cook state (assoc fun :args args))]
    (assoc state :data (conj data res))))

(definstr :jump []
  (let [[f & data] (:data state)
	code (:code f)
	regs (:regs f)]
    (assoc state
      :data data
      :code code
      :regs regs)))

(definstr :mjump []
  (let [[f & data] (:data state)
	code (:code f)
	regs (:regs f)
	res (:result f)
	result (conj (:result state) res)]
    (if (= @res ::init)
      (assoc state
	:data data
	:code code
	:regs regs
	:result result)
      (let [data (conj data @res)]
	((instructions :ret-val)
	 nil
	 (assoc state
	   :data data
	   :result (conj (:result state) nil)))))))

(definstr :jumpg [sym]
  (let [code (next ((:env state) sym))]
    (assoc state
      :code code)))

(definstr :eval [& code]
  ;; save state and then execute the code on the top of the stack
  (let [cstack (conj (:cstack state) (:code state))
	rstack (conj (:rstack state) (:regs state))]
    (assoc state
      :code code
      :cstack cstack
      :rstack rstack)))

(definstr :case [tag & code]
  (let [[e & data] (:data state)]
    (cond
     (and (vector? e) (= (first e) tag))
     (let [nregs (zipmap (iterate dec -1) (rest e))
	   regs (merge (:regs state) nregs)]
       (assoc state
	 :data data
	 :code code
	 :regs regs))

     (or (= e tag) (= tag :default))
     (let [regs (merge (:regs state) {-1 e})]
       (assoc state
	 :data data
	 :code code
	 :regs regs))

     :else
     state)))

(definstr :push [item]
  (let [data (conj (:data state) item)]
    (assoc state :data data)))

(definstr :ret-val []
  (let [cstack (next (:cstack state))
	rstack (next (:rstack state))
	code (first (:cstack state))
	regs (first (:rstack state))
	nstate
	(assoc state
	  :cstack cstack
	  :rstack rstack
	  :code code
	  :regs regs
	  :result (next (:result state)))]
    (if (first (:result state))
      (reset! (first (:result state)) (first (:data state))))
    nstate))

(definstr :cljcall [n sym]
  (let [[args data] (split-at n (:data state))
	val (apply @(resolve sym) args)
	data (conj data val)]
    (assoc state :data data)))

(defn run-program
  [prog]
  (let [init {:code (next (prog 'main)) :regs {} :env prog}]
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
  `((:closure (:push ~lit) (:ret-val))))

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
       (:eval ~@(compile-form env d) (:jump))
       ~@(map (fn [[tag bindings body]]
		(let [nenv (zipmap bindings (iterate dec -1))
		      env (merge env nenv)]
		  `(:case ~tag ~@(compile-form env body) (:jump))))
	      (partition 3 forms))))))

(defn compile-form
  [env form]
  ((cond
    (symbol? form) compile-symbol
    (not (list? form)) compile-lit
    (= 'quote (first form)) compile-quote
    (= 'case (first form)) compile-case
    :else compile-app)
   env form))

(defn args->env
  [args]
  (zipmap args (range)))

(defn compile-define
  [form]
  (let [[_ name args body] form]
    {name `(~(count args)
	    (:enter ~(count args))
	    ~@(compile-form (args->env args) body)
	    (:jump))}))

(defn compile-toplevel
  [form]
  ((cond
    (= 'define (first form)) compile-define)
   form))

(defn s-cons
  [first rest]
  (vector 'cons first rest))

(def low-prims
     '{if
       [3
	(:enter 3)
	(:eval (:get 0) (:mjump))
	(:case true (:get 1) (:jump))
	(:case false (:get 2) (:jump))]

       nil
       [0
	(:push [nil])
	(:ret-val)]

       cons
       [2
	(:enter 2)
	(:get 1)
	(:get 0)
	(:cljcall 2 s-cons)
	(:ret-val)]

       first
       [1
	(:enter 1)
	(:eval (:get 0) (:jump))
	(:case nil (:pushsc nil) (:jump))
	(:case cons (:get -1) (:jump))]

       rest
       [1
	(:enter 1)
	(:eval (:get 0) (:jump))
	(:case nil (:pushsc nil) (:jump))
	(:case cons (:get -2) (:jump))]})
       

(def builtins
     (->> '[[+ 2] [- 2] [* 2] [/ 2] [zero? 1] [nil? 1]]
	  (map (fn [[op n]]
		 {op
		  `(~n
		    (:enter ~n)
		    ~@(map (fn [i] `(:eval (:get ~(- n 1 i)) (:mjump)))
			   (range n))
		    (:cljcall ~n ~op)
		    (:ret-val))}))
	  (apply merge low-prims)))

(defn compile-program
  [prog]
  (apply merge
	 builtins
	 (map compile-toplevel prog)))

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
       (define nth
	 [coll n]
	 (if (zero? n)
	   (first coll)
	   (nth (rest coll) (- n 1))))
       (define main [] (nth (integers 0) 5000))))

