(ns strange.core)

;;; Take a VM approach first, and build up layers on top of that

(def instructions {})

(defmacro definstr
  [name [& bindings] & body]
  `(alter-var-root
    #'instructions assoc '~name
    (fn 
      [args# ~'state]
      (let [[~@bindings] args#]
	~@body))))

(defmacro update
  [k f & args]
  `(update-in ~'state [~k] ~f ~@args))

(defn memofn
  "Produce a lazily evaluated functional value (function of no arguments)"
  [f]
  (let [val (atom ::initial)]
    (fn []
      (if (= @val ::initial)
	(reset! val f)
	@val))))

(defn run-instr
  [state instr]
  ((instructions (first instr)) (rest instr) state))

(defn run-code
  [code locals env cache]
  (let [istate {:locals locals :env env :cache cache}
	state (reduce run-instr istate code)]
    (first (:data state))))

(definstr :push [val]
  (update :data conj val))

(defn cook-fn
  [f state]
  (if (= (count (:args f)) (:arity f))
    (let [mf (memofn #(run-code (:code f)
				(:args f)
				(:env state)
				(:cache state)))]
      (if (:strict? f)
	(trampoline mf)
	mf))
    f))

(definstr :pushval [sym]
  (let [pushv
	(if-let [val (get @(:cache state) sym)]
	  val
	  (let [code ((:env state) sym)
		f {:code (rest code)
		   :arity ((first code) 0)
		   :strict? ((first code) 1)}
		cooked (cook-fn f state)]
	    (swap! (:cache state) assoc sym cooked)
	    cooked))]
    (update :data conj pushv)))

(definstr :pop [n]
  (update :data nthnext n))

(definstr :local [n]
  (update :data conj (nth (:locals state) n)))

(definstr :cljcall [n sym]
  (let [args (take n (:data state))
	data (nthnext (:data state) n)]
    (assoc state :data (conj data (apply @(resolve sym) args)))))

(definstr :if []
  (let [[pred true-case false-case & data] (:data state)]
    (assoc state :data (conj data (if pred true-case false-case)))))

(definstr :curry [n]
  (let [f (first (:data state))
	f (if (fn? f) (trampoline f) f)
	[vals data] (split-at n (rest (:data state)))
	args (concat (:args f) vals)
	newf (cook-fn (assoc f :args args) state)]
    (assoc state :data (conj data newf))))

(definstr :unbox []
  (let [[val & data] (:data state)
	val (if (fn? val)
	      (trampoline val)
	      val)]
    (assoc state :data (conj data val))))

;;; Compiler

(defmacro compile-primitives
  [& forms]
  `'~(zipmap
      (map first forms)
      (map (fn [[sym n]]
	     `([~n true]
	       ~@(mapcat (fn [i]
			   `((:local ~(- n 1 i))
			     (:unbox)))
			 (range n))
	       (:cljcall ~n ~sym)))
	   forms)))

(defn s-cons
  [first rest]
  {:f first, :r rest})

(defn s-first
  [cons]
  (:f cons))

(defn s-rest
  [cons]
  (:r cons))

(def low-primitives
     '{cons
       [[2 true]
	(:local 1)
	(:local 0)
	(:cljcall 2 s-cons)]

       first
       [[1 true]
	(:local 0)
	(:unbox)
	(:cljcall 1 s-first)]

       rest
       [[1 true]
	(:local 0)
	(:unbox)
	(:cljcall 1 s-rest)]

       unbox
       [[1 true]
	(:local 0)]
       
       nil
       [[0 true]
	(:push)]})

(def standard-lib
     (merge low-primitives
	    (compile-primitives
	     (+ 2)
	     (- 2)
	     (* 2)
	     (/ 2)
	     (zero? 1)
	     (nil? 1))))

(declare compile-form)

(defn compile-lit
  [env lit]
  `((:push ~lit)))

(defn compile-symbol
  [env sym]
  (if (get env sym)
    `((:local ~(env sym)))
    `((:pushval ~sym))))

(defn compile-if
  [env form]
  (let [[pred t f] (rest form)]
    `(~@(compile-form env f)
      ~@(compile-form env t)
      ~@(compile-form env pred)
      (:unbox)
      (:if))))

(defn compile-quote
  [env form]
  `((:push ~(second form))))

(defn compile-app
  [env form]
  `(~@(mapcat (fn [frm] (compile-form env frm))
	      (reverse form))
    (:unbox)
    (:curry ~(dec (count form)))))

(defn compile-form
  [env form]
  ((cond
    (symbol? form) compile-symbol
    (nil? form) compile-symbol
    (not (list? form)) compile-lit
    (= (first form) 'if) compile-if
    (= (first form) 'quote) compile-quote
    :else compile-app)
   env form))

(defn args->env
  [args]
  (into {} (map-indexed (fn [n x] [x n]) args)))

(defn compile-fn
  [args body]
  (compile-form (args->env args) body))

(defn compile-define
  [form]
  (let [[name args body] (rest form)]
    {name (list* [(count args) false] (compile-fn args body))}))

(defn compile-toplevel
  [form]
  ((cond
    (= (first form) 'define) compile-define
    :else (constantly {}))
   form))

(defn compile-program
  [program]
  (let [prog (apply merge (map compile-toplevel program))]
    (merge standard-lib prog)))

(defn eval-program
  [program]
  (let [prog (compile-program program)
	main (concat (rest (prog 'main)) '((:unbox)))]
    (run-code main nil prog (atom {}))))

(def samp
     '[(define square [n] (* n n))
       (define main [] (square (+ 1 2)))])

(def samp2
     '[(define fib-loop
	 [n a b]
	 (if (zero? n)
	   b
	   (fib-loop (- n 1) b (+ a b))))
       (define fib
	 [n]
	 (fib-loop n 1 0))
       (define main [] (fib 5000))])

(def samp3
     '[(define integers
	 [n]
	 (cons n (integers (+ n 1))))
       (define nth
	 [coll n]
	 (if (zero? n)
	   (first coll)
	   (nth (rest coll) (- n 1))))
       (define main [] (nth (integers 0) 5000))])

(def samp4
     '[(define map2
	 [f coll1 coll2]
	 (if (nil? coll1)
	   nil
	   (cons (f (first coll1) (first coll2))
		 (map2 f (rest coll1) (rest coll2)))))
        (define nth
	 [coll n]
	 (if (zero? n)
	   (first coll)
	   (nth (rest coll) (- n 1))))
	(define fibs
	  []
	  (cons 0 (cons 1 nil)))
	(define fib2
	  []
	  (map2 + fibs fibs))
	(define main [] (nth fib2 1))])

