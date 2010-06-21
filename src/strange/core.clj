(ns strange.core)

(def *data-stack* (atom nil))
(def *work-stack* (atom nil))
(def *environment* (atom {}))

(defn eval-node
  "Evaluate node, and any node it returns, and so on until nil is returned"
  [node]
  (reset! *data-stack* nil)
  (reset! *work-stack* (list node))
  (loop [node node]
    (if node
      (if (fn? @node)
	(recur (@node))
	;; We are returing a cached value
	(do
	  (swap! *data-stack* conj @node)
	  (swap! *work-stack* next)
	  (recur (first @*work-stack*))))
      (first @*data-stack*))))

(defmacro make-node
  "Create a node that will evalute the body"
  [body]
  `(atom (fn [] ~body)))

(defn make-return-node
  "Create a node that returns a value"
  [val]
  (atom (fn []
	  (swap! *data-stack* conj val)
	  (reset! (first @*work-stack*) val)
	  (swap! *work-stack* next)
	  (first @*work-stack*))))

(defn node?
  "Return true if n is a node"
  [n]
  (instance? clojure.lang.Atom n))

(defn make-clojure-node
  "Create a node that executes a given closure"
  [f & thunks]
  (atom (fn []
	  (reset! (first @*work-stack*)
		  (fn []
		    (let [[vs data] (split-at (count thunks) @*data-stack*)
			  val (apply f (reverse vs))]
		      (if (node? val)
			(do
			  (reset! *data-stack* data)
			  val)
			(let [data (conj data val)]
			  (reset! *data-stack* data)
			  (reset! (first @*work-stack*) val)
			  (swap! *work-stack* next)
			  (first @*work-stack*))))))
	  (reset! *work-stack* (concat thunks @*work-stack*))
	  (first thunks))))

(defn make-case-node
  [case-thunk switches]
  (atom (fn []
	  (reset! (first @*work-stack*)
		  (fn []
		    (let [[obj & data] @*data-stack*
			  obj (if (vector? obj) obj [obj])
			  [tag & vals] obj]
		      (reset! *data-stack* data)
		      (cond
		       (contains? switches tag) (apply (switches tag) vals)
		       :else ((switches :default) obj)))))
	  (swap! *work-stack* conj case-thunk)
	  case-thunk)))

(defn curry
  "Given f and n, the desired number of additional arguments to f, and some
number of given arguments, return a function that will accumulate the additional
arguments and then return a node"
  [f n & given-args]
  (fn [& args]
    (if (= (count args) n)
      (atom #(apply f (concat given-args args)))
      (apply curry f (- n (count args)) (concat given-args args)))))

(defn plain-curry
  [f n]
  (fn [& args]
    (if (= (count args) n)
      (atom #(apply f args))
      (apply curry f (- n (count args)) args))))

(defn env-value
  "Return a value from the global environment"
  [sym]
  (@*environment* sym))

(declare compile-form)

(defn compile-lit
  [env lit]
  `(make-return-node '~lit))

(defn local-var?
  [env sym]
  (contains? (:locals env) sym))

(defn compile-symbol
  [env sym]
  (if (local-var? env sym)
    sym
    (let [n ((:args env {}) sym)]
      (if (= n 0)
	`(env-value '~sym)
	`(plain-curry (env-value '~sym) ~n)))))

(defn compile-quote
  [env form]
  (compile-lit env (second form)))

(defn compile-app
  [env form]
  (let [body
	(if (= ((:args env {}) (first form)) (count (rest form)))
	  `(make-node ((env-value '~(first form))
		       ~@(map #(compile-form env %) (rest form))))
	  (map #(compile-form env %) form))]
    body))

(defn compile-strict
  [env form]
  (let [[_ bindings body] form
	vt-pairs (partition 2 bindings)
	vars (map first vt-pairs)
	thunks (map second vt-pairs)]
    `(make-clojure-node
      (fn [~@vars]
	~body)
      ~@(map #(compile-form env %) thunks))))

(defn compile-case
  [env form]
  (let [[_ case & pairs] form
	pairs (partition 2 pairs)
	maps (map (fn [[[tag & args] body]]
		    {`(quote ~tag)
		     `(fn [~@args]
			~(compile-form
			  (assoc env
			    :locals (into (:locals env) args))
			  body))})
		  pairs)
	switch (apply merge maps)]
    `(make-case-node
      ~(compile-form env case)
      ~switch)))

(defn compile-pcons
  [env form]
  (let [[_ tag & args] form]
    `(make-return-node ['~tag
			~@(map #(compile-form env %) args)])))

(defn compile-form
  [env form]
  ((cond
    (symbol? form) compile-symbol
    (nil? form) compile-symbol
    (not (seq? form)) compile-lit
    (= 'quote (first form)) compile-quote
    (= 'strict (first form)) compile-strict
    (= 'case (first form)) compile-case
    (= 'pcons (first form)) compile-pcons
    :else compile-app)
   env form))

(defn compile-define
  [env form]
  (let [name (second form)
	comp
	(if (vector? (nth form 2))
	  (let [[_ _ [& args] body] form]
	    `(fn [~@args]
	       ~(compile-form
		 (assoc env :locals (set args))
		 body)))
	  (let [[_ _ body] form]
	    (compile-form env body)))]
    {name (eval comp)}))

(defn compile-toplevel
  [env form]
  ((cond
    (= 'define (first form)) compile-define
    :else (constantly {}))
   env form))

(defn gather-define
  [env form]
  (let [args (if (vector? (nth form 2)) (count (nth form 2)) 0)]
    (update-in env [:args] assoc (nth form 1) args)))

(defn gather-form
  [env form]
  ((cond
    (= 'define (first form)) gather-define
    :else (constantly env))
   env form))

(defn gather-global-env
  [program]
  (reduce gather-form {} program))

(defn merge-envs
  [env1 env2]
  {:args (merge (:args env1 {}) (:args env2 {}))
   :locals (:locals env2 #{})})

(defn compile-standalone
  [env program]
  (let [env (merge-envs env (gather-global-env program))]
    [(apply merge (map #(compile-toplevel env %) program))
     env]))

(def stdlib
     (compile-standalone
      {}
      '((define nil (pcons nil))
	(define cons [x xs] (pcons cons x xs))
	(define + [x y] (strict [x x, y y] (+ x y)))
	(define - [x y] (strict [x x, y y] (- x y)))
	(define * [x y] (strict [x x, y y] (* x y)))
	(define / [x y] (strict [x x, y y] (/ x y)))
	(define if [pred t f] (strict [pred pred] (if pred t f)))
	(define = [x y] (strict [x x, y y] (= x y)))
	(define nth
	 [coll n]
	 (case coll
	       [nil]
	       nil
	       
	       [cons x xs]
	       (if (= n 0)
		 x
		 (nth xs (- n 1)))))
	(define first
	  [coll]
	  (case coll [nil] nil [cons x xs] x))
	(define rest
	  [coll]
	  (case coll [nil] nil [cons x xs] xs)))))	

(defn compile-program
  [program]
  (merge (first stdlib)
	 (first (compile-standalone (second stdlib) program))))

(defn run-program
  [cprogram]
  (reset! *environment* cprogram)
  (let [main (cprogram 'main)]
    (eval-node main)))

(defn eval-program
  [program]
  (run-program (compile-program program)))

(def samp
     '((define main (square (+ 1 2)))
       (define square [n] (* n n))))

(def samp2
     '((define main (fibs 5000))
       (define fibs [n] (fibs-loop n 1 0))
       (define fibs-loop
	 [n a b]
	 (if (= 0 n)
	   b
	   (fibs-loop (- n 1) b (+ a b))))))

(def samp3
     '((define integers
	 [n]
	 (cons n (integers (+ n 1))))
       (define main (nth (integers 0) 5000))))

(def samp4
     '((define map2
	 [f coll1 coll2]
	 (case coll1
	       [cons x xs]
	       (case coll2
		     [cons y ys]
		     (cons (f x y) (map2 f xs ys)))))
       (define fibs
	 (cons 0 (cons 1 (map2 + fibs (rest fibs)))))
       (define main (nth fibs 5000))))

(def samp5
     '((define integers
	 [n]
	 (cons n (integers (+ n 1))))
       (define map
	 [f coll]
	 (case coll
	       [nil]
	       nil

	       [cons x xs]
	       (cons (f x) (map f xs))))
       (define fib-loop
	 [a b n]
	 (if (= n 0)
	   b
	   (fib-loop b (+ a b) (- n 1))))
       (define fibs
	 (map (fib-loop 1 0) (integers 0)))
       (define main (nth fibs 5000))))
