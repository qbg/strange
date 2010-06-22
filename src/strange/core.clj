(ns strange.core)

(def environment (atom {}))
(declare s-eval)

(defn- force-thunk
  [thunk]
  (if (delay? thunk)
    (recur @thunk)
    thunk))

(let [no-val (gensym)]
  (defn- eval-symbol
    [form env]
    (let [val (env form no-val)]
      (if (= val no-val)
	(let [val (@environment form no-val)]
	  (if (= val no-val)
	    (throw (Exception. (format "%s is undefined" form)))
	    val))
	val))))

(defn- convert-seq
  [coll]
  (if (seq coll)
    [:cons (first coll) (delay (convert-seq (rest coll)))]
    [:nil]))

(defn- eval-quote
  [form env]
  (let [form (second form)]
    (if (sequential? form)
      (convert-seq form)
      form)))

(defn- eval-if
  [form env]
  (let [[_ pred t f] form]
    (delay
     (if (force-thunk (s-eval pred env))
       (s-eval t env)
       (s-eval f env)))))

(defn- eval-let
  [form env]
  (let [[_ bindings body] form
	bindings (partition 2 bindings)
	vars (map first bindings)
	vals (map #(s-eval (second %) env) bindings)
	env (merge env (zipmap vars vals))]
    (s-eval body env)))

(defn- eval-letrec
  [form env]
  (let [[_ bindings body] form
	bindings (partition 2 bindings)
	vars (map first bindings)
	new-env (atom {})
	env (merge env (zipmap vars (map #(delay (@new-env %)) vars)))
	vals (map #(s-eval (second %) env) bindings)]
    (reset! new-env (zipmap vars vals))
    (s-eval body env)))

(defn- pattern-match
  ([pattern value]
     (pattern-match pattern value {}))
  ([pattern value asserts]
     (cond
      (nil? asserts) nil
      
      (symbol? pattern)
      (if-let [v (asserts pattern)]
	(if (= v value)
	  asserts)
	(merge asserts {pattern value}))

      (sequential? pattern)
      (if (and (sequential? value) (= (count pattern) (count value)))
	(if (seq pattern)
	  (recur (next pattern) (next value)
		 (pattern-match (first pattern) (first value) asserts))
	  asserts))

      :else
      (if (= pattern value)
	asserts))))
     
(defn- eval-case
  [form env]
  (let [[_ val & cases] form
	val (force-thunk (s-eval val env))
	cases (partition 2 cases)
	match (->>
		 cases
		 (map (fn [[pattern body]]
			[(pattern-match pattern val) body]))
		 (filter #(identity (first %)))
		 first)
	env (merge env (first match))]
    (if match
      (s-eval (second match) env)
      (throw (Exception.
	      (format "Failed to match value of type %s when executing %s"
		      (if (vector? val) (first val) val)
		      form))))))

(defn- eval-fn
  [form env]
  (let [[_ args body] form]
    [:fn :anonymous env args body]))

(defn- externalize
  [val]
  (cond
   (not (sequential? val)) val
   (= :nil (first val)) nil
   (= :cons (first val))
   (let [[_ f r] val
	 f (externalize (force-thunk f))
	 r (force-thunk r)]
     (lazy-seq
      (cons f (externalize r))))))

(defn- eval-prim
  [form env]
  (let [[_ f & args] form
	args (map #(externalize (force-thunk (s-eval % env))) args)]
    (apply (resolve f) args)))

(defn- eval-strict
  [form env]
  (force-thunk (s-eval (second form) env)))

(defn- partial-apply
  [f vals]
  (let [[vars args] (split-at (count vals) (f 3))
	env (merge (f 2) (zipmap vars vals))]
    [:fn (f 1) env args (f 4)]))

(defn- eval-app
  [form env]
  (delay
   (let [[f & args] form
	 f (force-thunk (s-eval f env))
	 args (map #(s-eval % env) args)]
     (if (or (not (vector? f)) (not= (f 0) :fn))
       (throw (Exception.
	       (format "Tried to call a non-function when executing %s"
		       form))))
     (if (= (count (f 3)) (count args))
       (let [env (merge (f 2) (zipmap (f 3) args))]
	 (s-eval (f 4) env))
       (partial-apply f args)))))

(defn- eval-adt
  [form env]
  (let [[_ type & args] form
	args (map #(s-eval % env) args)]
    (apply vector type args)))

(defn- s-eval
  [form env]
  (cond
   (nil? form) (eval-symbol form env)
   (symbol? form) (eval-symbol form env)
   (not (sequential? form)) form
   (= 'quote (first form)) (eval-quote form env)
   (= 'if (first form)) (eval-if form env)
   (= 'let (first form)) (eval-let form env)
   (= 'letrec (first form)) (eval-letrec form env)
   (= 'case (first form)) (eval-case form env)
   (= 'fn (first form)) (eval-fn form env)
   (= 'strict (first form)) (eval-strict form env)
   (= 'prim (first form)) (eval-prim form env)
   (= 'adt (first form)) (eval-adt form env)
   :else (eval-app form env)))

(defn- eval-def
  [form]
  (let [[_ name body] form]
    (swap! environment assoc name (s-eval body {}))
    name))

(defn- eval-defn
  [form]
  (let [[_ name args body] form]
    (swap! environment assoc name [:fn name {} args body])
    name))

(defn toplevel-eval
  "Given a form, evaluate it and return its value"
  [form]
  (cond
   (not (sequential? form)) (force-thunk (s-eval form {}))
   (= 'def (first form)) (eval-def form)
   (= 'defn (first form)) (eval-defn form)
   :else (force-thunk (s-eval form {}))))

(defn print-defs
  "Print out a list of all of the loaded definitions"
  []
  (println (sort (keys @environment))))

(def stdlib
     '((defn + (x y) (prim + x y))
       (defn - (x y) (prim - x y))
       (defn * (x y) (prim * x y))
       (defn / (x y) (prim / x y))
       (defn = (x y) (prim = x y))
       (defn eval (code) (prim strange.core/toplevel-eval code))
       (defn defs () (prim strange.core/print-defs))
       (defn cons (x xs) (adt :cons x xs))
       (def nil (adt :nil))
       (defn nil?
	 (xs)
	 (case xs
	       [:cons x y] false
	       [:nil] true))
       (defn first
	 (xs)
	 (case xs
	       [:cons x xs] x
	       [:nil] nil))
       (defn rest
	 (xs)
	 (case xs
	       [:cons x xs] xs
	       [:nil] nil))
       (defn map
	 (f xs)
	 (case xs
	       [:cons x xs]
	       (let [x (strict x)]
		 (cons (f x) (map f xs)))
	       [:nil] nil))
       (defn map2
	 (f xs ys)
	 (case xs
	       [:cons x xs]
	       (case ys
		     [:cons y ys]
		     (let [x (strict x)
			   y (strict y)]
		       (cons (f x y) (map2 f xs ys)))
		     [:nil] nil)
	       [:nil] nil))
       (defn nth
	 (xs n)
	 (case xs
	       [:cons x xs]
	       (if (= n 0)
		 x
		 (nth xs (strict (- n 1))))
	       [:nil]
	       nil))
       (defn iterate
	 (f val)
	 (cons val (iterate f (strict (f val)))))
       (def integers (iterate (+ 1) 0))
       (defn take
	 (n xs)
	 (if (= n 0)
	   nil
	   (case xs
		 [:cons x xs] (cons x (take (strict (- n 1)) xs))
		 [:nil] nil)))
       (defn append
	 (xs ys)
	 (case xs
	       [:cons x xs] (cons x (append xs ys))
	       [:nil] ys))
       (defn cycle
	 (xs)
	 (letrec [ys (append xs ys)] ys))
       (defn foldl
	 (f init xs)
	 (case xs
	       [:cons x xs]
	       (foldl f (strict (f init x)) xs)
	       [:nil]
	       init))
       (defn foldr
	 (f init xs)
	 (case xs
	       [:cons x xs]
	       (f x (foldr f init xs))
	       [:nil]
	       init))))

(defn eval-program
  "Evaluate a program and return its last value in a new enviornment"
  [program]
  (reset! environment {})
  (loop [program (concat stdlib program), val nil]
    (if (seq program)
      (recur (next program) (toplevel-eval (first program)))
      val)))

(declare print-val)

(defn- print-rest
  [val]
  (cond
   (= :nil (first val)) (print ")")
   :else
   (let [[_ f r] val
	 f (force-thunk f)
	 r (force-thunk r)]
     (print " ")
     (print-val f)
     (recur r))))

(defn- print-list
  [val]
  (let [[_ f r] val
	f (force-thunk f)
	r (force-thunk r)]
    (print "(")
    (print-val f)
    (print-rest r)))

(defn- print-fn
  [val]
  (let [[_ name env args body] val]
    (print (format "#<Function %s %s>" name (apply vector args)))))

(defn print-val
  "Print a returned value"
  [val]
  (let [val (force-thunk val)]
    (cond
     (not (vector? val)) (print val)
     (= :nil (first val)) (print nil)
     (= :cons (first val)) (print-list val)
     (= :fn (first val)) (print-fn val)
     :else (print (format "#<%s>" (first val))))))

(defn- safe-read
  []
  (try
    (read)
    (catch Exception e (do (println (str e)) nil))))

(defn repl
  "Launch a repl"
  []
  (eval-program nil)
  (loop []
    (print "> ")
    (.flush *out*)
    (let [form (safe-read)]
      (when (not (= form :quit)) 
	(try
	  (print-val (toplevel-eval form))
	  (println)
	  (catch Exception e (println (str e))))
	(println)
	(recur)))))
