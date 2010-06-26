(ns strange.core)

(def environment (atom {}))
(declare s-eval)

(defn- force-thunk
  [thunk]
  (if (delay? thunk)
    (recur @thunk)
    thunk))

(defn- eval-symbol
  [form env]
  (if (contains? env form)
    (env form)
    (if (contains? @environment form)
      (@environment form)
      (throw (Exception. (format "%s is undefined" form))))))

(declare internalize)

(defn- internalize-seq
  [coll]
  (if (seq coll)
    [:cons (internalize (first coll)) (delay (internalize-seq (rest coll)))]
    [:nil]))

(defn- internalize
  [form]
  (if (and (sequential? form) (not (vector? form)))
    (internalize-seq form)
    form))

(defn- eval-quote
  [form env]
  (let [form (second form)]
    (internalize form)))

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

      (and (sequential? pattern) (= 'quote (first pattern)))
      (if (= (second pattern) (force-thunk value))
	asserts)

      (sequential? pattern)
      (let [value (force-thunk value)]
	(if (and (sequential? value) (= (count pattern) (count value)))
	  (if (seq pattern)
	    (recur (next pattern) (next value)
		   (pattern-match (first pattern) (first value) asserts))
	    asserts)))

      :else
      (if (= pattern (force-thunk value))
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

(defn externalize
  [val]
  (let [val (force-thunk val)]
    (cond
     (not (sequential? val)) val
     (= :nil (first val)) nil
     (= :cons (first val))
     (let [[_ f r] val
	   f (externalize (force-thunk f))
	   r (force-thunk r)]
       (lazy-seq
	(cons f (externalize r))))
     :else val)))

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
    (if (seq args)
      [:fn (f 1) env args (f 4)]
      (throw (Exception. (format "Too many arguments applied to %s" (f 1)))))))

(defn- eval-app
  [form env]
  (delay
   (let [[f & args] form
	 f (force-thunk (s-eval f env))
	 args (map #(s-eval % env) args)]
     (when (or (not (vector? f)) (not= (f 0) :fn))
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

(defn- eval-env
  [form env]
  env)

(defn- eval-set!
  [form env]
  (let [[_ name body] form]
    (swap! environment assoc name (s-eval body env))
    name))

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
   (= 'environment (first form)) (eval-env form env)
   (= 'set! (first form)) (eval-set! form env)
   :else (eval-app form env)))

(defn print-defs
  "Print out a list of all of the loaded definitions"
  []
  (println (sort (keys @environment))))

(defn bound-toplevel?
  [sym]
  (contains? @environment sym))

(def stdlib '[

;; Bootstrap the system
(set! toplevel-env (environment))
(set! bound? (fn (sym) (prim strange.core/bound-toplevel? sym)))
(set! symbol? (fn (form) (prim symbol? form)))
(set! cons (fn (x xs) (adt :cons x xs)))
(set! nil (adt :nil))
(set! primitive-form (fn (form) (prim strange.core/externalize form)))
(set! make-fn
      (fn (name env args body)
	(adt :fn
	     (strict name)
	     (strict env)
	     (strict (primitive-form args))
	     (strict (primitive-form body)))))
(set! name-fn
      (fn (name f)
	(case f
	  (:fn _ env args body) (adt :fn name env args body))))
(set! eval-in-env ; Bootstrap version
      (fn (form env)
	((make-fn :anonymous env '() form))))
(set! append
      (fn (xs ys)
	(case xs
	  (:cons x xs) (cons x (append xs ys))
	  (:nil) ys)))
(set! quasiquote
      (fn (form env)
	(case form
	  (:cons 'unquote (:cons u-form (:nil)))
	  (eval-in-env u-form env)

	  (:cons (:cons 'unquote-splice (:cons u-form (:nil))) xs)
	  (append (eval-in-env u-form env) (quasiquote xs env))

	  (:cons x xs)
	  (cons (quasiquote x env) (quasiquote xs env))

	  x
	  x)))
(set! macroexpand-bindings
      (fn (bindings)
	(case bindings
	  (:cons var (:cons val xs))
	  (cons var (cons (macroexpand val) (macroexpand-bindings xs)))

	  (:nil)
	  nil)))
(set! map-macroexpand
      (fn (forms)
	(case forms
	  (:cons form forms) (cons (macroexpand form) (map-macroexpand forms))
	  (:nil) nil)))
(set! macroexpand
      (fn (form)
	(case form
	  (:cons 'quote x)
	  form

	  (:cons 'let (:cons bindings (:cons body (:nil))))
	  (cons 'let (cons (macroexpand-bindings bindings)
			   (cons (macroexpand body) nil)))

	  (:cons 'letrec (:cons bindings (:cons body (:nil))))
	  (cons 'letrec (cons (macroexpand-bindings bindings)
			      (cons (macroexpand body) nil)))

	  (:cons 'case (:cons val bindings))
	  (cons 'case (cons (macroexpand val) (macroexpand-bindings bindings)))

	  (:cons 'fn (:cons params (:cons body (:nil))))
	  (cons 'fn (cons params (cons (macroexpand body) nil)))

	  ;; if, strict, prim, adt, environment, and set! don't need cases

	  (:cons name args)
	  (if (symbol? name)
	    (if (bound? name)
	      (case (eval-in-env name toplevel-env)
		    (:macro expand-f) (macroexpand (expand-f form))
		    x (cons name (map-macroexpand args)))
	      (cons name (map-macroexpand args)))
	    (cons name (map-macroexpand args)))

	  x
	  x)))
(set! def
      (adt :macro
	   (fn (form)
	     (case form
	       (:cons 'def (:cons (:cons name args) (:cons body (:nil))))
	       (quasiquote
		'(set! (unquote name)
		       (name-fn (quote (unquote name))
				(fn (unquote args) (unquote body))))
		(environment))

	       (:cons 'def (:cons name (:cons val (:nil))))
	       (quasiquote '(set! (unquote name) (unquote val))
			   (environment))))))

;; Install the improved eval
(set! eval-in-env
      (fn (form env)
	((make-fn :anonymous env '() (macroexpand form)))))
(set! eval (fn (form) (eval-in-env form toplevel-env)))

;; The standard library
(def (+ x y) (prim + x y))
(def (- x y) (prim - x y))
(def (* x y) (prim * x y))
(def (/ x y) (prim / x y))
(def (= x y) (prim = x y))
(def (defs) (prim strange.core/print-defs))
(def (nil? xs) (case xs (:cons x y) false (:nil) true))
(def (first xs) (case xs (:cons x xs) x (:nil) nil))
(def (rest xs) (case xs (:cons x xs) xs (:nil) nil))
(def (map f xs)
  (case xs
    (:cons x xs)
    (let (x (strict x)) (cons (f x) (map f xs)))
    (:nil) nil))
(def (zip f xs ys)
  (case xs
    (:cons x xs)
    (case ys
      (:cons y ys)
      (let (x (strict x)
	      y (strict y))
	(cons (f x y) (zip f xs ys)))
      (:nil) nil)
    (:nil) nil))
(def (nth xs n)
  (case xs
    (:cons x xs)
    (if (= n 0)
      x
      (nth xs (strict (- n 1))))
    (:nil)
    nil))
(def (iterate f val) (cons val (iterate f (strict (f val)))))
(def integers (iterate (+ 1) 0))
(def (take n xs)
  (if (= n 0)
    nil
    (case xs
      (:cons x xs) (cons x (take (strict (- n 1)) xs))
      (:nil) nil)))
(def (drop n xs)
  (if (= n 0)
    xs
    (case xs
      (:cons x xs) (drop (strict (- n 1)) xs)
      (:nil) nil)))
(def (cycle xs) (letrec (ys (append xs ys)) ys))
(def (foldl f init xs)
  (case xs
    (:cons x xs) (foldl f (strict (f init x)) xs)
    (:nil) init))
(def (foldr f init xs)
  (case xs
    (:cons x xs) (f x (foldr f init xs))
    (:nil) init))

]) ; End of stdlib

(defn interactive-eval
  "Evaluate form using the interactive evaluator"
  [form]
  (if (contains? @environment 'eval)
    (force-thunk (s-eval `(~'eval '~form) {}))
    (force-thunk (s-eval form {}))))

(defn eval-program
  "Evaluate a program and return its last value in a new enviornment"
  [program]
  (reset! environment {})
  (loop [program (concat stdlib program), val nil]
    (if (seq program)
      (recur (next program) (interactive-eval (first program)))
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
  (let [[_ name env args body] val
	arg-str (if (seq args) (str (apply list args)) "()")]
    (print (format "#<Function %s %s>" name arg-str))))

(defn print-val
  "Print a returned value"
  [val]
  (let [val (force-thunk val)]
    (cond
     (map? val) (print "#<Environment>")
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
	  (print-val (interactive-eval form))
	  (println)
	  (catch Exception e (println "Error:" (.getMessage e))))
	(println)
	(recur)))))
