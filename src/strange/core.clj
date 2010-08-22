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

(defn interactive-eval
  "Evaluate form using the interactive evaluator"
  [form]
  (if (contains? @environment 'eval)
    (force-thunk (s-eval `(~'eval '~form) {}))
    (force-thunk (s-eval form {}))))

(defn eval-program
  "Evaluate a program and return its last value"
  [program]
  (loop [program program, val nil]
    (if (seq program)
      (recur (next program) (interactive-eval (first program)))
      val)))
  
(defn boot-system
  "Boot the system by initializing the environment and loading boot.sng"
  []
  (reset! environment {})
  (let [boot-url (.getResource (clojure.lang.RT/baseLoader) "strange/boot.sng")
	boot-contents (slurp boot-url)
	boot-program (read-string (str "(" boot-contents ")"))]
    (eval-program boot-program)))
  
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
  (boot-system)
  (println "System booted.")
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
