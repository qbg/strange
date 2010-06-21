(ns strange.core)

(def environment (atom {}))
(declare s-eval)

(defn force-thunk
  [thunk]
  (if (delay? thunk)
    (recur @thunk)
    thunk))

(defn eval-symbol
  [form env]
  (env form (@environment form)))

(defn eval-if
  [form env]
  (let [[_ pred t f] form]
    (delay
     (if (force-thunk (s-eval pred env))
       (s-eval t env)
       (s-eval f env)))))

(defn eval-let
  [form env]
  (let [[_ bindings body] form
	bindings (partition 2 bindings)
	vars (map first bindings)
	vals (map #(s-eval (second %) env) bindings)
	env (merge env (zipmap vars vals))]
    (s-eval body env)))

(defn pattern-match
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
     
(defn eval-case
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
    (s-eval (second match) env)))

(defn eval-fn
  [form env]
  (let [[_ args body] form]
    {:env env :args args :body body}))

(defn eval-prim
  [form env]
  (let [[_ f & args] form
	args (map #(force-thunk (s-eval % env)) args)]
    (apply (resolve f) args)))

(defn eval-strict
  [form env]
  (force-thunk (s-eval (second form) env)))

(defn partial-apply
  [f vals]
  (let [[vars args] (split-at (count vals) (:args f))
	env (merge (:env f) (zipmap vars vals))]
    (assoc f :args args :env env)))

(defn eval-app
  [form env]
  (delay
   (let [[f & args] form
	 f (force-thunk (s-eval f env))
	 args (map #(s-eval % env) args)]
     (if (= (count (:args f)) (count args))
       (let [env (merge (:env f) (zipmap (:args f) args))]
	 (s-eval (:body f) env))
       (partial-apply f args)))))

(defn eval-adt
  [form env]
  (let [[_ type & args] form
	args (map #(s-eval % env) args)]
    (apply vector type args)))

(defn s-eval
  [form env]
  (cond
   (nil? form) (eval-symbol form env)
   (symbol? form) (eval-symbol form env)
   (not (sequential? form)) form
   (= 'quote (first form)) (second form)
   (= 'if (first form)) (eval-if form env)
   (= 'let (first form)) (eval-let form env)
   (= 'case (first form)) (eval-case form env)
   (= 'fn (first form)) (eval-fn form env)
   (= 'strict (first form)) (eval-strict form env)
   (= 'prim (first form)) (eval-prim form env)
   (= 'adt (first form)) (eval-adt form env)
   :else (eval-app form env)))

(defn eval-def
  [form]
  (let [[_ name body] form]
    (swap! environment assoc name (s-eval body {}))
    name))

(defn eval-defn
  [form]
  (let [[_ name args body] form]
    (swap! environment assoc name {:env {} :args args :body body})
    name))

(defn toplevel-eval
  [form]
  (cond
   (not (sequential? form)) (force-thunk (s-eval form {}))
   (= 'def (first form)) (eval-def form)
   (= 'defn (first form)) (eval-defn form)
   :else (force-thunk (s-eval form {}))))

(def stdlib
     '((defn + [x y] (prim + x y))
       (defn - [x y] (prim - x y))
       (defn * [x y] (prim * x y))
       (defn / [x y] (prim / x y))
       (defn = [x y] (prim = x y))
       (defn cons [x xs] (adt :cons x xs))
       (def nil (adt :nil))
       (defn first
	 [xs]
	 (case xs
	       [:cons x xs] x
	       [:nil] nil))
       (defn rest
	 [xs]
	 (case xs
	       [:cons x xs] xs
	       [:nil] nil))
       (defn map
	 [f xs]
	 (case xs
	       [:cons x xs] (cons (f x) (map f xs))
	       [:nil] nil))
       (defn map2
	 [f xs ys]
	 (case xs
	       [:cons x xs]
	       (case ys
		     [:cons y ys] (cons (f x y) (map2 f xs ys))
		     [:nil] nil)
	       [:nil] nil))
       (defn nth
	 [xs n]
	 (case xs
	       [:cons x xs]
	       (if (= n 0)
		 x
		 (nth xs (strict (- n 1))))
	       [:nil]
	       nil))
       (defn iterate
	 [f val]
	 (cons val (iterate f (strict (f val)))))
       (def integers (iterate (+ 1) 0))
       (defn take
	 [n xs]
	 (if (= n 0)
	   nil
	   (case xs
		 [:cons x xs] (cons x (take (strict (- n 1)) xs))
		 [:nil] nil)))))

(defn eval-program
  [program]
  (reset! environment {})
  (loop [program (concat stdlib program), val nil]
    (if (seq program)
      (recur (next program) (toplevel-eval (first program)))
      val)))

(declare print-val)

(defn print-rest
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

(defn print-list
  [val]
  (cond
   (= :nil (first val)) (print "()")
   (= :cons (first val))
   (let [[_ f r] val
	 f (force-thunk f)
	 r (force-thunk r)]
     (print "(")
     (print-val f)
     (print-rest r))))

(defn print-val
  [val]
  (let [val (force-thunk val)]
    (cond
     (not (vector? val)) (print val)
     (= :nil (first val)) (print ())
     (= :cons (first val)) (print-list val)
     :else (print (format "#<ADT %s>" (first val))))))

(defn repl
  []
  (eval-program nil)
  (loop []
    (print "> ")
    (.flush *out*)
    (let [form (read)]
      (when (not (= form :quit))
	(print-val (toplevel-eval form))
	(println)
	(println)
	(recur)))))

(def samp
     '((defn square [x] (* x x))
       (def prog-1 (square (+ 1 2)))

       (defn fib-loop
	 [n a b]
	 (if (= n 0)
	   b
	   (fib-loop (strict (- n 1))
		     b
		     (strict (+ a b)))))
       (defn fib [n] (fib-loop n 1 0))

       (def fibs (cons 0 (cons 1 (map2 + fibs (rest fibs)))))
       (def fibs-2 (map fib integers))
       (def doubles (map2 + integers integers))

       (nth doubles 5)))
