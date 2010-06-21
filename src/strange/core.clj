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

(defn unify
  ([pattern value]
     (unify pattern value {}))
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
		 (unify (first pattern) (first value) asserts))
	  asserts))

      :else
      (if (= pattern value)
	asserts))))
     
(defn eval-case
  [form env]
  (let [[_ val & cases] form
	val (force-thunk (s-eval val env))
	cases (partition 2 cases)
	match (first (filter #(unify (first %) val) cases))
	env (merge env (unify (first match) val))]
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

(defn eval-program
  [program]
  (reset! environment {})
  (loop [program program, val nil]
    (if (seq program)
      (recur (next program) (toplevel-eval (first program)))
      val)))

(def samp
     '((defn + [x y] (prim +' x y))
       (defn - [x y] (prim -' x y))
       (defn * [x y] (prim *' x y))
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
	       [:cons x xs] (cons (f x (strict (first ys)))
				  (map2 f xs (strict (rest ys))))))
       (defn nth
	 [xs n]
	 (if (= n 0)
	   (strict (first xs))
	   (nth (strict (rest xs)) (strict (- n 1)))))
       (defn iterate
	 [f val]
	 (cons val (iterate f (strict (f val)))))
       (def integers (iterate (+ 1) 0))
       
       (defn square [x] (* x x))
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

       (nth fibs-2 5000)))
