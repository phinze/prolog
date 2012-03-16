(ns prolog.core)
(use 'clojure.set)
(use 'clojure.walk)
(use 'clojure.pprint)
(use 'clojure.tools.trace)


(declare unify unify-variables occurs-check reuse-cons subst-bindings consp unifier prove prove-all maphash clause-body clause-head get-clauses rename-variables variables-in unique-find-anywhere-if ?- show-prolog-solutions show-prolog-vars top-level-prove variable? continue?)


(defn != [x y]
  (not (= x y)))


(defn type? [x t]
  (= (type x) t))


(defn consp [x]
  (cond
   (= x '()) false
   (list? x) true
   (type? x clojure.lang.Cons) true
   true false))


; expects predicates & number of both arguments to be the same
(defn unify [x y bindings]
  (cond
   (nil? bindings) nil
   (= x y) bindings
   (variable? x) (unify-variables x y bindings)
   (variable? y) (unify-variables y x bindings)
   (and
    (consp x)
    (consp y)) (unify (rest x) (rest y)
                      (unify (first x) (first y) bindings))
    true nil))


(defn unify-variables [v x bindings] ; v is var name, x is value
  (cond
    (v bindings) (unify (v bindings) x bindings)
    (and
      (variable? x)
      (x bindings)) (unify v (x bindings) bindings)
    (occurs-check v x bindings) nil
    true (assoc bindings v x)))


(defn occurs-check [var x bindings]
  (cond (= var x) true
        (and
          (variable? x)
          (x bindings)) (occurs-check var (x bindings) bindings)
        (consp x) (or
                    (occurs-check var (first x) bindings)
                    (occurs-check var (rest x) bindings))
        true nil))


(defn reuse-cons [x y x-y]
  (if
      (and
       (= x (first x-y))
       (= y (rest x-y)))
    x-y
    (cons x y)))


(defn subst-bindings [bindings x]
  (cond
   (= bindings nil) nil
   (= bindings {}) x
   (and
     (variable? x)
     (x bindings)) (subst-bindings bindings (x bindings))
   (not (consp x)) x
   true (and
         (reuse-cons
          (subst-bindings bindings (first x))
          (subst-bindings bindings (rest x))
          x))))


(defn unifier [x y]
  (subst-bindings (unify x y {}) x))


(defn match-variable [v input bindings] ; v is the var name
  (let [binding (v bindings)]
    (cond
     (not binding) (assoc bindings v input)
     (= input binding) bindings
     true nil)))


; some helper functions
(defn clause-head [clause] (first clause))
(defn clause-body [clause] (rest clause))
(defn predicate [relation] (first relation))


(def *db-predicates* (ref {}))




(defn in?
  "true if seq contains elm"  [elm seq]
  (some #(= elm %) seq))


(defn not-in? [elm seq]
  (not (in? elm seq)))


(defn add-clause [clause]
  (let [pred (predicate  (clause-head clause))
        db   (deref *db-predicates*)]
    (assert (not (variable? pred)))
    (dosync
     (if (not-in?  pred (deref *db-predicates*))
       (ref-set *db-predicates*
                (assoc db pred '())))
     (ref-set *db-predicates*
              (assoc db pred (cons clause (pred db)))))
    pred))


(defn not-empty? [x] (not (empty? x)))


(defn maphash
  "maps a function to the value of every key/value in h
   pred should take two args: a key and a value and return a new value"
  [pred h]
  (loop [k (keys h)
         b {}]
    (if (not-empty k)
      (recur (rest k) (assoc b (first k) (pred (first k) (h (first k)))))
      b)))


(defn clear-db []
  (dosync
   (ref-set *db-predicates* (maphash (fn [x y] nil) (deref *db-predicates*)))))


(defn get-clauses [pred]
  "gets a list of clauses from database"
  (pred (deref *db-predicates*)))


(defn prove
  "return a list of possible solutions to a goal
  change mapcat to map to see call structure"
  [goal bindings other-goals] ; goal is always one clause in single
                                        ; parenthesis
  (let [clauses (get-clauses (predicate goal))]
    (if (consp clauses)
      (some
       (fn [clause]
         (let [new-clause (rename-variables clause)]
           (prove-all
            (concat (clause-body new-clause) other-goals)
            (unify goal (clause-head new-clause)  bindings))))
       (get-clauses (predicate goal)))

      ;; the predicate's clauses can be an atom:
      ;; a primitive function to be called
      (clauses (rest goal) bindings other-goals))))


(defn prove-all
  "calls prove on every clause with whatever bindings we've got.
   will return current bindings"
  [goals bindings]
  (cond
   (= bindings nil) nil
   (empty? goals) (list bindings)
   true (prove (first goals) bindings (rest goals))))


(defn sean-replace [string & replacements]
 (loop [p replacements
        s string]
   (if (not-empty p)
     (recur
       (-> p rest rest)
       (.replace s (first p) (second p)))
     s)))

(defn rename-variables
  "replace all variables in x with new ones"
  [x]
  (postwalk-replace
   (zipmap
    (variables-in x)
    (map (fn [x]
           (symbol
            (str
             "?"
             (sean-replace (str x) "?" "")
             (gensym))))
         (variables-in x)))
   x))


(defn variable? [x]
  (if
      (and
       (symbol? x)
       (!= (.indexOf (str x) "?") -1))
    true nil))


(defn variables-in
  "return a list of all the variables in expression"
  [exp]
  (unique-find-anywhere-if #'variable? exp))


(defn unique-find-anywhere-if
  "return a list of leaves of tree satisfying predicate
  with duplicates removed
  found-so-far needs to be by default a null set (set '())"
  [predicate tree]
  (filter
   predicate
   (set
    (filter #(!= % 'quote) (flatten tree)))))


(defmacro ?- [& goals]
  `(prove-all '~goals {}))


(defmacro ?- [& goals]
  `(top-level-prove '~goals))

(defmacro <- [& clause]
  `(add-clause '~clause))


(defn top-level-prove [goals]
  (prove-all `(~@goals (show-prolog-vars ~(variables-in goals))) {})
  (cl-format true "~&No."))


(defn show-prolog-solutions
  "Print the variables in each of the solutions"
  [vars solutions]
  (if (nil? solutions)
    (cl-format true "~&No\n")
    (map #(show-prolog-vars vars %) solutions)))


(defn continue?
  "@TODO ask user if we should stop"
  [] false)


(defn show-prolog-vars
  "Print each variable with its binding"
  [vars bindings other-goals]
  (if (nil? vars)
    (cl-format true "~&Yes")
    (map #(cl-format true "~&~a = ~a\n" % (subst-bindings bindings %)) vars))
  (if (continue?)
    nil
    (prove-all other-goals bindings)))


(defn add-builtin [command]
  (let [db (deref *db-predicates*)]
    (dosync   (ref-set *db-predicates*
                       (assoc db command (eval  command))))))


(comment
  (deftrace prove [a b c] (prove a b c))
  (deftrace prove-all [a b] (prove-all a b))
  )


(defn test-prove []
  (clear-db)
  (add-builtin 'show-prolog-vars)
  (<- (likes Kim Robin))
  (<- (likes Sandy Lee))
  (<- (likes Sandy Kim))
  (<- (likes Robin cats))
  (<- (likes Sandy ?x) (likes ?x cats))
  (<- (likes Kim ?x) (likes ?x Lee) (likes ?x Kim))
  (<- (likes ?x ?x))
  (?- (likes Sandy ?who)))
