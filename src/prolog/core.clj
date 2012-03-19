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
   (coll? x) true
   (type? x clojure.lang.Cons) true
   true false))


(defn cdr [x]jj
  (if (type? x clojure.lang.PersistentVector)
    (cond
     (= (count x) 0) nil
     (= (count x) 1) nil
     (= (count x) 2) (first (rest x))
     true (vec (rest x)))
    (if (empty? x)
      nil
      (rest x))))


; expects predicates & number of both arguments to be the same
(defn unify [x y bindings]
  (cond
   (nil? bindings) nil ; an assertion to prevent the prover from
                       ; putting in nil bindings. don't know why it
                       ; does this sometimes.
   (= x y) bindings ; the closing statement. the function ends at this line
   (variable? x) (unify-variables x y bindings)
   (variable? y) (unify-variables y x bindings)
   (and
    (consp x)
    (consp y)) (unify (cdr x) (cdr y)
                      (unify (first x) (first y) bindings))
   true nil)) ; function will fail if it reaches this point


(defn unify-variables [v x bindings] ; v is var name, x is value
  (cond
                                        ; called from variable? lines
                                        ; in unify
   (v bindings) (unify (v bindings) x bindings)
   (and
    (variable? x)
    (x bindings)) (unify v (x bindings) bindings)
   (occurs-check v x bindings) nil
   true (assoc bindings v x)))


(defn occurs-check [var x bindings]
  "if "
  (cond (= var x) true
        (and
          (variable? x)
          (x bindings)) (occurs-check var (x bindings) bindings)
        (consp x) (or
                    (occurs-check var (first x) bindings)
                    (occurs-check var (cdr x) bindings))
        true nil))


(defmacro xor
  "Evaluates exprs one at a time, from left to right.  If only one form returns
  a logical true value (neither nil nor false), returns true.  If more than one
  value returns logical true or no value returns logical true, retuns a logical
  false value.  As soon as two logically true forms are encountered, no
  remaining expression is evaluated.  (xor) returns nil."
  ([] nil)
  ([f & r]
     `(loop [t# false f# '[~f ~@r]]
        (if-not (seq f#) t#
                (let [fv# (eval (first f#))]
                  (cond
                   (and t# fv#) false
                   (and (not t#) fv#) (recur true (rest f#))
                   :else (recur t# (rest f#))))))))


(defn blank? [x]
  (or
   (nil? x)
   (and
    (coll? x)
    (empty? x))))


(defn !blank? [x]
  (not (blank? x)))


(defn sean-cons [x y]
  (cond
   (and
    (blank? y)
    (!blank? x)) (list x)
   (not (consp y))
   (cons x (list y))
   true (cons x y)))


(defn subst-bindings [bindings x]
  ;(assert (not (nil? x)))
  (cond
   (= bindings nil) nil
   (= bindings {}) x
   (and
     (variable? x)
     (x bindings)) (subst-bindings bindings (x bindings))
   (not (consp x)) x
   true (sean-cons
         (subst-bindings bindings (first x))
         (subst-bindings bindings (cdr x)))))


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
   (ref-set *db-predicates* (maphash (fn [x y] nil) (deref *db-predicates*))))
  (add-builtin 'prolog.core/show-prolog-vars)
  (add-builtin 'prolog.core/prolog-print))


(defn get-clauses [pred]
  "gets a list of clauses from database"
  (pred (deref *db-predicates*)))


(defn prove
  "return a list of possible solutions to a goal
  change mapcat to map to see call structure"
  [goal bindings other-goals] ; goal is always one clause in single
                                        ; parenthesis
  (let [clauses (get-clauses (predicate goal))] ; referenced only if
                                        ; clauses is a builtin predicate
    (if (consp clauses)
      (some
       (fn [clause] ; for every single clause from get-clauses, attempt
                                        ; to unify with head clause
                                        ; if it unifies, prove will be
                                        ; called again with the next
                                        ; clause of in line of
                                        ; whatever was unified
                                        ; so if you have 2 rules of 2
                                        ; and 3 clauses, prove will
                                        ; attempt to unify with the
                                        ; head clause of both and if
                                        ; they unify, it will set the
                                        ; goal to the next clause and
                                        ; attempt to unify with that
                                        ; and so on.
                                        ; it will also attempt to
                                        ; cross unify because the goal
                                        ; clause even if it's unified
                                        ; with the head clause of
                                        ; another clause, can still be
                                        ; unified with the head clause
                                        ; of yet another clause
         (let [new-clause (rename-variables clause)]
           (prove-all
            (concat (clause-body new-clause) other-goals) ; puts
                                        ; clause body at beginning
            (unify goal (clause-head new-clause)  bindings))))
       (get-clauses (predicate goal))) ; gets clauses from db

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
  (prove-all `(~@goals (show-prolog-vars ~@(variables-in goals))) {}))


(defn show-prolog-solutions
  "Print the variables in each of the solutions"
  [vars solutions]
  (if (nil? solutions)
    (cl-format true "~&No\n")
    (map #(show-prolog-vars vars %) solutions)))


(defn continue?
  "@TODO ask user if we should stop"
  [] true)


(comment
   (doall (map #(cl-format true "~&~a = ~a\n" % (subst-bindings bindings %)) vars)))


(defn show-prolog-vars
  "Print each variable with its binding"
  [vars bindings other-goals]
  ;(println bindings)
  (if (nil? vars)
    (cl-format true "~&Yes")
    (loop [vars vars
           v (first vars)]
      (if (not (nil? v))
        (cl-format true "~&~a = ~a\n" v (subst-bindings bindings v)))
      (if (not (nil? v))
        (recur
         (rest vars)
         (first (rest  vars))))))
  (if (continue?)
    nil
    (prove-all other-goals bindings)))


(defn add-builtin [command]
  (let [db (deref *db-predicates*)]
    (dosync   (ref-set *db-predicates*
                       (assoc db command (eval  command))))))


(defn prolog-print
  [vars bindings other-goals]
  (doall (map #(println %) vars))
  (prove-all other-goals bindings))


;(deftrace prove-all [a b] (prove-all a b))
;(deftrace prove [a b c] (prove a b c))
(clear-db)

(defn test-prove []
  (clear-db)
  (<- (likes Kim Robin))
  (<- (likes Sandy Lee))
  (<- (likes Sandy Kim))
  (<- (likes Robin cats))
  (<- (likes Sandy ?x) (likes ?x cats))
  (<- (likes Kim ?x) (likes ?x Lee) (likes ?x Kim))
  (<- (likes ?x ?x))
  (?- (likes Sandy ?who)))


(defn test-append []
  (clear-db)
  (<- (append [] ?xs ?xs))
  (<- (append [?x ?xs] ?ys [?x ?zs])
      (append ?xs ?ys ?zs))
  (?- (append ?x (c d) (a b c d))))


(defn test-member []
  (clear-db)
  (<- (member ?x [?x ?rest]))
  (<- (member ?x [? ?rest]) (member ?x ?rest))
  (?- (member a (a b)) (prolog.core/prolog-print true)))


(defn test-lisp []
  (clear-db)
  (<- (eval-all [] []) (eval-all []))
  (?- (eval-all () ()) (prolog.core/prolog-print true)))
