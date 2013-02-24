(ns prolog.core)

(use 'prolog.unify)
(use 'clojure.set)
(use 'clojure.walk)
(use 'clojure.pprint)
(use 'clojure.tools.trace)


(declare prove prove-all maphash clause-body clause-head get-clauses 
         rename-variables ?- show-prolog-solutions 
         show-prolog-vars top-level-prove continue? add-builtin
         prolog-equals
         prolog-is)


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
  
;  (if (continue?)
;    nil
;    )
  (prove-all other-goals bindings)
  )


(defn prolog-fail [vars bindings other-goals]
  (println "failure")
  nil)


(defn prolog-equals [vars bindings other-goals]
  ;(println (first vars))
  ;(println (subst-bindings bindings (first vars)))
  ;(println (second vars))
  ;(println (subst-bindings bindings (second vars)))
  (let [x (subst-bindings bindings (first vars))
        y (subst-bindings bindings (second vars))]
		;(println "x is" x)
		;(println "y is" y)
    (if (= x y)
      (prove-all other-goals bindings)
      nil)))

(defn prolog-add [vars bindings other-goals]
  ;(println (first vars))
  ;(println (subst-bindings bindings (first vars)))
  ;(println (second vars))
  ;(println (subst-bindings bindings (second vars)))
  (let [x (subst-bindings bindings (first vars))
        y (subst-bindings bindings (second vars))]
		;(println "x is" x)
		;(println "y is" y)
    (if (= x y)
      (prove-all other-goals bindings)
      nil)))



(defn prolog-is [vars bindings other-goals]
  (println "vars are")
  (doall (map #(println %) vars))
  (prove-all other-goals bindings))


(defn prolog-print
  [vars bindings other-goals]
  (println "entering prolog print")
  ;(println (lookup (first vars) bindings))
  (dorun (map #(println (lookup % bindings)) vars))
  ;doall (map #(println (% bindings)) vars))
  ;(println "vars are")
  ;(doall (map #(println %) vars))
  ;(println "bindings are")
  ;(doall (map #(println %) bindings))
  ;(println "other goals are")
  ;(doall (map #(println %) other-goals))
  ;(println "exiting prolog print")
  (prove-all other-goals bindings)
  )




; some helper functions
(defn clause-head [clause] (first clause))
(defn clause-body [clause] (rest clause))
(defn predicate [relation] (first relation))


(def db-predicates (ref {}))


(defn in?
  "true if seq contains elm"  [elm seq]
  (some #(= elm %) seq))


(defn not-in? [elm seq]
  (not (in? elm seq)))


(defn add-clause [clause]
  (let [pred (predicate  (clause-head clause))
        db   (deref db-predicates)]
    (assert (not (variable? pred)))
    (dosync
     (if (not-in?  pred (deref db-predicates))
       (ref-set db-predicates
                (assoc db pred '())))
     (ref-set db-predicates
              (assoc db pred (sean-cons clause (pred db))))) ; second usage of cons
    pred))



(defn maphash
  "maps a function to the value of every key/value in h
   pred should take two args: a key and a value and return a new value"
  [pred h]
  (loop [k (keys h)
         b {}]
    (if (!empty? k)
      (recur (rest k) (assoc b (first k) (pred (first k) (h (first k)))))
      b)))


(defn add-builtin [command expression]
  (let [db (deref db-predicates)]
    (dosync   (ref-set db-predicates
                       (assoc db command (eval (load-string (str "prolog.core/" expression))))))))



(defn clear-db []
  (dosync
   (ref-set db-predicates {}))
  (add-builtin :show-vars 'show-prolog-vars)
  (add-builtin :print 'prolog-print)
  (add-builtin :is 'prolog-is)
  (add-builtin :fail 'prolog-fail)
  (add-builtin := 'prolog-equals)
  (add-builtin :+ 'prolog-add)

  ;(add-builtin 'prolog-equals)
  )


(defn get-clauses [pred]
  "gets a list of clauses from database"
  ((deref db-predicates) pred))


; this is where we do the logic like from 
; http://lib.store.yahoo.net/lib/paulgraham/onlisp.pdf
; remember, prove can call prove-all multiple times
; and prove-all can call prove multiple times
; prove-all can call prove-all 
; prove cannot call prove

; both prove-all and prove can return nil
; only prove-all can return bindings
; prove returns nil if no head clauses can unify with the goal
(defn prove
  "return a list of possible solutions to a goal
  change mapcat to map to see call structure"
  [goal bindings other-goals] ; goal is always one clause in single
                                        ; parenthesis
  ; remember, when you're getting new clauses, your getting new clauses based on the predicate of the goal
  ; so for any () with likes in the front, it's gonna get this from the db:
  ; db-predicates => #<Ref@18598b6: {likes (((likes Sandy ?x) (:or (likes ?x cats) (likes ?x Lee))) ((likes Robin cats))), :show-vars #<core$show_prolog_vars prolog.core$show_prolog_vars@19cb8>}>
  (println (predicate goal))
  (println (get-clauses (predicate goal))
  (let [clauses (get-clauses (predicate goal))] ; referenced only if
                                        ; clauses is a builtin predicate, which means the clauses from the database for something like :show returned something like prolog.core/show-prolog-vars
    ;(println "clauses from pred" clauses)
    (if (consp clauses) ; we call consp clauses because sometimes the clauses variable is a function which we can call to do an operation
      ; like arithmetic or printing to O
      
      ; this is the old version from peter norvig
        
      (some ; why do we call some?? some think that's a very good question
       ; we call some because some returns the first value that is non-nil
       ; we could also just call prove-all on the first head-clause that unifies with goal (first param)
       
       ; actually, the thing is, we have to call prove-all even if the bindings are nil.
       ; why is this?
       
       ;-------------------------
       ;clojure.core/some
       ;([pred coll])
       ;Returns the first logical true value of (pred x) for any x in coll,
       ;else nil.  One common idiom is to use a set as pred, for example
       ;this will return :fred if :fred is in the sequence, otherwise nil:
       ;(some #{:fred} coll)
       ;(some #(if (even? %) %) [1 2 3 4]) => 2
       
       
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
         (let [new-clause (rename-variables clause)] ; each clause is a group of terms in parenthesis
          (prove-all
            ; puts clause body at beginning
            (concat (clause-body new-clause) other-goals) ; goals
            (unify goal (clause-head new-clause) bindings)))) ; this is like only calling prove-all if the goal unifies with the head clause
       																												; unify will return nil if these two clauses don't unify
       																												; and prove-all returns nil if the bindings param is nil
       ; TODO: this would be much simpler if we didn't call prove-all if the bindings param was nil
       
       clauses)

      ;; the predicate's clauses can be an atom:
      ;; a primitive function to be called
      
      (clauses (rest goal) bindings other-goals)
      ))) ; arithmetic


; this is the entry/exit point
; prove-all is called first and it is what returns the bindings
; whenever you see prove-all have nil as the second parameter means that prove wasn't able to unify something
; clauses can unify or not unify based on the bindings variable
; what unified before may not unify later depending on the bindings for the variables.
; this is how we don't go into infinite recursion (usually)
(defn prove-all
  "calls prove on every clause with whatever bindings we've got.
   will return current bindings"
  [goals bindings]
  (cond
   (= bindings nil) nil ; this is the failure code, you can do consp on the return code of prove-all to determine if prove-all failed to unify
   (empty? goals) (list bindings) ; if the return code is a list, then, consp will return true
   true ; to simulate default and statement, just use (prove (first goals) bindings (rest goals)) instead of garbage below
          (let [pred (predicate (first goals))]
            ;(println (= pred :and))
            (cond (= pred :and) ;(prove (first goals) bindings (rest goals))
                  (let [clauses (rest (first goals))]
                    ;(println "and statement reached" clauses)
                    ;(println "clauses was" clauses)
                    ;(println "(first goals) was" (first goals))
                    ;(println "(first clauses) was" (first clauses))
                    ;(println "(rest goals) was" (rest goals))
                    ;(println "(rest clauses) was" (rest clauses))
										;(println "new goal thing is" (into (rest goals) (rest clauses)))
                    ; this worked.
                    ;(prove (first clauses) bindings (into (rest goals) (rest clauses))) ; into puts every element in (rest clauses) into start of list
                    ; but this works better
                    ; process clauses here before you call prove. once you call prove you can't process or, and or not statements anymore
                    (prove-all (into (rest goals) clauses) bindings) ; into puts every element in (rest clauses) into start of list
                    )
                  (= pred :or) ; now for the or statement, we want to do some conditional branching.
                  (let [clauses (rest (first goals))]
                    ;(println "or statement reached" clauses)
                    ;(println "clauses was" clauses)
                    ;(println "(first goals) was" (first goals))
                    ;(println "(rest goals) was" (rest goals))
                    ;(println "(first clauses) was" (first clauses))
                    ;(println "(rest clauses) was" (rest clauses))
										;(println "new goal thing is" (into (rest goals) (list (first clauses))))
                    (loop [clauses (rest (first goals))
                           other-goals (rest goals)]
                      ;(println "clauses is" clauses)
                      ;(println "Other goals is" other-goals)
                      (if (= (count clauses) 0)
                        nil
                      	(if (consp (prove-all (into (rest goals) (list (first clauses))) bindings))
                        	bindings
                        	(recur (rest clauses) other-goals)))
                    ;(prove (first goals) bindings (rest goals))                 
                    ))
                  ; that means calling prove-all on several clauses
                  true (prove (first goals) bindings (rest goals))
                  ))))




(comment
(deftrace prove [goal bindings]
  ;(println "Calling prove from" called-from)
  ;(println "entering prove")
  ;(println "Goals" goal)
  ;(println "Bindings" bindings)
  ;(if (consp (get-clauses (predicate goal))) (println "the clauses are---------------" (clause-head (first (get-clauses (predicate goal))))))
  (let [clauses (get-clauses (predicate goal))] 
    (if (consp clauses) 
  		(some (fn [clause] (let [new-clause (rename-variables clause)]
            (prove-all (clause-body new-clause)
                       (unify goal (clause-head new-clause) bindings))))
        (get-clauses (predicate goal)))
      (clauses (rest goal) bindings))))


; this is the entry point
(deftrace prove-all [goals bindings]
  ;(println "Calling prove-all from" called-from)
  ;(println "Entering prove-all")
  ;(println "Goals" goals)
  ;(println "Bindings" bindings)
  (cond
   (= bindings nil) nil
   (empty? goals) (list bindings)
   true (some (fn [goal1-solution] (prove-all (rest goals) goal1-solution))
              (prove (first goals) bindings))))
)


(defn sean-replace [string & replacements]
 (loop [p replacements
        s string]
   (if (!empty? p)
     (recur
       (-> p rest rest)
       (.replace s (first p) (second p)))
     s)))

(def i (ref 0))
(defn get-next-sym [] 
  (dosync (ref-set i (+ (deref i) 1)))
  (str (deref i)))
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
               (get-next-sym))))
         (variables-in x)))
   x))


(defmacro ?- [& goals]
  `(top-level-prove '~goals))

(defmacro <- [& clause]
  `(add-clause '~clause))





(defn top-level-prove [goals]
  (prove-all `(~@goals (:show-vars ~@(variables-in goals))) {}))


(defn continue?
  "@TODO ask user if we should stop"
  [] true)


(defn prolog-assert
  [vars bindings other-goals]
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
  (?- (likes Sandy ?who))
  (println "done."))


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
  (?- (member a (a b)) (prolog-print true)))


(defn test-lisp []
  (clear-db)
  (<- (eval-all [] []) (eval-all []))
  (?- (eval-all () ()) (prolog-print true)))

(defn -main [& args]
  (println (test-prove)))

