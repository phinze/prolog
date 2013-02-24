(ns prolog.unify)

(declare consp variable? variables-in unique-find-anywhere-if unify-variables get-binding get-val lookup occurs-check)


(defn != [x y]
  (not (= x y)))


(defn !empty? [x] (not (empty? x)))

(defn type? [x t]
  (= (type x) t))

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

; there is a difference between consp & blank
;(consp 4) => false
;(consp '()) => false
;(consp '[]) => false
;(consp []) => false
;(consp (list)) => false
;(consp '(4)) => true
;(consp '[4]) => true
;(consp (sean-cons 4 5)) => true

;(blank? 4) => false
;(blank? '()) => true
;(blank? '[]) => true
;(blank? '(4)) => false
;(blank? '[4]) => false
(defn blank? [x]
  (or
   (nil? x)
   (and
    (coll? x)
    (empty? x))))


(defn !blank? [x]
  (not (blank? x)))

; clojure cons vs conj
; http://stackoverflow.com/a/3009747/761726
; only used by subst-bindings
(defn sean-cons [x y]
  (cond
   (and
    (blank? y) ; if y is nil or empty '() or '[]
    (!blank? x)) ; and x is the opposite (an atom)
   		(list x) ; return x by itself
   (not (consp y)) (list x y) ; this is the same as (list x y), was (cons x (list y)) before
   true (cons x y))) ; first usage of cons



; notes to myself about types in clojure.
;(type (cons 4 '())) => clojure.lang.Cons
;(type '()) => clojure.lang.PersistentList$EmptyList
;(type '(1)) => clojure.lang.PersistentList
;(type '[]) => clojure.lang.PersistentVector
;(type '[1]) => clojure.lang.PersistentVector
;(type (list)) => clojure.lang.PersistentList$EmptyList
;(type (cons 4 [])) => clojure.lang.Cons


; consp is to replace coll?
; coll? doesn't return false if something is an empty list or nil. I wanted that distinction
;(coll? '()) => true
;(coll? '[]) => true
;(coll? (cons 4 '())) => true
;(coll? (cons 4 '[])) => true
;(coll? (sean-cons 4 5)) => true
(defn consp [x]
  (cond
   (= x '()) false ; do we ever have the empty list instead of nil?
   (coll? x) true ; this makes sense.
   ;(type? x clojure.lang.Cons) true ; hopefully we don't need this line.. put it back in if necessary
   true false ; if you pass anything else other than a list, it's definitely not a list
   ))


; cdr returns the same thing for both [] lists & () lists & leaves the type intact
;(cdr '[]) => nil
;(cdr '()) => nil
;(cdr '[1]) => nil
;(cdr '(1)) => ()
;(cdr '[1 2]) => 2
;(cdr '(1 2)) => (2)
;(cdr '[1 2 3]) => [2 3]
;(cdr '(1 2 3)) => (2 3)
; it's a replacement for rest which does undesired behavior:
;(rest '[]) => ()
;(rest '()) => ()
;(rest '[1]) => ()
;(rest '(1)) => ()
;(rest '[1 2]) => (2)
;(rest '(1 2)) => (2)
;(rest '[1 2 3]) => (2 3)
;(rest '(1 2 3)) => (2 3)
(defn cdr [x]
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
; see defs on here to figure out these functions
;https://github.com/sneilan/clj-prolog/blob/master/src/clj_prolog/unify.clj 
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

; todo more docs but, this won't be focus of talk
(defn unify-variables [v x bindings] ; v is var name, x is value
  (cond
                                        ; called from variable? lines
                                        ; in unify
   (get-binding v bindings) (unify (lookup v bindings) x bindings)
   (and
    (variable? x)
    (get-binding x bindings)) (unify v (lookup x bindings) bindings)
   (occurs-check v x bindings) nil
   ; don't worry about the  (and *occurs-check* (occurs-check var x bindings)) fail, thing
   true (assoc bindings v x)))

; todo more docs
(defn occurs-check [var x bindings]
  (cond (= var x) true
        (and
          (variable? x)
          (get-binding x bindings)) (occurs-check var (lookup x bindings) bindings)
        (consp x) (or
                    (occurs-check var (first x) bindings)
                    (occurs-check var (cdr x) bindings))
        true nil))




; https://github.com/sneilan/clj-prolog/blob/master/src/clj_prolog/unify.clj
; don't need these. you can just go (x bindings).
(defn get-binding
  "Find a (var value) pair in the binding list"
  [var bindings]
  (first (filter #(= (first %) var) bindings)))


(defn binding-val [binding]
  "Given a binding pair, return the value"
  (second binding))


(defn lookup [var bindings]
  "Get the value part (for var) from a binding list"
  (binding-val (get-binding var bindings)))


(defn subst-bindings [bindings x]
  ;(assert (not (nil? x)))
  (cond
   (= bindings nil) nil
   (= bindings {}) x
   (and
     (variable? x)
     (x bindings)) (subst-bindings bindings (x bindings))
   (not (consp x)) x
   true (sean-cons ; only usage of sean-cons
         (subst-bindings bindings (first x))
         (subst-bindings bindings (cdr x)))))


(defn match-variable [v input bindings] ; v is the var name
  (let [binding (v bindings)]
    (cond
     (not binding) (assoc bindings v input)
     (= input binding) bindings
     true nil)))

