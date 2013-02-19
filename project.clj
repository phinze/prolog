(defproject prolog "1.0.0-SNAPSHOT"
  :description "FIXME: write description"
  :dependencies [[org.clojure/clojure "1.4.0"]
                 [org.clojure/core.unify "0.5.5"]
                 [org.clojure/tools.trace "0.7.5"]                 
                 ]
  ;:repl-options [:init nil :caught clj-stacktrace.repl/pst+]
  ;:dev-dependencies [[swank-clojure "1.4.0"]]
  :main prolog.core
  )

