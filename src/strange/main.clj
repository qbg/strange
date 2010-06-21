(ns strange.main
  (:require [strange.core :as core])
  (:gen-class))

(defn -main
  []
  (println "Strange v0.0.1-alpha REPL")
  (println "Enter :quit to quit")
  (core/repl)
  (System/exit 0))
