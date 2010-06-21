(ns strange.main
  (:require [strange.core :as core])
  (:gen-class))

(defn -main
  []
  (println "Strange 0.0.1-alpha")
  (println "Enter :quit to quit")
  (core/repl)
  (System/exit 0))
