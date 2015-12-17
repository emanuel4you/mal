(ns core
  (:require [readline]
            [printer]))

;; Errors/exceptions
(defn mal_throw [obj]
  (throw (ex-info "mal exception" {:data obj})))

;; Metadata functions
;; - store metadata at :meta key of the real metadata
(defn mal_with_meta [obj m]
  (let [new-meta (assoc (meta obj) :meta m)]
    (with-meta obj new-meta)))

(defn mal_meta [obj]
  (:meta (meta obj)))

; Strings and printing functions
(defn pr-helper [coll sep readable?]
  (clojure.string/join sep (map #(printer/mal-pr-str % readable?) coll)))

(defn mal_pr_str [& args]
  (pr-helper args " " true))

(defn mal_str [& args]
  (pr-helper args "" false))

(defn mal_prn [& args]
  (println (pr-helper args " " true)))

(defn mal_println [& args]
  (println (pr-helper args " " false)))

;; core_ns is core namespaces functions
(def core_ns
  [['= =]
   ['throw mal_throw]
   ['nil? nil?]
   ['true? true?]
   ['false? false?]
   ['symbol symbol]
   ['symbol? symbol?]
   ['keyword keyword]
   ['keyword? keyword?]

   ['pr-str mal_pr_str]
   ['str mal_str]
   ['prn mal_prn]
   ['println mal_println]
   ['readline readline/readline]
   ['read-string reader/read-string]
   ['slurp slurp]
   ['< <]
   ['<= <=]
   ['> >]
   ['>= >=]
   ['+ +]
   ['- -]
   ['* *]
   ['/ /]
   ['time-ms (fn time-ms [] (System/currentTimeMillis))]
  
   ['list list]
   ['list? seq?]
   ['vector vector]
   ['vector? vector?]
   ['hash-map hash-map]
   ['map? map?]
   ['assoc assoc]
   ['dissoc dissoc]
   ['get get]
   ['contains? contains?]
   ['keys (fn [hm] (let [ks (keys hm)] (if (nil? ks) '() ks)))]
   ['vals (fn [hm] (let [vs (vals hm)] (if (nil? vs) '() vs)))]
   
   ['sequential? sequential?]
   ['cons cons]
   ['concat concat]
   ['nth nth]
   ['first first]
   ['rest rest]
   ['empty? empty?]
   ['count count]
   ['apply apply]
   ['map #(doall (map %1 %2))] 

   ['conj conj]

   ['with-meta mal_with_meta]
   ['meta mal_meta]
   ['atom atom]
   ['atom? (fn atom? [atm] (= (type atm) clojure.lang.Atom))]
   ['deref deref]
   ['reset! reset!]
   ['swap! swap!]])
