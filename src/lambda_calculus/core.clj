(ns lambda-calculus.core
  (:use midje.sweet)
  (:use [clojure.core.match :only (match)]))

(defprotocol LambdaTerm
  (lambda-eval [lambda-term])
  (replace-free-instances [term parameter-name replacer])
  (free-variables [term]))

(defrecord Function [parameter-name body]
  LambdaTerm
  (lambda-eval [t]
    (->Function parameter-name
                (lambda-eval body)))
  (replace-free-instances [function replace-name replacer]
    (if (= replace-name (get function :paremeter-name))
      function
      (->Function parameter-name
                  (replace-free-instances body
                                          replace-name
                                          replacer))))
  (free-variables [function]
    (clojure.set/difference (free-variables body)
                            #{parameter-name}))
  (toString [function]
    (str "(λ" parameter-name "." body ")")))

(defrecord Application [term1 term2]
  LambdaTerm
  (lambda-eval [t]
    (let [term1 (get t :term1)
          term2 (get t :term2)
          evaled1 (lambda-eval term1)
          evaled2 (lambda-eval term2)]
      (if (= (type evaled1) lambda_calculus.core.Function)
        (lambda-eval (replace-free-instances (get evaled1 :body)
                                             (get evaled1 :parameter-name)
                                             evaled2))
        (->Application evaled1 evaled2))))
  (replace-free-instances [app parameter-name replacer]
    (->Application (replace-free-instances (get app :term1) parameter-name replacer)
                   (replace-free-instances (get app :term2) parameter-name replacer)))
  (free-variables [application]
    (clojure.set/union (free-variables term1)
                       (free-variables term2)))
  (toString [term]
    (str "(" term1 " " term2 ")")))

(defrecord Variable [name]
  LambdaTerm
  (lambda-eval [x] x)
  (replace-free-instances [variable parameter-name replacer]
    (if (= (get variable :name)
           parameter-name)
      replacer
      variable))
  (free-variables [variable] #{name})
  (toString [function]
    (str name)))

(defrecord Empty []
  LambdaTerm
  (lambda-eval [x] x)
  (replace-free-instances [x parameter-name replacer] [x])
  (free-variables [empty] #{})
  (toString [empty] ""))

(def app ->Application)
(def fun ->Function)
(def lvar ->Variable)

(def empty-lambda (->Empty))

(def id (fun "x" (lvar "x")))

(fact "identity evaluates to itself"
  (let [term (->Function "x" (->Variable "x")) ]
    (lambda-eval term) => term
    (lambda-eval (->Application term term)) => term))

(def tru (->Function "t" (->Function "f" (->Variable "t"))))
(def fls (->Function "t" (->Function "f" (->Variable "f"))))

(defn singleton? [a-seq]
  (and (not-empty a-seq)
       (empty? (rest a-seq))))

(defn seq->app [terms]
  (if (empty? terms)
    []
    (reduce app terms)))

(facts "seq->app"
  (seq->app []) => []
  (seq->app [(lvar "x")]) => (lvar "x")
  (seq->app [tru tru tru]) => (app (app tru tru) tru))

(def lambda-and
  (fun "x" (fun "y" (seq->app [(lvar "x") (lvar "y") fls]))))

(tabular
  (fact "lambda-and"
    (lambda-eval (seq->app [lambda-and ?bool1 ?bool2])) => ?result)
  ?bool1 ?bool2 ?result
  tru    tru    tru
  tru    fls    fls
  fls    tru    fls
  fls    fls    fls)

(def lambda-0
  (fun "s" (fun "z" (lvar "z"))))

(def lambda-1
  (fun "s" (fun "z" (seq->app [(lvar "s") (lvar "z")]))))

(def lambda-2
  (fun "s" (fun "z" (app (lvar "s") (app (lvar "s") (lvar "z"))))))

(def lambda-3
  (fun "s" (fun "z" (app (lvar "s") (app (lvar "s") (app (lvar "s") (lvar "z")))))))

(def scc
  (fun "n" (fun "s" (fun "z" (app (lvar "s") (seq->app [(lvar "n") (lvar "s") (lvar "z")]))))))

(facts "scc"
  (lambda-eval (app scc lambda-0)) => lambda-1
  (lambda-eval (app scc lambda-1)) => lambda-2
  (lambda-eval (app scc lambda-2)) => lambda-3)

(defn num->church-numeral [n]
  (let [church-body (fn [self n]
                      (if (zero? n)
                        (lvar "z")
                        (app (lvar "s") (self self (- n 1)))))]
  (fun "s" (fun "z" (church-body church-body n)))))

(facts "num->church-numeral"
  (num->church-numeral 0) => lambda-0
  (num->church-numeral 1) => lambda-1
  (num->church-numeral 2) => lambda-2
  (lambda-eval (app scc (num->church-numeral 1))) => lambda-2)

(def plus
  (fun "n" (fun "m" (fun "s" (fun "z" (seq->app [(lvar "n")
                                                 (lvar "s")
                                                 (seq->app [(lvar "m")
                                                            (lvar "s")
                                                            (lvar "z")])]))))))

(facts "plus"
  (doseq [n (range 20)
          m (range 20)]
    (lambda-eval (seq->app [plus (num->church-numeral n)
                                 (num->church-numeral m)])) => (num->church-numeral (+ n m))))
