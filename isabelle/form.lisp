;;
;;;; intuitionistic equational logic reasoner
;;

(require 'printv)
(require 'alexandria)
(use-package :alexandria)

(defun cat (&rest strings)
  (apply 'concatenate 'string (mapcar 'string strings)))

(defun vflatten (vec)
  (if (simple-vector-p vec)
      (loop :for term across vec
            :appending (vflatten term))
      (list vec)))

(defun vlist (vec)
  (if (simple-vector-p vec)
      (loop :for term across vec
            :collect (vlist term))
      vec))

(defun vsubst (vec test)
  "substitute the result of test for subterms if true. NIL is not a valid term."
  (let (did-sub)
    (labels ((rec (subtree)
               (if-let (new (funcall test subtree)) ; assume new return not nil
                 (setf did-sub new)
                 (if (simple-vector-p subtree)
                     (loop :with copy = (copy-array subtree)
                           :for i below (length subtree)
                           :do (setf (svref copy i) (rec (svref subtree i)))
                           :finally (return copy))
                     subtree))))
      (values (rec vec) did-sub))))

(defun nvsubst (vec test)
  "substitute the result of test for subterms if true. NIL is not a valid term."
  (let (did-sub)
    (labels ((rec (subtree)
               (if-let (new (funcall test subtree)) ; assume new return not nil
                 (setf did-sub new)
                 (progn
                   (when (simple-vector-p subtree)
                     (loop :for i below (length subtree)
                           :do (setf (svref subtree i) (rec (svref subtree i)))))
                   subtree))))
      (values (rec vec) did-sub))))

;;
;;; internal syntax
;;
;; variables: locally-nameless (named binders) de-bruijn
;; untyped for now lol
;; TODO inductive types and case form (scott encoding)

(deftype tvar () '(or string fixnum))
(defun tvar-p (e) (typep e 'tvar))

;; in this setup bound variables are represented as indices
;; note: free variables may appear captured, they will not be printed as indices
(defun tbound (tvar)
  (integerp tvar))

(defstruct (lam (:constructor ld (bind body)))
  (bind (error "") :type tvar)
  (body (error "")))

;; this is bad practice but we're not reading anyways
(defmethod print-object ((lam lam) s)
  (format s "λ~a.~a" (lam-bind lam) (lam-body lam)))

(defstruct (app (:constructor ap (lam1 lam2)))
  (lam1 (error ""))
  (lam2 (error "")))

(defmethod print-object ((ap app) s)
  (format s "~a" (list (app-lam1 ap) (app-lam2 ap))))

(defun named->dbruijn (lam)
  (labels ((rec (env lam)
             (cond ((tvar-p lam)
                    (if-let (cs (assoc lam env :test 'string=)) ; bound
                      (cdr cs)
                      lam))
                   ((lam-p lam)
                    (ld (lam-bind lam)
                        (rec (acons (lam-bind lam)
                                    0
                                    (mapcar (lambda (sn) (cons (car sn) (1+ (cdr sn))))
                                            env))
                             (lam-body lam))))
                   ((app-p lam)
                    (ap (rec env (app-lam1 lam)) (rec env (app-lam2 lam))))
                   (t (error "bad named term ~a" lam)))))
    (rec () lam)))

(defun dbruijn->named (lam)
  (labels ((rec (env lam)
             (cond ((tvar-p lam)
                    (if (tbound lam)
                        (cdr (assoc lam env))
                        lam))
                   ((lam-p lam)
                    (ld (lam-bind lam)
                        (rec (acons 0
                                    (lam-bind lam)
                                    (mapcar (lambda (sn) (cons (1+ (car sn)) (cdr sn)))
                                            env))
                             (lam-body lam))))
                   ((app-p lam)
                    (ap (rec env (app-lam1 lam)) (rec env (app-lam2 lam)))))))
    (rec () lam)))

;; (sub (named->dbruijn (ld "f" (ld "x" (ap "f" "x")))) "x")
(defun sub (f x)
  (labels ((rec (n lam x)
             (cond ((tvar-p lam)
                    (cond ((not (tbound lam)) lam)
                          ((= n lam) x)
                          (t lam)))
                   ((lam-p lam)
                    (ld (lam-bind lam)
                        (rec (1+ n) (lam-body lam) x)))
                   ((app-p lam)
                    (ap (rec n (app-lam1 lam) x) (rec n (app-lam2 lam) x))))))
    (assert (lam-p f))
    (rec 0 (lam-body f) x)))

(defun copy-term (tree)
  (typecase tree
    (simple-vector (map 'simple-vector 'copy-term tree))
    (t tree)))

;;
;;; unification
;;
;; terms are either symbols (constants/schemas) or vectors
;;

(defun schemify (s)
  (gensym (cat "?" s)))

(defun schema-p (sym)
  (and (symbolp sym)
       (let ((ssym (string sym)))
         (and (plusp (length ssym))
              (char= #\? (char ssym 0))))))

(assert (schema-p (schemify "n")))
(assert (not (schema-p (symbolicate "")))) ; 0-length

(defstruct (eqn (:constructor eqn (lh rh)))
  lh
  rh)

(defun deschemify (term)
  (vsubst term (lambda (s) (when (schema-p s)
                        (subseq (string s) 0 2)))))

(defmethod print-object ((e eqn) s)
  (format s "~a = ~a"
          (vlist (deschemify (eqn-lh e)))
          (vlist (deschemify (eqn-rh e)))))

(defun occurs (s term)
  "assumes no binding of s, and returns true on s = term"
  (if (atom term)
      (eq s term)
      (some (lambda (e) (occurs s e)) term)))

(assert (equalp #(1 2) (nvsubst #(1 2) (lambda (e) (if (equal e nil) 42)))))
(assert (equalp #(b b) (nvsubst #(a a) (lambda (e) (if (eq e 'a) 'b)))))

(defun get-subst (subst v)
  (when-let (eqn (find v subst :test 'equal :key 'eqn-lh))
    (eqn-rh eqn)))

;; does not respect binding: only schematic vars substituted
(defun usubst (subst term)
  (nvsubst term (lambda (subtree) (get-subst subst subtree))))

(defun unify (ta tb)
  (let ((subst (list)))
    (labels ((rec (ta tb)
               (when (schema-p ta)
                 (when-let (res (get-subst subst ta))
                   (setf ta res)))
               (when (schema-p tb)
                 (when-let (res (get-subst subst tb))
                   (setf tb res)))
               ;; handles double schema/constant case
               (cond ((and (symbolp ta) (symbolp tb) (eq ta tb)) t)
                     ;; functions symbols necessarily equal by above case
                     ((and (simple-vector-p ta) (simple-vector-p tb)
                           (= (length ta) (length tb)))
                      (loop :for i below (length ta)
                            :do (rec (svref ta i) (svref tb i))))
                     ((schema-p ta)
                      (if (not (occurs ta tb))
                          (push (eqn ta tb) subst)
                          (return-from unify nil)))
                     ((schema-p tb)
                      (if (not (occurs tb ta))
                          (push (eqn tb ta) subst)
                          (return-from unify nil)))
                     (t
                      (return-from unify nil)))))
      (rec ta tb)
      (values subst t))))

(assert (equalp (list (eqn '?F 'f)) (unify #(f x) #(?F x))))
(assert (equalp (list (eqn '?Y '?A) (eqn '?X #(G ?Y)))
                (unify #(f #(g ?y) #(g ?y)) #(f ?x #(g ?a)))))

;; consider DAGs to avoid this exponential duplication,
;; (h (f :x0 :x0) (f :x1 :x1) :y1         :y2         :x2)
;; (h :x1         :x2         (f :y0 :y0) (f :y1 :y1) :y2)
;; tho in practice it doesn't seem to matter



;;
;;; metatheory
;;

(deftype atomic-prop () '(or symbol simple-vector))
(defun atomprop (e) (typep e 'atomic-prop))

;; conjunctions, disjunctions represented as prop sets
(defstruct conj
  (cjs #() :type (simple-array prop)))
(defun conj (&rest cjs)
  (make-conj :cjs (coerce cjs 'simple-vector)))

(defstruct disj
  (djs #() :type (simple-array prop)))
(defun disj (&rest djs)
  (make-disj :djs (coerce djs 'simple-vector)))

(defmethod print-object ((e conj) s)
  (format s "(~{~a ~^∧ ~})"
          (mapcar (lambda (e) (if (atomprop e) (vlist (deschemify e)) e))
                  (coerce (conj-cjs e) 'list))))

(defmethod print-object ((e disj) s)
  (format s "(~{~a ~^∨ ~})"
          (mapcar (lambda (e) (if (atomprop e) (vlist (deschemify e)) e))
                  (coerce (disj-djs e) 'list))))

;; pre => con
(defstruct (imp (:constructor imp (pre con)))
  (pre #() :type prop)
  (con (error "") :type prop))

(defmethod print-object ((e imp) s)
  (let ((pre (imp-pre e))
        (con (imp-con e)))
    (if (atomprop pre)
        (format s "~a => ~a"
                (vlist (deschemify pre))
                (if (atomprop con) (vlist (deschemify con)) con))
        (format s "[~a] => ~a"
                pre
                (if (atomprop con) (vlist (deschemify con)) con)))))

;; bottom needed for negative statements
(defconstant +bot+ '⊥)
(defun pnot (prop) (imp prop +bot+))

;; pred: (symbol args...), only occurs in propositional contexts
;; convert existentials Ex.P(x) to (P(:x) => Q) => Q
(deftype prop () '(or symbol simple-vector #|<- atomic props|# conj disj imp eqn))

;; e.g.
;; (add Z ?m) = ?m
;; (add (S ?n) ?m) = (S (add ?n ?m))

(defstruct (thm (:constructor thm (inf)))
  (inf (error "") :type prop))

(defmethod print-object ((e thm) s)
  (format s "<THM ~a>" (thm-inf e)))



;;
;;; theorem collection
;;
;; assume we have all the theorems needed to prove the goal
;; note: all schematic variables should be unique, otherwise unification gets messy

(defparameter *defbase* (make-hash-table :test 'equal))

(defmacro defeq ((name) a = b)
  (declare (type simple-string name))
  (assert (eq = '=))
  (let* ((schemas (remove-if-not 'keywordp (append (vflatten a) (vflatten b))))
         (gsyms (mapcar 'schemify schemas)))
    (flet ((substkeys (term)
             (loop for s in schemas
                   for g in gsyms
                   do (setf term (nvsubst term (lambda (e) (when (eq e s) g))))
                   finally (return term))))
      (let ((a* (substkeys a))
            (b* (substkeys b)))
        `(setf (gethash ,name *defbase*)
               ,(thm (eqn a* b*)))))))

;; constant definition XXX do not redefine at repl, breaks gensyms
(defeq ("addZ") #(add Z :m)      = :m)
(defeq ("addS") #(add #(S :n) :m) = #(S #(add :n :m)))
(defeq ("gUnit") #(g :a one) = :a)
(defeq ("gAssoc") #(g :a #(g :b :c)) = #(g #(g :a :b) c))

(defun print-theorems ()
  (maphash (lambda (k v) (format t "~a ~s~%" k v)) *defbase*))



;;
;;; search
;;
;; transitive eqs and congruences are equivalent to transport

;; (defun fsearch (lh rh thms)
;;   (loop
;;     :with eqns = (mapcar (lambda (thm) (svref (thm-inf thm) 0)) ; TODO
;;                          (hash-table-values thms))
;;     :with proof = ()
;;     :do (when (second (multiple-value-list (unify lh rh)))
;;           (loop-finish))

;;         (dolist (eqn eqns)
;;           (multiple-value-bind
;;                 (newlh did-sub)
;;               (nvsubst lh
;;                       (lambda (subtree)
;;                         (sleep 0.1)
;;                         (:printv "matching" subtree (eqn-lh eqn))
;;                         (multiple-value-bind (subst stat)
;;                             (unify subtree (eqn-lh eqn))
;;                           (when stat
;;                             (usubst subst (copy-term (eqn-rh eqn)))))))
;;             (when did-sub
;;               (setf lh newlh)
;;               (push (copy-term newlh) proof))))
;;     :finally (return (nreverse proof))))

;; (fsearch #(ADD Z Z) 'Z *defbase*)
;; (fsearch #(ADD #(S Z) :g) #(S :g) *defbase*)
;; (fsearch #(ADD #(S Z) #(S Z)) #(S #(S Z)) *defbase*)



;;; random

;; e.g. defining Even(x) = ?k.x = 2*k, then
;; ?x. Even x becomes
;; (?k.:x = 2*k => Q) => Q
;; (((:x = 2*:k => R) => R) => Q) => Q
;; (((:x = 2*:k => (r = true)) => (r = true)) => (q = true)) => (q = true)
;; solved by e.g.
;; ((:x = 2*:k => R) => R) subgoal by unification q with ass lhs q
;; :x = 2*:k subgoal by ""
;; 0 = 2 * 0 by unifying with 0 = :n * 0

;; (S :n) = (S :m)  =>  :n = :m
;; (S :n) = Z  =>  T=F
;; prove SSZ = SZ  =>  T=F

;; orderings?

;; group left=>right inverse and square: maybe handle assoc/commut/unit/inverse?
;; adding

;; why are types necessary?
;; - case-splitting
;; - sound instantiation

;; to prove: (plus :n Z) = :n
;; induct on n using provided schemas

;; Nat ≡ Z | S Nat
;; cases on Nat can be seen as:
;; !n. Z != S n
;; primitive: initiality/case analysis

;; plus defined by pattern matching
;; plus 0     b = b -- (0)
;; plus (S a) b = S (plus a b) -- (1)
;;
;; proof of n + 0 = n
;; Cases on n
;; 0 + 0 = 0 by def
;;
;; inductive: S a + 0 = S a -rewrite-> (S S a) + 0 = S S(a)
;; solution:
;; (S S a) + 0 = -forwards by (1)-> S (S a + 0) = S S a -rev cong-> Sa + 0 = Sa

;; map m(a->val) = \x -> case (\x -> if x = a then Some val else None) x of
;;                         None -> m x
;;                         Some v -> v

;; neural net evaluation
