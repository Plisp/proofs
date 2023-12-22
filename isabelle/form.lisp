;;
;;;; intuitionistic equational logic reasoner
;;

(require 'printv)
(require 'alexandria)
(use-package :alexandria)

(defun cat (&rest strings)
  (apply 'concatenate 'string (mapcar 'string strings)))

(defun veltsubst (vec test)
  "substitute the result of test for subterms if true. NIL is not a valid term."
  (labels ((rec (subtree)
             (if-let (new (funcall test subtree))
               new
               (progn
                 (when (simple-vector-p subtree)
                   (loop :for i below (length subtree)
                         :do (setf (svref subtree i) (rec (svref subtree i)))))
                 subtree))))
    (rec vec)))

;;
;;; internal syntax
;;
;; variables: locally-nameless (named binders) de-bruijn
;; untyped for now lol
;; TODO inductive types and case form

(deftype tvar () '(or string fixnum))
(defun tvar-p (e) (typep e 'tvar))

;; in this setup bound variables are represented as indices
;; note: free variables may appear captured, they will not be printed as indices
(defun tbound (tvar)
  (integerp tvar))

(defstruct lam
  (bind (error "") :type tvar)
  (body (error "")))
(defun ld (s lam) (make-lam :bind s :body lam))

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

(defun schema-p (s) (keywordp s))

(defun copy-term (tree)
  (typecase tree
    (simple-vector (map 'simple-vector 'copy-term tree))
    (t tree)))

;;
;;; unification
;;
;; terms are either symbols (constants/schemas) or lists
;; schematic unification handles both theorem instantiation and free vars
;;

(defun occurs (s term)
  ;; schematic variables cannot be bound
  (if (atom term)
      (eq s term)
      (some (lambda (e) (occurs s e)) term)))

(assert (equalp #(1 2) (veltsubst #(1 2) (lambda (e) (if (equal e nil) 42)))))
(assert (equalp #(b b) (veltsubst #(a a) (lambda (e) (if (eq e 'a) 'b)))))

;; does not respect binding: only schematic vars substituted
(defun usubsts (substs term)
  (veltsubst term
             (lambda (subtree)
               (when-let (eqn (find subtree substs :test 'equal :key 'eqn-lh))
                 (eqn-rh eqn)))))

(defun map-usubsts (substs v start)
  (loop :for i from start below (length v)
        :do (setf (svref v i) (usubsts substs (svref v i)))))

(defun unify (ta tb)
  (cond ((and (symbolp ta) (symbolp tb)
              (eq ta tb))
         ;; handles both eq constants and eq schemas, occurs can ignore these
         (values () t))
        ((schema-p ta)
         (if (not (occurs ta tb))
             (values (list (eqn ta tb)) t)
             (values () nil)))
        ((schema-p tb)
         (if (not (occurs tb ta))
             (values (list (eqn tb ta)) t)
             (values () nil)))
        ;; inductive
        ((and (simple-vector-p ta) (simple-vector-p tb)
              (= (length ta) (length tb)))
         (loop :with res = ()
               :for i below (length ta)
               :do (multiple-value-bind (substs stat)
                       (unify (svref ta i) (svref tb i))
                     (if stat
                         (progn
                           (nconcf res substs)
                           (map-usubsts substs ta (1+ i))
                           (map-usubsts substs tb (1+ i)))
                         (return (values () nil))))
               :finally (return (values res t))))
        (t
         (values () nil))))

(assert (equalp (list (eqn :X #(G :Y)) (eqn :Y :A))
                (unify '#(f #(g :y) #(g :y)) '#(f :x #(g :a)))))

;; consider DAGs to avoid this exponential duplication,
;; (h (f :x0 :x0) (f :x1 :x1) :y1         :y2         :x2)
;; (h :x1         :x2         (f :y0 :y0) (f :y1 :y1) :y2)
;; tho in practice it doesn't seem to matter



;;
;;; non-theory
;;

(defstruct (eqn (:constructor eqn (lh rh)))
  lh
  rh)

(defmethod print-object ((e eqn) s)
  (format s "~s = ~s" (eqn-lh e) (eqn-rh e)))
(defmethod make-load-form ((e eqn) &optional env)
  (make-load-form-saving-slots e :environment env))

;; e.g.
;; (add Z ?m) = ?m
;; (add (S ?n) ?m) = (S (add ?n ?m))

(defstruct (thm (:constructor thm (req inf)))
  ;; conjunctions of eqns and atomic facts
  ;; TODO does disjunction need a separate repr
  (req (error "") :type simple-vector)
  (inf (error "") :type simple-vector))

(defmethod print-object ((e thm) s)
  (format s "<THM: [~{~s~^,~}] => [~{~s~^,~}]>"
          (coerce (thm-req e) 'list)
          (coerce (thm-inf e) 'list)))

(defmethod make-load-form ((e thm) &optional env)
  (make-load-form-saving-slots e :environment env))



;;; theorem collection
(defparameter *defbase* (make-hash-table :test 'equal))

(defmacro defthm ((name) a = b)
  (declare (type string name))
  (assert (eq = '=))
  `(setf (gethash ,name *defbase*) ,(thm #() (vector (eqn a b)))))

;; constant definition, same repr as constructors
(defthm ("addZ") #(add Z :m)      = :m)
(defthm ("addS") #(add #(S :n) :m) = #(S #(add :n :m)))

(defun print-theorems ()
  (maphash (lambda (k v) (format t "~a ~s~%" k v)) *defbase*))



;;
;;; search
;;
;; trans and congruency are automatic
;; TODO symmetry

(defun fsearch (lh rh thms)
  (loop
    :with eqns = (mapcar (lambda (thm) (svref (thm-inf thm) 0)) ;; TODO
                         (hash-table-values thms))
    :with proof = ()
    :do (dolist (eqn eqns)
          (when-let (newlh
                     (veltsubst
                      lh
                      (lambda (subtree)
                        ;; (sleep 0.5)
                        ;; (:printv "matching" subtree (eqn-lh eqn))
                        (multiple-value-bind (substs stat)
                            (unify subtree (copy-term (eqn-lh eqn)))
                          (when stat
                            (usubsts substs (copy-term (eqn-rh eqn))))))))
            (setf lh newlh)
            (nconcf proof `(= ,(copy-term newlh)))
            (when (second (multiple-value-list (unify newlh rh)))
              (return-from fsearch proof))))))

;; (fsearch #(ADD Z Z) 'Z *defbase*)
;; (fsearch #(ADD #(S Z) :g) #(S :g) *defbase*)
;; (fsearch #(ADD #(S Z) #(S Z)) #(S #(S Z)) *defbase*)



;;; random

;; group left=>right inverse and square: maybe handle assoc/commut/unit/inverse?

;; why are types necessary?
;; - case-splitting
;; - sound instantiation

;; what measure? bigger is bad unless unfolding allows a reduction step
;; specific measure per rewrite?

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
