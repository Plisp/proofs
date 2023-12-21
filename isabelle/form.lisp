;;
;;;; intuitionistic equational logic reasoner
;;

(require 'printv)
(require 'alexandria)
(use-package :alexandria)

(defun cat (&rest strings)
  (apply 'concatenate 'string (mapcar 'string strings)))


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

(defun schema-p (s) (keywordp s))

;; constant definition, same repr as constructors
(defthm ("addZ") (add Z :m)      = :m)
(defthm ("addS") (add (S :n) :m) = (S (add :n :m)))

(defun print-theorems ()
  (maphash (lambda (k v) (format t "~a ~s~%" k v)) *defbase*))



;;
;;; unification
;;
;; terms are either symbols (constants/schemas) or lists
;; schematic unification handles both theorem instantiation and free vars
;;

(defun occurs (s term)
  ;; schematic variables cannot be bound
  (if (symbolp term)
      (eq s term)
      (some (lambda (e) (occurs s e)) term)))

;; does not respect binding: only schematic vars substituted
(defun usubst (s term)
  (nsubst (eqn-rh s) (eqn-lh s) term))

(defun usubsts (substs term)
  (loop :for s in substs
        :do (setf term (usubst s term))
        :finally (return term)))

(defun do-usubsts (substs l)
  (mapcar (lambda (e) (usubsts substs e)) l))

(defun unify (la lb)
  (cond ((and (symbolp la) (symbolp lb)
              (eq la lb))
         ;; handles both eq constants and eq schemas, occurs can ignore these
         (values () t))

        ((schema-p la)
         (if (not (occurs la lb))
             (values (list (eqn la lb)) t)
             (values () nil)))
        ((schema-p lb)
         (if (not (occurs lb la))
             (values (list (eqn lb la)) t)
             (values () nil)))

        ((and (listp la) (listp lb))
         (if (eq (car la) (car lb))
             ;; assume lengths equal
             (loop :with res = ()
                   :for a = (cdr la) then (cdr a)
                   :for b = (cdr lb) then (cdr b)
                   :while a
                   :do (multiple-value-bind (substs stat)
                           (unify (car a) (car b))
                         (if stat
                             (progn
                               (appendf res substs)
                               (setf (cdr a) (do-usubsts substs (cdr a))
                                     (cdr b) (do-usubsts substs (cdr b))))
                             (return (values () nil))))
                   :finally (return (values res t)))
             ;; no higher order unification
             (values () nil)))
        (t
         (values () nil))))

(assert (equalp (list (eqn :X '(G :Y)) (eqn :Y :A))
                (unify '(f (g :y) (g :y)) '(f :x (g :a)))))

;; consider DAGs to avoid this exponential duplication,
;; tho in practice it doesn't seem to matter
;; (unify '(h (f :x0 :x0) (f :x1 :x1) :y1         :y2         :x2)
;;        '(h :x1         :x2         (f :y0 :y0) (f :y1 :y1) :y2))



;;
;;; search
;;
;; trans and congruency are automatic
;; TODO symmetry

(defun map-subterms (f parent)
  "f should return the replacement subterm"
  (flet ((try-match (parent)
           (when-let (replace (funcall f (car parent)))
             (setf (car parent) replace)
             (return-from map-subterms t))))

    (try-match parent)
    ;; then try children
    (let ((term (car parent)))
      (unless (symbolp term)
        (mapl (lambda (ptr) (and (map-subterms f ptr) (return-from map-subterms t)))
              (cdr term))
        nil))))

(defun fsearch (lh rh thms)
  (loop ;; TODO handle assumptions svref
        :initially (setf lh (list lh) rh (list rh))
        :with eqns = (mapcar (lambda (thm) (svref (thm-inf thm) 0))
                             (hash-table-values thms))
        :with proof = (copy-tree lh)
        :do (dolist (eqn eqns)
              (when (map-subterms
                     (lambda (llh)
                       (:printv "matching" llh (eqn-lh eqn))
                       (multiple-value-bind (substs stat)
                           (unify llh (copy-tree (eqn-lh eqn)))
                         (when stat
                           (usubsts substs (copy-tree (eqn-rh eqn))))))
                     lh)
                ;; found rewrite
                (appendf proof `(= ,@(car (copy-tree lh))))
                (when (equal lh rh)
                  (return-from fsearch proof))))))

;; (fsearch '(ADD Z Z) 'Z *defbase*)
;; (fsearch '(ADD (S Z) (S Z)) '(S (S Z)) *defbase*)



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
