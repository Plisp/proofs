;;
;;;; equational reasoner
;;

(require 'printv)
(require 'alexandria)
(use-package :alexandria)

(defun cat (&rest strings)
  (apply 'concatenate 'string (mapcar 'string strings)))

;;; internal syntax

;; variable: locally-nameless (named binders) de-bruijn
;; application: (Op a a)
;; (ap (ld (add (tvar "v") Z)) Z)
;; case: (rec t (λ (n) suc-term)...)

;; untyped for now lol

(defstruct tvar
  (name "" :type string)
  (i 0 :type integer))
(defun tvar (name &optional (i 0)) (make-tvar :name name :i i))

(defun tbound (tvar)
  (string= "" (tvar-name tvar)))

(defmethod print-object ((v tvar) s)
  (if (not (tbound v))
      (format s "~a" (cat "!" (tvar-name v)))
      (format s "~d" (tvar-i v))))

(defstruct lam
  (bind (error "") :type tvar)
  (body (error "")))
(defun ld (s lam) (make-lam :bind (tvar s) :body lam))

(defmethod print-object ((lam lam) s)
  (format s "~a" (list 'ld (tvar-name (lam-bind lam)) (lam-body lam))))

(defstruct app
  (lam1 (error ""))
  (lam2 (error "")))
(defun ap (lam1 lam2) (make-app :lam1 lam1 :lam2 lam2))

(defmethod print-object ((ap app) s)
  (format s "~a" (list (app-lam1 ap) (app-lam2 ap))))

(defun named->dbruijn (lam)
  (labels ((rec (env lam)
             (cond ((tvar-p lam)
                    (if-let (cs (assoc (tvar-name lam) env :test 'string=)) ; bound
                      (tvar "" (cdr cs))
                      lam))
                   ((lam-p lam)
                    (ld (tvar-name (lam-bind lam))
                        (rec (acons (tvar-name (lam-bind lam))
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
                        (cdr (assoc (tvar-i lam) env))
                        lam))
                   ((lam-p lam)
                    (ld (tvar-name (lam-bind lam))
                        (rec (acons 0
                                    (tvar-name (lam-bind lam))
                                    (mapcar (lambda (sn) (cons (1+ (car sn)) (cdr sn)))
                                            env))
                             (lam-body lam))))
                   ((app-p lam)
                    (ap (rec env (app-lam1 lam)) (rec env (app-lam2 lam)))))))
    (rec () lam)))

(defun sub (f x)
  (labels ((rec (n lam x)
             (cond ((tvar-p lam)
                    (cond ((not (tbound lam)) lam)
                          ((= n (tvar-i lam)) x)
                          (t lam)))
                   ((lam-p lam)
                    (ld (tvar-name (lam-bind lam))
                        (rec (1+ n) (lam-body lam) x)))
                   ((app-p lam)
                    (ap (rec n (app-lam1 lam) x) (rec n (app-lam2 lam) x))))))
    (assert (lam-p f))
    (rec 0 (lam-body f) x)))

;;; external syntax

(defun schemify (s)
  (gensym (cat "?" s)))

(defun schema-p (sym)
  (let ((ssym (string sym)))
    (and (plusp (length ssym))
         (char= #\? (char ssym 0)))))

(assert (schema-p (schemify "n")))
(assert (not (schema-p (symbolicate "")))) ; 0-length

;; equality is external
;; implication?
;; S(:a) = S(:b) ==> :a = :b

;; (defstruct eqn
;;   (lh () :type list)
;;   (rh () :type list))

;; e.g.
;; (add Z ?m) = ?m
;; (add (S ?n) ?m) = (S (add ?n ?m))

(defparameter *defbase* (make-hash-table))

(defmacro defthm ((&optional name) a = b)
  (declare (ignorable name))
  (assert (eq = '=))
  (let* ((schemas (remove-if-not 'keywordp (alexandria:flatten (append a b))))
         (gsyms (mapcar 'schemify schemas)))
    (flet ((substkeys (tm)
             (loop for s in schemas
                   for g in gsyms
                   do (setf tm (subst g s tm))
                   finally (return tm))))
      `(push ',(substkeys b) (gethash ',(substkeys a) *defbase*)))))

(defthm () (add Z :m)      = :m)
(defthm () (add (S :n) :m) = (S (add :n :m)))



;;; unification

(defun unify (la lb)
  "unification does not compute"
  ;; TODO scoped occurs check in schema cases
  (cond ((schema-p la) (values (list `(,la = ,lb)) t))
        ((schema-p lb) (values (list `(,lb = ,la)) t))
        ;; constants
        ((and (symbolp la) (symbolp lb))
         (if (eq la lb)
             (values () t)
             (values () nil)))
        ((and (listp la) (listp lb))
         (if (eq (car la) (car lb))
             (loop with res = ()
                   for a in la
                   for b in lb
                   do (multiple-value-bind (subst stat)
                          (unify a b)
                        ;; TODO need to apply subst
                        (if stat
                            (and subst (appendf res subst))
                            (return (values () nil))))
                   finally (return (values res t)))
             (values () nil)))
        (t
         (:printv "failed to unify" la lb)
         (values () nil))))



;;; search

;; TODO respect binding
(defun dosubsts (term substs)
  (loop for s in substs
        do (setf term (subst (third s) (first s) term))
        finally (return term)))

(defun show (lh rh &optional (eqs *defbase*))
  ;; TODO compute
  (if (equal lh rh)
      (list 'id)
      (loop for eqn in (hash-table-keys eqs)
            do (:printv "trying" lh eqn)
               ;; TODO try unifying eqn at deeper levels
               (multiple-value-bind (substs stat)
                   (unify lh eqn)
                 (when stat
                   (let* ((eqn-rhs (first (gethash eqn eqs)))
                          (newlhs (dosubsts eqn-rhs substs)))
                     (:printv "rewritten to" newlhs)
                     (when-let (a (show newlhs rh))
                       (return (append `(,eqn = ,eqn-rhs) a)))))))))

;; neural net/nondeterministic search

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
;; (S S a) + 0 = -forwards by (1)-> S (S a + 0) = S S a

;; map m(a->val) = \x -> case (\x -> if x = a then Some val else None) x of
;;                         None -> m x
;;                         Some v -> v
