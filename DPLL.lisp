;; Copyright (C) 2016, University of British Columbia
;; Written by Mark Greenstreet and Yan Peng, UBC, 2016/11/03
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software

(in-package "SMT")
(include-book "../smtlink/top" :ttags :all)

(include-book "std/util/define" :dir :system)
(include-book "misc/eval" :dir :system) ; Define must-succeed and must-fail macros.
(include-book "tools/bstar" :dir :system)
(include-book "ihs/ihs-init" :dir :system) ; for disable-theory and enable-theory
(include-book "centaur/fty/top" :dir :system) ; for defalist, etc.

(deftheory before-arith (current-theory :here))
(include-book "arithmetic-5/top" :dir :system)
(deftheory after-arith (current-theory :here))
(deftheory arithmetic-book-only (set-difference-theories (theory 'after-arith) (theory 'before-arith)))

(defttag :tshell)
(value-triple (tshell-ensure))
(set-state-ok t)

(set-evisc-tuple (evisc-tuple 100 200 nil nil) :iprint :same :sites :all)

(local
 (defun my-smtlink-expt-config ()
   (declare (xargs :guard t))
   (make-smtlink-config :interface-dir "/Users/penny/Work/fun/theorem_proving/smtlink/z3_interface"
                        :SMT-files-dir "z3\_files"
                        :SMT-module    "RewriteExpt"
                        :SMT-class     "to_smt_w_expt"
                        :SMT-cmd       "python"
                        :file-format   ".py")))

(make-event
 (list 'defconst '*wrld-fn-len*
       (b* ((world (w state)))
         (len (remove-duplicates-eq
               (strip-cadrs (universal-theory :here)))))))

(defun my-smtlink-hint-1 ()
  (declare (xargs :guard t :guard-debug t))
  (change-smtlink-hint
   *default-smtlink-hint*
   :functions (list (make-func :name 'expt
                               :formals (list (make-decl :name 'r
                                                         :type (make-hint-pair :thm 'rationalp :hints nil))
                                              (make-decl :name 'i
                                                         :type (make-hint-pair :thm 'rationalp :hints nil)))
                               :returns (list (make-decl :name 'ex
                                                         :type (make-hint-pair :thm 'rationalp :hints nil)))
                               :body 'nil
                               :expansion-depth 0
                               :uninterpreted t))
   :int-to-rat t
   :rm-file nil
   :smt-hint nil
   :smt-cnf (my-smtlink-expt-config)
   :wrld-fn-len *wrld-fn-len*))

(defattach smt-hint my-smtlink-hint-1)

(add-default-hints '((SMT::SMT-hint-wrapper-hint clause)))

;;; some functions and bounds on parameters that we use throughout the proof
(defconst *g1-min* (/ 65536))	  ; g1 is the size of a 'step' in c, the control capacitance
(defconst *g1-max* (/ 8))         ;   Note: c is implicit in the model below with c = nc*g1
;   where nc is the digital control setting for c.

(defconst *g2* (- (/ 1/3200 5)))  ; g2 is the size of a 'step' in v, the control voltage

(defconst *Kt-min* (/ 2))         ; Kt is the 'time-gain' of the loop.  Kt=1 would be perfect
(defconst *Kt-max* (/ 9 10))      ;   time gain -- the old phase error completely cancelled
;   at the next cycle of fref

(defconst *v-min* 0)		  ; minimum value for the control voltage
(defconst *v-max* 3)		  ; maximum value for the control voltage

(defconst *ccode* 1)		  ; The target value for c.
(defconst *N-freq* 1)             ; the frequency multiplication factor of the DPLL.
(defconst *fref* 1)

(defconst *alpha* 1)		  ; *alpha* and *beta* are gain terms in the DCO model
(defconst *beta* 1)		  ; I (mrg) suspect these can be absorbed into other model parameters.
(defconst *f0* 1)



(define dpll-var-p (x)
  :guard t
  :returns (p booleanp)
  :enabled t
  (and x (symbolp x) (not (keywordp x))))
(define dpll-var-fix ((x dpll-var-p))
  :returns (v dpll-var-p)
  :enabled t
  (mbe :logic (if (dpll-var-p x) x 'dpll-var-bogus)
       :exec x))
(define dpll-var-equiv ((x dpll-var-p) (y dpll-var-p))
  :returns (eqv booleanp)
  :enabled t
  (mbe :logic (eql (dpll-var-fix x) (dpll-var-fix y))
       :exec  (eql x y)))
(defequiv dpll-var-equiv)
(fty::deffixtype dpll-var
                 :pred   dpll-var-p
                 :fix    dpll-var-fix
                 :equiv  dpll-var-equiv)
(fty::deflist dpll-var-list
              :elt-type dpll-var-p
              :true-listp t)

(define dpll-sym-p (x)
  :guard t
  :returns (p booleanp)
  :enabled t
  (and x (symbolp x)))
(define dpll-sym-fix ((x dpll-sym-p))
  :returns (v dpll-sym-p)
  :enabled t
  (mbe :logic (if (dpll-sym-p x) x 'dpll-sym-bogus)
       :exec x))
(define dpll-sym-equiv ((x dpll-sym-p) (y dpll-sym-p))
  :returns (eqv booleanp)
  :enabled t
  (mbe :logic (eql (dpll-sym-fix x) (dpll-sym-fix y))
       :exec  (eql x y)))
(defequiv dpll-sym-equiv)
(fty::deffixtype dpll-sym
                 :pred   dpll-sym-p
                 :fix    dpll-sym-fix
                 :equiv  dpll-sym-equiv)
(fty::deflist dpll-sym-list
              :elt-type dpll-sym-p
              :true-listp t)

(define dpll-hyps-arglist-p (x)
  :guard t
  :returns (b booleanp)
  :enabled t
  (and (dpll-sym-list-p x)
       (or (endp x) (keywordp (car x)))))
(define dpll-hyps-arglist-fix ((x dpll-hyps-arglist-p))
  :returns (v dpll-hyps-arglist-p)
  :enabled t
  (mbe :logic (if (dpll-hyps-arglist-p x) x nil)
       :exec x))
(define dpll-hyps-arglist-equiv ((x dpll-hyps-arglist-p) (y dpll-hyps-arglist-p))
  :returns (eqv booleanp)
  :enabled t
  (b* ((xx (dpll-hyps-arglist-fix x))
       (yy (dpll-hyps-arglist-fix y)))
    (equal xx yy)))
(defequiv dpll-hyps-arglist-equiv)
(fty::deffixtype dpll-hyps-arglist
                 :pred   dpll-hyps-arglist-p
                 :fix    dpll-hyps-arglist-fix
                 :equiv  dpll-hyps-arglist-equiv)

(define kw-fix ((x keywordp))
  :returns (k keywordp)
  :enabled t
  (mbe :logic (if (keywordp x) x :kw-bogus)
       :exec x))
(define kw-equiv ((x keywordp) (y keywordp))
  :returns (eqv booleanp)
  :enabled t
  (mbe :logic (eql (kw-fix x) (kw-fix y))
       :exec  (eql x y)))
(defequiv kw-equiv)
(fty::deffixtype keyword
                 :pred  keywordp
                 :fix   kw-fix
                 :equiv kw-equiv)

(fty::defalist dpll-hyps-alist
               :pred dpll-hyps-alist-p
               :key-type keywordp
               :val-type dpll-var-list-p
               :true-listp t)

(define dpll-make-hyps-alist-help ((foo dpll-sym-list-p))
  :returns (mv (v dpll-var-list-p :hyp :guard) (h dpll-hyps-alist-p :hyp :guard))
  (b* (((if (endp foo)) (mv nil foo))
       ((mv v h) (dpll-make-hyps-alist-help (cdr foo)))
       (x (cons (car foo) v))
       ((if (keywordp (car foo))) (mv nil (cons x h))))
    (mv x h)))

;; dpll-make-hyps-alist requires its argument to be a dpll-hyps-arglist-p.
;;   In this case, the v part of the return from dpll-make-hyps-alist-help
;;   shoudld be nil; in other words, there shouldn't be any variables that
;;   haven't been associated with a keyword.  The next theorem proves that
;;   this is indeed the case.
(defthm dpll-make-hyps-alist-help.v=nil-when-dpll-hyps-arglist-p-of-foo
  (implies (dpll-hyps-arglist-p foo)
           (b* (((mv ?v ?h) (dpll-make-hyps-alist-help foo)))
             (not v)))
  :hints(("Goal" :in-theory (enable dpll-make-hyps-alist-help))))

(define dpll-make-hyps-alist ((foo dpll-hyps-arglist-p))
  :returns (h dpll-hyps-alist-p :hyp :guard)
  (b* (((mv ?v ?h) (dpll-make-hyps-alist-help foo))) h))

;; TODO: need to check def. of dv-bound: do *alpha* and *beta* need to be swapped?
;; TODO: fix hardcoding of g1 for :nc
(define dpll-hyps-hyps ((key keywordp) (vars dpll-var-list-p))
  (b* (((if (endp vars)) nil)
       (var (car vars))
       (dv-bound '(/ (* *alpha* g1) (* 4 *beta* ))))
    (append (case key
              (:g1 `((rationalp ,var) (< *g1-min* ,var) (< ,var *g1-max*)))
              (:Kt `((rationalp ,var) (< *Kt-min* ,var) (< ,var *Kt-max*)))
              (:v0 `((rationalp ,var) (< *v-min*  ,var) (< ,var *v-max*)))
              (:dv `((rationalp ,var) (< (- ,dv-bound) ,var) (< ,var ,dv-bound)))
              (:nc `((integerp ,var) (nc-ok ,var)))
              (:nnc `((integerp ,var) (nc-ok (- ,var))))
              (:int `((integerp ,var)))
              (:nat `((integerp ,var) (<= 0 ,var)))
              (:pos `((integerp ,var) (<= 1 ,var)))
              (:rat `((rationalp ,var)))
              (otherwise '(dpll-hyps-bad-key key)))
            (dpll-hyps-hyps key (cdr vars)))))

(define dpll-hyps-generate ((template-alist dpll-hyps-alist-p) (stuff-alist dpll-hyps-alist-p))
  (b* (((unless (consp template-alist)) nil)
       (template-key  (caar template-alist))
       (template-vars (cdar template-alist))
       (hyps-tail (dpll-hyps-generate (cdr template-alist) stuff-alist))
       (stuff (assoc template-key stuff-alist))
       ((unless stuff) hyps-tail)
       (stuff-vars (cdr stuff))
       (vars (if stuff-vars stuff-vars template-vars))
       (hyps (dpll-hyps-hyps template-key vars)))
    (append hyps hyps-tail)))

;; (dpll-hyps-fn key-list) -- the function that does the work for the hyps macro.
(define dpll-hyps-fn (stuff)
  :guard (dpll-hyps-arglist-p stuff)
  :returns (h true-listp)
  (b* ((template '(:int :nat :pos :rat :g1 g1 :Kt Kt :v0 v0 :dv dv :nc nc))
       (template-alist (dpll-make-hyps-alist template))
       (stuff-alist (dpll-make-hyps-alist stuff)))
    (cons 'and (dpll-hyps-generate template-alist stuff-alist))))

(defmacro dpll-hyps (&rest stuff) (dpll-hyps-fn stuff))

(mutual-recursion
 (defun dpll-hyps-expand-fn (stuff)
   (b* (((if (atom stuff)) stuff)
        (fn (car stuff))
        (args (cdr stuff))
        ((if (eq fn 'dpll-hyps))
         (dpll-hyps-fn (if args args (list :g1 :Kt :v0 :dv)))))
     (cons (dpll-hyps-expand-fn fn)
           (do-args args))))
 (defun do-args (args)
   (if (endp args) nil
     (cons (dpll-hyps-expand-fn (car args))
           (do-args (cdr args))))))

(defmacro dpll-hyps-expand (term)
  `(quote ,(dpll-hyps-expand-fn term)))

; mu is a handy normalization term for the frequency terms that occur in the DPLL model.
;   In particular, the values of n and v0 need to satisfy
;     (equal (/ (+ 1 (* *alpha* (+ v0 dv))) (+ 1 (* *beta* n g1))))
;   for the DCO to be oscillating at the target frequency.
(defmacro mu ()
  (/ *f0* (* *N-freq* *fref*)))

; fdco is the *normalized* frequency of the DCO -- it took me (mrg) a while to figure this out.
;   The frequency of the DCO is (* (/ (+ 1 (* *alpha* (+ v0 dv))) (+ 1 (* *beta* n g1))) f0)
;   The target frequency is (* *N-freq* *fref*).  Thus,
;     (* (/ (+ 1 (* *alpha* (+ v0 dv))) (+ 1 (* *beta* nc g1))) mu)
;   is 1 when the DCO is at the target frequency.  (fdco nc v0 dv g1) returns the quantity above.
(defmacro fdco (nc &optional opt-v0 opt-dv opt-g1)
  (b* ((v0 (if opt-v0 opt-v0 'v0))
       (dv (if opt-dv opt-dv 'dv))
       (g1 (if opt-g1 opt-g1 'g1)))
    `(/ (* (mu) (1+ (* *alpha* (+ ,v0 ,dv)))) (1+ (* *beta* ,nc ,g1)))))

; (equ-c v0) is the value of c (i.e. (* nc g1)) that sets the DCO
;   frequency to the target frequency given a control voltage of v0.
;   mrg: I'm guessing I can replace all instances of equ-c with equ-nc
(defmacro equ-c (v0)
  `(/ (1- (* (mu) (1+ (* *alpha* ,v0)))) *beta*))

; (equ-nc v0) is the value of nc that will sets the DCO frequency
;   to the target frequency given a control voltage of v0.
(defmacro equ-nc (v0 g1)
  `(/ (1- (* (mu) (1+ (* *alpha* ,v0)))) (* *beta* ,g1)))

; (gamma Kt) is the attenuation factor for a PLL with time-gain Kt
; In other words, if the phase offset at one rising edge of phi-ref is delta-phi,
; then the phase offset at the next rising edge will be (* (gamma Kt) delta-phi)
; plus any additional phase change due to (- (/ fdco *N-freq*) fref)
(defmacro gamma (Kt)
  `(- 1 ,Kt))

; (m nnco v0 g1) returns a value for nc that is nnco below the value
;   that would establish (equal (fdco n v0 dv g1) (* *N-freq* *fref*))
(defmacro m (nnco v0 g1)
  `(- (equ-nc ,v0 ,g1) ,nnco))

(defmacro dv0 ()
  `(* -2 *g2*)) 

;;:start-proof-tree
(defun fix-rest (stuff)
  (b* (((unless (consp stuff)) nil)
       ((if (eql (caar stuff) :expand)) (fix-rest (cdr stuff)))
       ((if (eql (caar stuff) :uninterpreted)) (fix-rest (cdr stuff))))
    (cons (car stuff) (fix-rest (cdr stuff)))))

(defun smtlink-dpll-fn (clause-name stuff)
  (b* ((my-fns '( (A rationalp)
                  (B-term rationalp)
                  (B-term-expt rationalp)
                  (B-term-rest rationalp)
                  (dv0 rationalp)
                  (delta rationalp)
                  (delta-a-half rationalp)
                  (delta-b-half rationalp)
                  (equ-c rationalp)
                  (equ-nc rationalp)
                  (fdco rationalp)
                  (gamma rationalp)
                  (m rationalp)
                  (mu rationalp)
                  (phi-2n-1 rationalp)
                  (plus rationalp)
                  (delta-a rationalp)
                  (delta-b rationalp)))
       (my-level 1)
       (my-uninterpreted '((expt rationalp rationalp rationalp)))
       (fn-list (append my-fns (cadr (assoc :functions (cadr (assoc :expand stuff))))))
       (new-fn-level (cadr (assoc :expansion-level (cadr (assoc :expand stuff)))))
       (fn-level (if new-fn-level new-fn-level my-level))
       (uninterpreted (append my-uninterpreted (cadr (assoc :uninterpreted-functions stuff))))
       (arg1 `((:expand ((:functions ,fn-list) (:expansion-level ,fn-level)))
               (:uninterpreted-functions ,uninterpreted)
               (:python-file ,clause-name)))
       (args (append arg1 (fix-rest stuff))))
    (list 'smtlink-custom-config 'clause `(quote ,args))))

(defmacro smtlink-dpll (clause-name &optional stuff)
  (smtlink-dpll-fn clause-name stuff))

(defconst *-/2beta* (/ (* -2 *beta*)))
(defun nc-ok-help (g1 stuff)
  (b* (((unless (consp stuff)) nil)
       (nc (car stuff))
       (tail (nc-ok-help g1 (cdr stuff))))
    (cons `(< *-/2beta* (* ,g1 ,nc)) tail)))
(defun nc-ok-fn (g1 stuff)
  (cons 'and (nc-ok-help (if g1 g1 'g1) stuff)))
(defmacro nc-ok (&rest stuff)
  (nc-ok-fn 'g1 stuff))

; a handy special case when the base of the exponent is rational
; I could probably generalize this to the case where
;   (and (equal x 0) (< 0 n))
; but I don't seem to need that version here.
(defthm rationalp-of-expt
  (implies (and (rationalp x) (not (equal 0 x)) (integerp n)) (rationalp (expt x n))))

(defthm expt-gamma-Kt-is-positive
  (implies (dpll-hyps :Kt :int n) (< 0 (expt (gamma Kt) n)))
  :hints(("Goal" :in-theory (enable expt))))

; I would like to redefine m to avoid the need to negate nco.
; I suspect this might be workable now that Yan has revised smtlink to handle
; clauses with multiple disjuncts.  When I have the main proof finished, I'll
; prove an ACL2 rewrite rule that would convert the nice-to-write version
; and transform it into the expression that Z3 can handle.
(define B-term (nco v0 dv g1 Kt)
  :guard (dpll-hyps :v0 :dv :g1 :Kt :nc nco)
  :returns (bt rationalp :hyp :guard)
  (if (< 0 (1+ (* *beta* (+ (* g1 nco) (equ-c v0)))))
      (* (expt (gamma Kt) (- nco))
         (1- (* (mu) (/ (1+ (* *alpha* (+ v0 dv)))
                        (1+ (* *beta* (+ (* g1 nco) (equ-c v0))))))))
    0))


(define B-sum (nco-hi v0 dv g1 Kt)
  :guard (and (dpll-hyps :g1 :Kt :v0 :dv :nat nco-hi) (nc-ok (- nco-hi)))
  :guard-debug t
  :returns (x rationalp :hyp :guard)
  (if (posp nco-hi)
      (+ (B-term nco-hi v0 dv g1 Kt) (B-term (- nco-hi) v0 dv g1 Kt)
         (B-sum (- nco-hi 1) v0 dv g1 Kt))
    0))

(define B (nco v0 dv g1 Kt)
  :guard (and (dpll-hyps :v0 :dv :g1 :kt :int nco) (<= 2 nco) (nc-ok (- 2 nco)))
  :returns (x rationalp :hyp :guard)
  (* (expt (gamma Kt) (- nco 2))
     (B-sum (- nco 2) v0 dv g1 Kt)))

(encapsulate ()
  (local (defthmd lemma-1
           (implies (and (dpll-hyps :Kt :pos h) (<= 2 h))
                    (<= (expt (gamma Kt) h) (expt (gamma Kt) 2)))))

  ;; ACL2 proves that the expanded SMT-link clause implies the original
  ;; much faster when we disable the arithmetic books.
  (local (acl2::disable-theory (theory 'arithmetic-book-only)))

  ;; I'm going through some extra gymnastics to bring a bound on (expt (gamma Kt) h)
  ;; to the attention of my code for handling expt in SMTlink.  I should generalize
  ;; that code to eliminate the ened for the extra hypothesis here.  That should
  ;; allow B-term-neg to be proven directly by the SMT solver without any extra
  ;; lemmas.
  (local (defthm lemma-2
           (implies (and (dpll-hyps :g1 :Kt :v0 :dv :pos h) (nc-ok (- h))
                         (implies (<= 2 h) (<= (expt (gamma Kt) h) (expt (gamma Kt) 2))))
                    (< (+ (B-term h v0 dv g1 Kt) (B-term (- h) v0 dv g1 Kt)) 0))
           :hints (
                   ("Goal"
                    :clause-processor (SMT::smtlink clause)))))

  (local (acl2::enable-theory (theory 'arithmetic-book-only)))

  (defthm B-term-neg
    (implies (and (dpll-hyps :g1 :Kt :v0 :dv :pos h) (nc-ok h (- h)))
             (< (+ (B-term h v0 dv g1 Kt) (B-term (- h) v0 dv g1 Kt)) 0))
    :hints (("Goal''" :use(
                           (:instance lemma-1 (Kt Kt)  (h h))
                           (:instance lemma-2 (g1 g1) (Kt Kt) (v0 v0) (dv dv) (h h)))))
    :rule-classes :linear))


; B-sum-neg show that the sum of a bunch of B-term pairs is negative.
;   This is a trivial induction proof that the sum of a bunch of negative values is negative.
;   We need B-term-neg to know that the terms in the sum are individually negative.
(defthm B-sum-neg
  (implies (and (dpll-hyps :g1 :Kt :v0 :dv :pos n-minus-2) (nc-ok (- n-minus-2)))
           (< (B-sum n-minus-2 v0 dv g1 Kt) 0))
  :hints (("Goal" :in-theory (e/d (B-sum) (B-term)))))

(encapsulate ()
  (local (defthm lemma-1 ; I can't believe I have to do this!
           (implies (and (rationalp x) (rationalp y) (< 0 x) (< y 0))
                    (< (* x y) 0))))

  (defmacro b-neg-hyps ()
    '(and (dpll-hyps :g1 :Kt :v0 :dv :int nnco) (<= 3 nnco) (nc-ok (- nnco 2) (- 2 nnco))))

  (local (defthm lemma-2
           (implies (b-neg-hyps)
                    (and (< 0 (expt (gamma Kt) (- nnco 2)))
                         (< (B-sum (- nnco 2) v0 dv g1 Kt) 0)
                         (< (* (expt (gamma Kt) (- nnco 2)) (B-sum (- nnco 2) v0 dv g1 Kt)) 0)))
           :hints (("Goal"
                    :in-theory (disable lemma-1)
                    :use((:instance lemma-1 (x (expt (gamma Kt) (- nnco 2)))
                                    (y (B-sum (- nnco 2) v0 dv g1 Kt))))))))

  ;; Can I eliminate lemma-2 and just use a :corollary here?
  (defthm B-neg
    (implies (b-neg-hyps)
             (< (B nnco v0 dv g1 Kt) 0))
    :hints (("Goal"
             :in-theory (e/d (B) (lemma-2))
             :use((:instance lemma-2 (g1 g1) (Kt Kt) (v0 v0) (dv dv) (nnco nnco)))))))

(define A (nnco phi0 v0 dv g1 Kt)
  :guard (and (dpll-hyps :nat nnco :rat phi0 :g1 :Kt :v0 :dv) (nc-ok (- nnco)))
  :returns (aa rationalp :hyp :guard)
  (+ (* (expt (gamma Kt) (- (* 2 nnco) 1)) phi0)
     (* (expt (gamma Kt) (- (* 2 nnco) 2))
        (- (fdco (m nnco v0 g1) v0 dv g1) 1))
     (* (expt (gamma Kt) (- (* 2 nnco) 3))
        (- (fdco (1+ (m nnco v0 g1)) v0 dv g1) 1))))

(define phi-2n-1 (nnco phi0 v0 dv g1 Kt)
  :guard (and (dpll-hyps :int nnco :rat phi0 :g1 :Kt :v0 :dv)
              (nc-ok nnco (- nnco)) (<= 2 nnco))
  :returns (x rationalp :hyp :guard)
  (+ (A nnco phi0 v0 dv g1 Kt) (B nnco v0 dv g1 Kt)))


(encapsulate ()
  ;; I suspect that lemma-1 is needed because I have to disable the
  ;;   arithmetic books so that the proof that the expanded clause implies
  ;;   the original clause will go through (for except-for-delta-<-0).
  ;;   However, without the arithmetic books, ACL2 can't figure out
  ;;   that the hypotheses for except-fo-delta-<-0 imply the hypotheses
  ;;   for B-neg (needed for "Subgoal 4").
  (defthm lemma-1
    (implies (and (dpll-hyps :g1 :int nnco) (<= 3 nnco) (nc-ok (- nnco)))
             (nc-ok (- 2 nnco) (- nnco 2))))

  (local (acl2::disable-theory (theory 'arithmetic-book-only)))


  (defun my-smtlink-hint-2 ()
  (declare (xargs :guard t :guard-debug t))
  (change-smtlink-hint
   *default-smtlink-hint*
   :hypotheses (list (make-hint-pair :thm '(< (B nnco v0 dv g1 Kt) '0) :hints nil)
                     ;; (make-hint-pair
                     ;;  :thm '(equal (binary-+ (A nnco phi0 v0 dv g1 Kt) (B nnco v0 dv g1 Kt))
                     ;;               (phi-2n-1 nnco phi0 v0 dv g1 Kt))
                     ;;  :hints nil)
                     (make-hint-pair :thm '(< (phi-2n-1 nnco phi0 v0 dv g1 Kt) '0) :hints nil)
                     )
   :functions (list (make-func :name 'expt
                               :formals (list (make-decl :name 'r
                                                         :type (make-hint-pair :thm 'rationalp :hints nil))
                                              (make-decl :name 'i
                                                         :type (make-hint-pair :thm 'rationalp :hints nil)))
                               :returns (list (make-decl :name 'ex
                                                         :type (make-hint-pair :thm 'rationalp :hints nil)))
                               :body 'nil
                               :expansion-depth 0
                               :uninterpreted t)
                    ;; (make-func :name 'A
                    ;;            :formals (list (make-decl :name 'nnco
                    ;;                                      :type (make-hint-pair :thm 'rationalp :hints nil))
                    ;;                           (make-decl :name 'phi0
                    ;;                                      :type (make-hint-pair :thm 'rationalp :hints nil))
                    ;;                           (make-decl :name 'v0
                    ;;                                      :type (make-hint-pair :thm 'rationalp :hints nil))
                    ;;                           (make-decl :name 'dv
                    ;;                                      :type (make-hint-pair :thm 'rationalp :hints nil))
                    ;;                           (make-decl :name 'g1
                    ;;                                      :type (make-hint-pair :thm 'rationalp :hints nil))
                    ;;                           (make-decl :name 'kt
                    ;;                                      :type (make-hint-pair :thm 'rationalp :hints nil)))
                    ;;            :returns (list (make-decl :name 'aa
                    ;;                                      :type (make-hint-pair :thm 'rationalp :hints nil)))
                    ;;            :body 'nil
                    ;;            :expansion-depth 0
                    ;;            :uninterpreted t)
                    (make-func :name 'B
                               :formals (list (make-decl :name 'nnco
                                                         :type (make-hint-pair :thm 'rationalp :hints nil))
                                              (make-decl :name 'v0
                                                         :type (make-hint-pair :thm 'rationalp :hints nil))
                                              (make-decl :name 'dv
                                                         :type (make-hint-pair :thm 'rationalp :hints nil))
                                              (make-decl :name 'g1
                                                         :type (make-hint-pair :thm 'rationalp :hints nil))
                                              (make-decl :name 'kt
                                                         :type (make-hint-pair :thm 'rationalp :hints nil)))
                               :returns (list (make-decl :name 'bb
                                                         :type (make-hint-pair :thm 'rationalp :hints nil)))
                               :body 'nil
                               :expansion-depth 0
                               :uninterpreted t)
                    ;; (make-func :name 'phi-2n-1
                    ;;            :formals (list (make-decl :name 'nnco
                    ;;                                      :type (make-hint-pair :thm 'rationalp :hints nil))
                    ;;                           (make-decl :name 'phi0
                    ;;                                      :type (make-hint-pair :thm 'rationalp :hints nil))
                    ;;                           (make-decl :name 'v0
                    ;;                                      :type (make-hint-pair :thm 'rationalp :hints nil))
                    ;;                           (make-decl :name 'dv
                    ;;                                      :type (make-hint-pair :thm 'rationalp :hints nil))
                    ;;                           (make-decl :name 'g1
                    ;;                                      :type (make-hint-pair :thm 'rationalp :hints nil))
                    ;;                           (make-decl :name 'kt
                    ;;                                      :type (make-hint-pair :thm 'rationalp :hints nil)))
                    ;;            :returns (list (make-decl :name 'ph
                    ;;                                      :type (make-hint-pair :thm 'rationalp :hints nil)))
                    ;;            :body 'nil
                    ;;            :expansion-depth 0
                    ;;            :uninterpreted t)
                    )
   :int-to-rat t
   :rm-file nil
   :smt-hint nil
   :smt-cnf (my-smtlink-expt-config)
   :wrld-fn-len *wrld-fn-len*))

  (defattach smt-hint my-smtlink-hint-2)
  (add-default-hints '((SMT::SMT-hint-wrapper-hint clause)))

  (defthm except-for-delta-<-0
    (implies (and (dpll-hyps :g1 :Kt :v0 :dv :int nnco :rat phi0)
                  (<= 3 nnco) (nc-ok (- nnco))
                  (< (phi-2n-1 nnco phi0 v0 dv g1 Kt) 0))
             (< (+ (* (gamma Kt) (gamma Kt) (A nnco phi0 v0 dv g1 Kt))
                   (* (gamma Kt) (B nnco v0 dv g1 Kt)))
                0))
    :hints (("Goal"
             :clause-processor (SMT::smtlink clause))
            ("Subgoal 2'"
             :in-theory (enable A B phi-2n-1)))
    ;; :hints (
    ;;         ("Goal'" :clause-processor
    ;;          (smtlink-dpll "except-for-delta-<-0"
    ;;                        ((:let ( (aa (A nnco phi0 v0 dv g1 Kt) rationalp)
    ;;                                 (bb (B nnco v0 dv g1 Kt) rationalp)
    ;;                                 (ph (phi-2n-1 nnco phi0 v0 dv g1 Kt) rationalp)))
    ;;                         (:hypothesize ( (< bb 0)
    ;;                                         (equal (+ aa bb) ph)
    ;;                                         (< ph 0)))))))
    ))

(define delta-a-half (nnco v0 dv g1 Kt)
  :guard (and (dpll-hyps :g1 :Kt :v0 :dv :int nnco) (nc-ok (- -1 nnco)))
  :returns (d rationalp :hyp :guard)
  (* (expt (gamma Kt) nnco)
     (- (fdco (m (+ nnco 1) v0 g1) v0 dv g1)
        (fdco (m nnco v0 g1) v0 dv g1))))

(define delta-a (nnco v0 dv g1 Kt)
  :guard (and (dpll-hyps :g1 :Kt :v0 :dv :int nnco) (nc-ok (- -1 nnco)))
  :returns (a-sum rationalp :hyp :guard)
  (+ (delta-a-half nnco v0 dv g1 Kt)  (delta-a-half (- nnco 1) v0 dv g1 Kt)))

(define delta-b-half (nnco v0 dv g1 Kt)
  :guard (and (dpll-hyps :g1 :Kt :v0 :dv :int nnco) (nc-ok (- nnco)))
  :returns (d rationalp :hyp :guard)
  (* (expt (gamma Kt) (- nnco 1))
     (1- (fdco (m nnco v0 g1) v0 dv g1))))

(define delta-b (nnco-3 v0 dv g1 Kt)
  :guard (and (dpll-hyps :g1 :Kt :v0 :dv :int nnco-3)
              (nc-ok (- -2 nnco-3) (+ 2 nnco-3)))
  :returns (b-sum rationalp :hyp :guard)
  (+ (delta-b-half (- -2 nnco-3) v0 dv g1 Kt) (delta-b-half (+ nnco-3 2) v0 dv g1 Kt)))

(define delta (nnco v0 dv g1 Kt)
  :guard (and (dpll-hyps :g1 :Kt :v0 :dv :int nnco) (<= 3 nnco)
              (nc-ok (- -1 nnco) (- nnco 1)))
  :returns (d rationalp :hyp :guard
              :hints (("Goal"
                       :use (
                             (:instance rationalp-of-expt (x (gamma Kt)) (n nnco))
                             (:instance rationalp-of-delta-a (nnco nnco) (v0 v0) (dv dv) (g1 g1) (Kt Kt))
                             (:instance rationalp-of-delta-b (nnco-3 (- nnco e)) (v0 v0) (dv dv) (g1 g1) (Kt Kt))))))
  (* (expt (gamma Kt) nnco) (+ (delta-a nnco v0 dv g1 Kt) (delta-b (- nnco 3) v0 dv g1 Kt))))

;(encapsulate ()  ; defthm delta-<-0
;; The proofs that the "expanded clause implies the original" go through *much*
;;   faster without the help from the arithmetic books.
(acl2::disable-theory (theory 'arithmetic-book-only))

(defattach smt-hint my-smtlink-hint)
(add-default-hints '((SMT::SMT-hint-wrapper-hint clause)))

(local (defthm delta-a-bound
         (implies (and (dpll-hyps :g1 :Kt :v0 :dv :int nnco)
                       (<= 3 nnco) (< nnco (1- (/ (mu) (* 2 *beta* g1)))))
                  (< (delta-a nnco v0 dv g1 Kt)
                     (* (expt (gamma Kt) (- nnco 1)) (* 4 *beta* g1 (/ (1+ (* 2 *alpha* v0))))
                        (+ 1 (gamma Kt)))))
         :hints(("Goal'" :in-theory (enable delta-a-half delta-a)
                 :clause-processor
                 (SMT::smtlink clause)))))

;; This takes z3 6 minutes on my laptop -- I might break it into a few simpler
;; lemmas.
;; New: This proof takes about 1 min in z3 now. Mark believes -9/8 can be strengthened
;; to -6/5 or even -97/80, but z3 took about 4.5 mins to prove the -6/5 result. We don't
;; need a slower proof.
(local (defthm delta-b-bound
         (implies (and (dpll-hyps :g1 :Kt :v0 :dv :nat nnco-3)
                       (< nnco-3 (- (/ (mu) (* 2 *beta* g1)) 4)))
                  (< (delta-b nnco-3 v0 dv g1 Kt)
                     (* (expt (gamma Kt) (- -3 nnco-3)) *beta*
                        g1 (/ (mu)) (/ (+ 1 (* *alpha* v0))) -9/8
                        )))
         :hints(("Goal'" :in-theory (enable delta-b-half delta-b)
                 :clause-processor
                 (SMT::smtlink clause)))))


;; (stop)


(local (defthm lemma-1x  ; the key inequality for showing (< (delta ...)  0)
         (implies (and (dpll-hyps :g1 :Kt :v0 :dv :nat nnco-3)
                       (< nnco-3 (- (/ (mu) (* 2 *beta* g1)) 4)))
                  (< (+ (* (expt (gamma Kt) (+ nnco-3 2)) (* 4 *beta* g1 (/ (1+ (* 2 *alpha* v0)))) (+ 1 (gamma Kt)))
                        (* (expt (gamma Kt) (- -3 nnco-3)) *beta* g1 (/ (mu)) (/ (+ 1 (* *alpha* v0))) -9/8)) 0))
         :hints(("Goal''" :clause-processor
                 (SMT::smtlink clause)))))

(acl2::enable-theory (theory 'arithmetic-book-only))

;  (local (defthm lemma-rationalp-of-a-bound ; needed for the main proof
;    (implies (and (dpll-hyps :g1 :Kt :v0 :int nnco)
;	     (rationalp (+ (* 4 g1 (/ (+ 1 (* 2 v0))) (expt (gamma Kt) nnco))
;			   (* 4 g1 (/ (+ 1 (* 2 v0))) (expt (gamma Kt) (+ -1 nnco))))))
;    :hints (("Goal" :in-theory (enable gamma))))))
;
;  (local (defthm lemma-rationalp-of-delta-a
;    ; the instance of rational-of-delta-a needed for the main proof
;    (implies (and (hyp-fn (list :g1 g1 :Kt Kt :v0 v0 :dv dv))
;		  (integerp nnco) (< nnco (1- (/ (* 2 *beta* g1)))))
;	     (rationalp (delta-a nnco v0 dv g1 Kt)))
;    :hints (("Goal"
;      :nonlinearp t
;      :in-theory (disable rationalp-of-delta-a)
;      :use((:instance rationalp-of-delta-a (nnco nnco) (v0 v0) (dv dv) (g1 g1) (Kt Kt)))))))
;
;  (local (defthm lemma-rationalp-of-delta-b
;    ; the instance of rational-of-delta-b needed for the main proof
;    (implies (and (hyp-fn (list :g1 g1 :Kt Kt :v0 v0 :dv dv))
;		  (integerp nnco) (<= 3 nnco) (< nnco (1- (/ (* 2 *beta* g1)))))
;	     (rationalp (delta-b (- nnco 3) v0 dv g1 Kt)))
;    :hints (("Goal"
;      :nonlinearp t
;      :in-theory (disable rationalp-of-delta-b)
;      :use((:instance rationalp-of-delta-b (nnco-3 (- nnco 3)) (v0 v0) (dv dv) (g1 g1) (Kt Kt)))))))

(local (defthmd b-bound-corollary  ; instantiate delta-b-bound with (nnco-3 (- nnco 3))
         (implies (and (dpll-hyps :g1 :Kt :v0 :dv :int nnco)
                       (<= 3 nnco) (< nnco (- (/ (mu) (* 2 *beta* g1)) 1)))
                  (< (delta-b (- nnco 3) v0 dv g1 Kt)
                     (* (expt (gamma Kt) (- nnco)) *beta* g1 (/ (mu)) (/ (+ 1 (* *alpha* v0))) -9/8)))
         :hints(("Goal" :in-theory (disable delta-b-bound)
                 :use((:instance delta-b-bound (nnco-3 (- nnco 3)) (v0 v0) (dv dv) (g1 g1) (Kt Kt)))))))

(local (defthmd lemma-1-corollary ; instantiate lemma-1 with (nnco-3 (- nnco 3))
         (implies (and (dpll-hyps :g1 :Kt :v0 :dv :int nnco)
                       (<= 3 nnco) (< nnco (- (/ (mu) (* 2 *beta* g1)) 1)))
                  (< (+ (* (expt (gamma Kt) (- nnco 1)) (* 4 *beta* g1 (/ (1+ (* 2 *alpha* v0)))) (+ 1 (gamma Kt)))
                        (* (expt (gamma Kt) (- nnco)) *beta* g1 (/ (mu)) (/ (+ 1 (* *alpha* v0))) -9/8)) 0))
         :hints(("Goal" :in-theory (disable lemma-1x)
                 :use((:instance lemma-1x (nnco-3 (- nnco 3)) (v0 v0) (g1 g1) (Kt Kt)))))))

(local (defthmd lemma-2-1
         (implies (and (rationalp a0) (rationalp a1) (rationalp b0) (rationalp b1)
                       (< a0 a1) (< b0 b1) (< (+ a1 b1) 0))
                  (< (+ a0 b0) 0))))

(acl2::disable-theory (theory 'arithmetic-book-only))

  (defun my-smtlink-hint-3 ()
  (declare (xargs :guard t :guard-debug t))
  (change-smtlink-hint
   *default-smtlink-hint* ;; ((< a0 a1) (< b0 b1) (< (+ a1 b1) 0))
   :hypotheses (list (make-hint-pair :thm '(< (delta-a nnco v0 dv g1 Kt) a1) :hints delta-a-bound)
                     (make-hint-pair
                      :thm '(equal (binary-+ (A nnco phi0 v0 dv g1 Kt) (B nnco v0 dv g1 Kt))
                                   (phi-2n-1 nnco phi0 v0 dv g1 Kt))
                      :hints nil)
                     (make-hint-pair :thm '(< (phi-2n-1 nnco phi0 v0 dv g1 Kt) '0) :hints nil))
   :functions (list (make-func :name 'expt
                               :formals (list (make-decl :name 'r
                                                         :type (make-hint-pair :thm 'rationalp :hints nil))
                                              (make-decl :name 'i
                                                         :type (make-hint-pair :thm 'rationalp :hints nil)))
                               :returns (list (make-decl :name 'ex
                                                         :type (make-hint-pair :thm 'rationalp :hints nil)))
                               :body 'nil
                               :expansion-depth 0
                               :uninterpreted t)
                    (make-func :name 'A
                               :formals (list (make-decl :name 'nnco
                                                         :type (make-hint-pair :thm 'rationalp :hints nil))
                                              (make-decl :name 'phi0
                                                         :type (make-hint-pair :thm 'rationalp :hints nil))
                                              (make-decl :name 'v0
                                                         :type (make-hint-pair :thm 'rationalp :hints nil))
                                              (make-decl :name 'dv
                                                         :type (make-hint-pair :thm 'rationalp :hints nil))
                                              (make-decl :name 'g1
                                                         :type (make-hint-pair :thm 'rationalp :hints nil))
                                              (make-decl :name 'kt
                                                         :type (make-hint-pair :thm 'rationalp :hints nil)))
                               :returns (list (make-decl :name 'aa
                                                         :type (make-hint-pair :thm 'rationalp :hints nil)))
                               :body 'nil
                               :expansion-depth 0
                               :uninterpreted t)
                    (make-func :name 'B
                               :formals (list (make-decl :name 'nnco
                                                         :type (make-hint-pair :thm 'rationalp :hints nil))
                                              (make-decl :name 'v0
                                                         :type (make-hint-pair :thm 'rationalp :hints nil))
                                              (make-decl :name 'dv
                                                         :type (make-hint-pair :thm 'rationalp :hints nil))
                                              (make-decl :name 'g1
                                                         :type (make-hint-pair :thm 'rationalp :hints nil))
                                              (make-decl :name 'kt
                                                         :type (make-hint-pair :thm 'rationalp :hints nil)))
                               :returns (list (make-decl :name 'bb
                                                         :type (make-hint-pair :thm 'rationalp :hints nil)))
                               :body 'nil
                               :expansion-depth 0
                               :uninterpreted t)
                    (make-func :name 'phi-2n-1
                               :formals (list (make-decl :name 'nnco
                                                         :type (make-hint-pair :thm 'rationalp :hints nil))
                                              (make-decl :name 'phi0
                                                         :type (make-hint-pair :thm 'rationalp :hints nil))
                                              (make-decl :name 'v0
                                                         :type (make-hint-pair :thm 'rationalp :hints nil))
                                              (make-decl :name 'dv
                                                         :type (make-hint-pair :thm 'rationalp :hints nil))
                                              (make-decl :name 'g1
                                                         :type (make-hint-pair :thm 'rationalp :hints nil))
                                              (make-decl :name 'kt
                                                         :type (make-hint-pair :thm 'rationalp :hints nil)))
                               :returns (list (make-decl :name 'ph
                                                         :type (make-hint-pair :thm 'rationalp :hints nil)))
                               :body 'nil
                               :expansion-depth 0
                               :uninterpreted t))
   :int-to-rat t
   :rm-file nil
   :smt-hint nil
   :smt-cnf (my-smtlink-expt-config)
   :wrld-fn-len *wrld-fn-len*))

(defattach smt-hint my-smtlink-hint-3)
(add-default-hints '((SMT::SMT-hint-wrapper-hint clause)))

(local (defthm lemma-2
         (implies (and (dpll-hyps :g1 :Kt :v0 :dv :int nnco)
                       (<= 3 nnco) (nc-ok (- -1 nnco)))
                  (< (+ (delta-a nnco v0 dv g1 Kt) (delta-b (- nnco 3) v0 dv g1 Kt)) 0))
         :hints (("Goal"
                  :in-theory (disable lemma-2-1 delta-a-bound b-bound-corollary lemma-1-corollary)
                  :use ((:instance lemma-2-1
                                          (a0 (delta-a nnco v0 dv g1 Kt))
                                          (a1 (* (expt (gamma Kt) (- nnco 1)) (* 4 *beta* g1 (/ (1+ (* 2 *alpha* v0))))
                                                 (+ 1 (gamma Kt))))
                                          (b0 (delta-b (- nnco 3) v0 dv g1 Kt))
                                          (b1 (* (expt (gamma Kt) (- nnco)) *beta* g1 (/ (mu)) (/ (+ 1 (* *alpha* v0))) -9/8)))
                               (:instance delta-a-bound (nnco nnco) (g1 g1) (v0 v0) (dv dv) (kt kt))
                               (:instance b-bound-corollary (nnco nnco) (g1 g1) (v0 v0) (dv dv) (kt kt))
                               (:instance lemma-1-corollary (nnco nnco) (g1 g1) (v0 v0) (dv dv) (kt kt))
                               (:instance rationalp-of-delta-b (nnco-3 (- nnco 3))))))))
         :hints(
                ("Goal'" :clause-processor )
                ("Goal'" :clause-processor (smtlink-dpll "delta-<-0--lemma-2"
                                                         (  (:let ( (a0 (delta-a nnco v0 dv g1 Kt) rationalp)
                                                                    (a1 (* (expt (gamma Kt) (- nnco 1)) (* 4 *beta* g1 (/ (1+ (* 2 *alpha* v0))))
                                                                           (+ 1 (gamma Kt))) rationalp)
                                                                    (b0 (delta-b (- nnco 3) v0 dv g1 Kt) rationalp)
                                                                    (b1 (* (expt (gamma Kt) (- nnco)) *beta* g1 (/ (mu)) (/ (+ 1 (* *alpha* v0)))
                                                                           -9/8) rationalp)))
                                                            (:hypothesize ((< a0 a1) (< b0 b1) (< (+ a1 b1) 0)))
                                                            (:use (;; (:let  ( (lemma-rationalp-of-delta-a)
                                                                   ;;	         (lemma-rationalp-of-a-bound)
                                                                   ;;	         (lemma-rationalp-of-delta-b)))
                                                                   (:hypo ( (delta-a-bound) (b-bound-corollary) (lemma-1-corollary))))))))
                ("Subgoal 4"
                 :use((:instance delta-a-bound (nnco nnco) (g1 g1) (Kt Kt) (v0 v0) (dv dv)))))))


   (defthm delta-<-0
     (implies (and (hyp-fn (list :g1 g1 :Kt Kt :v0 v0 :dv dv))
                   (integerp nnco) (<= 3 nnco) (< nnco (- (/ (mu) (* 2 *beta* g1)) 1)))
              (< (delta nnco v0 dv g1 Kt) 0))
     :hints(
            ("Goal"
             :in-theory (e/d (delta) (lemma-2 expt-gamma-kt-is-positive))
             :use((:instance lemma-2 (nnco nnco) (v0 v0) (dv dv) (g1 g1) (Kt Kt))))
            ("Subgoal 2"
             :use((:instance expt-gamma-kt-is-positive (n nnco) (Kt Kt))))))
;)
