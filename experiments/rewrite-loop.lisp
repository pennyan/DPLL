(in-package "ACL2")
(include-book "arithmetic-5/top" :dir :system)
;; (include-book "../../smtlink/top" :ttags :all)
;;; (INCLUDE-BOOK "../../smtlink/verified/SMT-goal-generator")
;; (include-book "ordinals/lexicographic-ordering" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

;; For below example
;; If lexicographic-ordering is used with arithmetic-5, then there will be
;; rewrite loop; but if lexicographic-ordering-without-arithmetic is used, then
;; the theorem would go through.
(thm
 (IMPLIES
  (AND (< -1/2 (* G1 NCO))
       (INTEGERP NCO)
       (< V0 3)
       (< 0 V0)
       (RATIONALP V0)
       (< KT 9/10)
       (< 1/2 KT)
       (RATIONALP KT)
       (< G1 1/8)
       (< 1/65536 G1)
       (RATIONALP G1))
  (AND
   ;; Disable functional-commutativity-of-minus-*-left
   (OR (<= (+ 1
              (* 1
                 (+ (* G1 NCO)
                    (* (+ -1 (* 1 (+ 1 (* 1 V0)))) 1))))
           0)
       (NOT (EQL (+ 1 (- KT)) 0))
       (<= 0 (- NCO)))
   ;; This one fails too for some reason
   (OR (<= (+ 1
              (* 1
                 (+ (* G1 NCO)
                    (* (+ -1 (* 1 (+ 1 (* 1 V0)))) 1))))
           0)
       (ACL2-NUMBERP (EXPT (+ 1 (- KT)) (- NCO))))
   )))

;; (DEFTHM |(- (* c x))|
;;   (IMPLIES (SYNTAXP (QUOTEP C))
;;            (EQUAL (- (* C X)) (* (- C) X))))

;; (DEFTHM FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT
;;   (EQUAL (* (- X) Y) (- (* X Y))))

