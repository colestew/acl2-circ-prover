(defconst *f74182-netlist*
  '((f74182
     (c~ p0 p1 p2 p3 g0 g1 g2 g3)
     (c~+x c~+y c~+z p~ g~)
     ()
     (
      ;; output for propagate in w1
      (g-w0    (w0)    buf   (p0))
      (g-w1    (w1)    buf   (p1))
      (g-w2    (w2)    buf   (p2))
      (g-w3    (w3)    buf   (p3))
      (g-w4    (w4)    or4   (w0 w1 w2 w3))

      ;; output for generate
      (g-w5    (w5)    buf   (g0))
      (g-w6    (w6)    buf   (g1))
      (g-w7    (w7)    buf   (g2))
      (g-w8    (w8)    buf   (g3))
      (g-w9    (w9)    and4  (w5 w6 w7 w8))
      (g-w10   (w10)   and4  (w6 w7 w8 w1))
      (g-w11   (w11)   and3  (w7 w8 w2))
      (g-w12   (w12)   and   (w3 w8))
      (g-w13   (w13)   or4   (w9 w10 w11 w12))

      ;; output for c~+z
      (g-w14   (w14)   not   (c~))
      (g-w15   (w15)   and4  (w14 w5 w6 w7))
      (g-w16   (w16)   and4  (w5 w6 w7 w0))
      (g-w17   (w17)   and3  (w6 w7 w1))
      (g-w18   (w18)   and   (w7 w2))
      (g-w19   (w19)   nor4  (w15 w16 w17 w18))

      ;; output for c~+y
      (g-w20   (w20)   and3  (w14 w5 w6))
      (g-w21   (w21)   and3  (w5 w6 w0))
      (g-w22   (w22)   and   (w1 w6))
      (g-w23   (w23)   nor3  (w20 w21 w22))

      ;; output for c~+x
      (g-w24   (w24)   and   (w14 w5))
      (g-w25   (w25)   and   (w5 w0))
      (g-w26   (w26)   nor   (w24 w25))

      ;; outputs
      (g-c~+x  (c~+x)  buf   (w26))
      (g-c~+y  (c~+y)  buf   (w23))
      (g-c~+z  (c~+z)  buf   (w19))
      (g-g~    (g~)    buf   (w13))
      (g-p~    (p~)    buf   (w4)))
     )))

(defun f74182-netlist (c~ p0 p1 p2 p3 g0 g1 g2 g3)
  (let* (
         ;; output for P in w4
         (w0 p0)
         (w1 p1)
         (w2 p2)
         (w3 p3)
         (w4 (q-or w0 (q-or w1 (q-or w2 w3))))

         ;; output for g in w13
         (w5 g0)
         (w6 g1)
         (w7 g2)
         (w8 g3)
         (w9 (q-and w5 (q-and w6 (q-and w7 w8))))
         (w10 (q-and w6 (q-and w7 (q-and w8 w1))))
         (w11 (q-and w7 (q-and w8 w2)))
         (w12 (q-and w3 w8))
         (w13 (q-or w9 (q-or w10 (q-or w11 w12))))

         ;; output for c~+z in w19
         (w14 (q-not c~))
         (w15 (q-and w14 (q-and w5 (q-and w6 w7))))
         (w16 (q-and w5 (q-and w6 (q-and w7 w0))))
         (w17 (q-and w6 (q-and w7 w1)))
         (w18 (q-and w7 w2))
         (w19 (q-not (q-or w15 (q-or w16 (q-or w17 w18)))))

         ;; output for c~+y in w23
         (w20 (q-and w14 (q-and w5 w6)))
         (w21 (q-and w5 (q-and w6 w0)))
         (w22 (q-and w1 w6))
         (w23 (q-not (q-or w20 (q-or w21 w22))))

         ;; output for c~+x in w26
         (w24 (q-and w14 w5)) ;; and (not c~) g0
         (w25 (q-and w5 w0))  ;; and g0 p0
         (w26 (q-nor w24 w25))

         ;; outputs of 74182
         (p~ w4)
         (g~ w13)
         (c~+z w19)
         (c~+y w23)
         (c~+x w26))
    (list c~+x c~+y c~+z p~ g~)))

(defthm net-syntax-okp-f74182-netlist
  (net-syntax-okp *f74182-netlist*)
  :rule-classes nil)

(defthm net-arity-okp-f74182-netlist
  (net-arity-okp *f74182-netlist*)
  :rule-classes nil)

(defthm f74182-netlist-is-same-as-f74182
  (let* ((c (qv 0))
         (p (list (qv 1) (qv 3) (qv 5) (qv 7)))
         (g (list (qv 2) (qv 4) (qv 6) (qv 8)))
         (p0 (car p))
         (p1 (cadr p))
         (p2 (caddr p))
         (p3 (cadddr p))
         (g0 (car g))
         (g1 (cadr g))
         (g2 (caddr g))
         (g3 (cadddr g))
         (netlist *f74182-netlist*))
    (equal (se 'f74182
               (list c p0 p1 p2 p3 g0 g1 g2 g3)
               nil
               netlist)
           (f74182-netlist c p0 p1 p2 p3 g0 g1 g2 g3))))

