;;                         DE EXAMPLES: F74181 ALU and F74182 LOOKAHEAD

;; F74181 definitions and DE2 credits to Dr. Warren A. Hunt, Jr.

;; Cole Stewart

(in-package "ACL2")
(include-book "../de2/de-hdl/de5")

(ld "f74181-netlist.lisp")
(ld "f74182-netlist.lisp")

(defund qv (i)
  ;; Creates the (nfix i)'th BDD variable
  (declare (xargs :guard t))
  (if (posp i)
      (let ((prev (qv (1- i))))
        (hons prev prev))
    (hons t nil)))

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


