;;                         DE EXAMPLES: F74181 ALU and F74182 LOOKAHEAD

;; F74181 definitions and DE2 credits to Dr. Warren A. Hunt, Jr.

;; Cole Stewart

(in-package "ACL2")
(include-book "../de2/de-hdl/de5")

(ld "f74181-netlist.lisp")
(ld "f74182-netlist.lisp")
(ld "lkahead-16.lisp")

(defund qv (i)
  ;; Creates the (nfix i)'th BDD variable
  (declare (xargs :guard t))
  (if (posp i)
      (let ((prev (qv (1- i))))
        (hons prev prev))
    (hons t nil)))

(defun qv-adder (c a-v b-v)
  (if (atom a-v)
      (list c)
    (let ((ai (car a-v))
          (bi (car b-v)))
      (cons (q-xor c (q-xor ai bi))
            (qv-adder (q-ite c (q-or ai bi) (q-and ai bi))
                      (cdr a-v)
                      (cdr b-v))))))

(defun firstn (x n)
  (declare (xargs :guard (and (true-listp x)
                              (natp n))))
  (if (zp n)
      nil
    (cons (car x)
          (firstn (cdr x) (1- n)))))

(defun qv-number (start number increment)
  (declare (xargs :guard (and (natp start)
                              (natp number)
                              (natp increment))))
  (if (zp number)
      nil
    (cons (qv start)
          (qv-number (+ start increment) (1- number) increment))))

(defun count-conses (x)
  (declare (xargs :guard t))
  (if (atom x)
      0
    (+ 1
       (count-conses (car x))
       (count-conses (cdr x)))))

(memoize 'count-conses)

(defthm f74181-netlist-can-be-adder
  (let* ((a (qv-number 6 4 2))
         (b (qv-number 7 4 2))
         (c (qv 5))
         (m nil)
         (s0 t) (s1 nil) (s2 nil) (s3 t)
         (cin (q-not c))
         (netlist *f74181-netlist*)
         (complete-answer
          (se 'f74181
              (append  (list cin) a b (list m s0 s1 s2 s3))
              nil
              netlist))
         (c-out (q-not (nth 4 complete-answer)))
         (f-out (list (nth 0 complete-answer)
                      (nth 1 complete-answer)
                      (nth 2 complete-answer)
                      (nth 3 complete-answer)
                      c-out)))
     (equal f-out (qv-adder c a b))))

;; testing de2 lkahead-16-netlist definition
(se 'lkahead-16
    (list
     t
     nil nil nil t nil nil nil nil
     nil nil nil nil nil nil nil nil
     nil nil nil t t nil nil nil
     nil nil nil nil nil nil nil nil
     nil t nil nil t)
    nil
    *lkahead-16-netlist*)

(defthm lkahead-16-can-add
  (let* ((a (qv-number 6 16 2))
         (b (qv-number 7 16 2))
         (c (qv 5))
         (cin (q-not c))
         (complete-answer
          (lkahead-16-netlist cin a b))
         (c-out (q-not (cadr complete-answer)))
         (s-out (append (car complete-answer) (list c-out))))
    (equal s-out (qv-adder c a b))))


(defthm lkahead-64-can-add
  (let* ((a (qv-number 6 64 2))
         (b (qv-number 7 64 2))
         (c (qv 5))
         (cin (q-not c))
         (complete-answer
          (lkahead-64-netlist cin a b))
         (c-out (q-not (cadr complete-answer)))
         (s-out (append (car complete-answer) (list c-out))))
    (equal s-out (qv-adder c a b))))

(defthm lkahead-64-gen-can-add
  (let* ((a (qv-number 6 64 2))
         (b (qv-number 7 64 2))
         (c (qv 5))
         (cin (q-not c))
         (complete-answer
          (lkahead-N-netlist cin a b 1))
         (c-out (q-not (cadr complete-answer)))
         (s-out (append (car complete-answer) (list c-out))))
    (equal s-out (qv-adder c a b))))

(defthm lkahead-1024-gen-can-add
  (let* ((a (qv-number 6 1024 2)) ;; 4^(3+2) = 1024
         (b (qv-number 7 1024 2)) ;; so N=3
         (c (qv 5))
         (cin (q-not c))
         (complete-answer
          (lkahead-N-netlist cin a b 3))
         (c-out (q-not (cadr complete-answer)))
         (s-out (append (car complete-answer) (list c-out))))
    (equal s-out (qv-adder c a b))))

(skip-proofs
 ;; the following proofs go through, they just take a while!
 ;; (4 seconds and 30 seconds)
 (defthm lkahead-4096-gen-can-add
   (let* ((a (qv-number 6 4096 2)) ;; 4^(4+2) = 4096
          (b (qv-number 7 4096 2)) ;; so N=4
          (c (qv 5))
          (cin (q-not c))
          (complete-answer
           (lkahead-N-netlist cin a b 4))
          (c-out (q-not (cadr complete-answer)))
          (s-out (append (car complete-answer) (list c-out))))
     (equal s-out (qv-adder c a b)))))

(skip-proofs
 (defthm lkahead-16384-gen-can-add
   (let* ((a (qv-number 6 16384 2)) ;; 4^(5+2) = 16384
          (b (qv-number 7 16384 2)) ;; so N=5
          (c (qv 5))
          (cin (q-not c))
          (complete-answer
           (lkahead-N-netlist cin a b 5))
          (c-out (q-not (cadr complete-answer)))
          (s-out (append (car complete-answer) (list c-out))))
     (equal s-out (qv-adder c a b)))))

