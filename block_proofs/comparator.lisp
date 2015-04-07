

(defun v-to-nat (a)
  (declare (xargs :guard t))
  (if (atom a)
      0
    (+ (if (car a) 1 0)
       (* 2 (v-to-nat (cdr a))))))

(defun rem-2 (x)
  (declare (xargs :guard t))
  (if (<= (nfix x) 1)
      (nfix x)
    (rem-2 (- x 2))))

(defun div-2 (x)
  (declare (xargs :guard t))
  (if (<= (nfix x) 1)
      0
    (+ 1 (div-2 (- x 2)))))

(defun one-at-a-time (x)
  (if (zp x)
      0
    (one-at-a-time (- x 1))))
(defthm div-2-lemma-0
  (implies (natp x)
           (equal (div-2 (* 2 x))
                  x))
  :hints (("Goal" :induct (one-at-a-time x))))

(defthm div-2-lemma-1
  (implies (natp x)
           (equal (div-2 (+ 1 (* 2 x)))
                  x))
  :hints (("Goal" :induct (one-at-a-time x))))

(defun rem-2 (x)
  (declare (xargs :guard t))
  (if (<= (nfix x) 1)
      (nfix x)
    (rem-2 (- x 2))))

(defthm rem-2-lemma-0
  (implies (natp x)
           (equal (rem-2 (* 2 x))
                  0))
  :hints (("Goal" :induct (one-at-a-time x))))

(defthm rem-2-lemma-1
  (implies (natp x)
           (equal (rem-2 (+ 1 (* 2 x)))
                  1))
  :hints (("Goal" :induct (one-at-a-time x))))

;;;  The function NAT-TO-V converts number X into a bit-vector of L bits.
(defun nat-to-v (x l)
  (declare (xargs :guard (and (natp x)
                              (natp l))))
  (if (zp l)
      nil
    (cons (if (= (rem-2 x) 1) t nil)
	  (nat-to-v (div-2 x) (1- l)))))

;;;  To make sure that V-TO-NAT and NAT-TO-V are inverses we prove the
;;;  following.
(defthm nat-to-v-of-v-to-nat
  (implies (boolean-listp x)
           (equal (nat-to-v (v-to-nat x) (len x))
                  x)))


(defun v-< (a b)
  (if (atom a)
      nil
    (if (xor (car a) (car b))
        (and (not (car a)) (car b))
      (v-< (cdr a) (cdr b)))))

(defun v-= (a b)
  (if (atom a)
      (atom b)
    (and (equal (car a) (car b))
         (v-= (cdr a) (cdr b)))))


(defthm v-=-correct
  (implies (and (boolean-listp a)
                (boolean-listp b)
                (equal (len a)
                       (len b)))
           (equal (v-= a b)
                  (= (v-to-nat a) (v-to-nat b)))))


(defun xnor (a b)
  (or (and (not a)
           (not b))
      (and a b)))

(defun nor (a b)
  (not (or a b)))

(defun comparator-netlist (a0 a1 a2 a3 b0 b1 b2 b3)
  (let* (
         (w14 (not b2))
         (w12 (xnor a0 b0))
         (w19 (not b3))
         (w1 (xnor a1 b1))
         (w7 (not b1))
         (w3 (not b0))
         (w26 (xnor a3 b3))
         (w17 (xnor a2 b2))
         (w27 (and w12 w1 w17 w26))
         (w18 (and w1 w12 w14 a2))
         (w11 (and w12 w7 a1))
         (w2 (and w17 w1))
         (w10 (and w3 a0))
         (w25 (and w2 w12 w19 a3))
         (w28 (or w10 w11 w18 w25))
         (w29 (nor w27 w28))
         (a-eq-b w27)
         (a-gt-b w28)
         (a-lt-b w29)
        )
    (list a-eq-b a-gt-b a-lt-b)))

(defthm comparator-netlist-compares-=
  (equal (v-= (list a0 a1 a2 a3) (list b0 b1 b2 b3))
         (comparator-netlist ())))
