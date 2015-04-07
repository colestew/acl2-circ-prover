
;; Adder functions

(defun xor3 (a b c)
  (xor a (xor b c)))

(defun b-carry (a b c)
  (if a (or b c) (and b c)))

; Here is the definition of v-adder which generated
; adder blocks will use
(defun v-adder (c a b)
  (if (atom a)
      (list c)
    (cons (xor3 c (car a) (car b))
          (v-adder (b-carry c (car a) (car b))
                   (cdr a)
                   (cdr b)))))

(defun v-to-nat (a)
  (declare (xargs :guard t))
  (if (atom a)
      0
    (+ (if (car a) 1 0)
       (* 2 (v-to-nat (cdr a))))))

;;;  We will now consider what ripple-carry addition means.  We first
;;;  define several "helper" functions.

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

(defthm v-adder-really-adds
  (implies (equal (len a)
                  (len b))
           (equal (v-to-nat (v-adder c a b))
                  (+ (if c 1 0)
                     (v-to-nat a)
                     (v-to-nat b)))))

; Generated netlist for 1-bit-adder block from Cedar
(defun full-adder-netlist (A B Cin )
  (let* (
         (w1 (xor A B))
         (w7 (xor w1 Cin))
         (w5 (and Cin w1))
         (w6 (and B A))
         (w8 (or w5 w6))
         (S w7)
         (Cout w8)
        )
    (list S Cout)))

;; Here we will show that the generated netlist really adds
;; We will show the same below by showing that the two functions are equal
(defthm full-adder-really-adds
  (equal (v-to-nat (full-adder-netlist A B Cin))
         (+ (if Cin 1 0)
            (if A 1 0)
            (if B 1 0))))

;; Here we will show that the generated full adder is equivalent
;; to the correct functional implementation
(defthm v-adder-represents-netlist
  (implies (and (booleanp a)
                   (booleanp b))
              (equal (v-adder c (list a) (list b))
                     (full-adder-netlist a b c))))



