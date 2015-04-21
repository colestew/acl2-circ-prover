;; CS389R
;; University of Texas at Austin
;; Cole Stewart
;;
;; Here we will define a series of functions and models that can
;; be used to represent circuits and evaluate them. First we will
;; define a model which serves a simple evaluator for linear circuits.
;; Then we will define a model which also includes information about
;; time delays within the gates within the circuit as well.

;; first we will define a few easy functions to get us comfortable in our model
;;(include-book "arithmetic/top-with-meta" :dir :system)

(include-book "arithmetic-5/top" :dir :system)

;; recognizes boolean vectors
(defun bvp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (equal x nil)
    (and (booleanp (car x))
         (bvp (cdr x)))))

;; equivalent to boolean-listp 
(thm (equal (bvp x)
            (boolean-listp x)))

;; recognizes tree vectors
(defun tvp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (booleanp x)
    (and (tvp (car x))
         (tvp (cdr x)))))

;; compares the structure of tvs
(defun eq-tv-struct (a b)
  (declare (xargs :guard t))
  (if (or (atom a) (atom b))
      (equal (atom a) (atom b))
    (and (eq-tv-struct (car a) (car b))
         (eq-tv-struct (cdr a) (cdr b)))))

;; counts the number of "tips" in a tv
(defun tv-cnt (x)
  (declare (xargs :guard t))
  (if (atom x)
      1
    (+ (tv-cnt (car x))
       (tv-cnt (cdr x)))))

;; if the structures are equal the number of nodes are equivalent
(thm (implies (eq-tv-struct a b)
              (= (tv-cnt a) (tv-cnt b))))

;; tv-not accepts a boolean cons structure and negates each element
(defun tv-not (x)
  (declare (xargs :guard (tvp x)))
  (if (atom x)
      (not x)
    (cons (tv-not (car x))
          (tv-not (cdr x)))))

;; bv-to-tv accepts a list and converts it to a tv
;; this function essentially replaces the nil-terminator with the last
;; element of the list
(defun bv-to-tv (x)
  (declare (xargs :guard t))
  (if (atom x)
      nil
    (if (atom (cdr x))
        (car x)
      (cons (car x)
            (bv-to-tv (cdr x))))))

;; bv-to-v accepts a boolean cons structure and flattens it into a list
;; useful for showing equality to other models which accept a flat vector
;; as input
(defun tv-to-bv (x)
  (declare (xargs :guard t))
  (if (atom x)
      (list x)
    (append (tv-to-bv (car x))
            (tv-to-bv (cdr x)))))

;; converts a bv to a natural number. Assumes bits are in little endian order
(defun bv-to-nat (x)
  (declare (xargs :guard (bvp x)))
  (if (atom x)
      0
    (+ (if (car x) 1 0)
       (* 2 (bv-to-nat (cdr x))))))

;; converts an arbitrary tv to a natural number. Assumes bits are in little
;; endian order. 
(defun tv-to-nat (x)
  (declare (xargs :guard (tvp x)))
  (if (atom x)
      (if x 1 0)
    (if (atom (car x))
        (+ (if (car x) 1 0)
           (* 2 (tv-to-nat (cdr x))))
      (+ (tv-to-nat (car x))
         (* (tv-to-nat (cdr x))
            (expt 2 (tv-cnt (car x))))))))


;;;  sourced from v-adder-example.lisp by Dr. Hunt
;;;  define several "helper" functions.

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



(defthm bvp->tvp
  (implies (bvp x)
           (tvp x)))

;; converts a natural number to a bv
(defun nat-to-bv (x lenx)
  (declare (xargs :guard (and (natp x)
                              (natp lenx))))
  (if (zp lenx)
      nil
    (cons (if (= (rem-2 x) 1) t nil)
          (nat-to-bv (div-2 x) (1- lenx)))))

(defthm nat-to-bv-of-bv-to-nat
  (implies (bvp x)
           (equal (nat-to-bv (bv-to-nat x) (len x))
                  x)))

(defthm bvp-app
  (implies (and (bvp x)
                (bvp y))
           (bvp (append x y))))

(defthm tvp-app
  (implies (and (tvp x)
                (tvp y))
           (tvp (append x y))))

;; could be tv-bv-ok-lemma-1
(defthm bv-to-nat-of-append
  (implies (and (bvp x)
                (bvp y))
           (= (bv-to-nat (append x y))
                  (+ (bv-to-nat x)
                     (* (bv-to-nat y) (expt 2 (len x)))))))

(defthm tv-bv-ok-lemma-0
  (implies (tvp x)
           (= (tv-cnt x)
              (len (tv-to-bv x)))))

(defthm tv-bv-ok
  (implies (tvp x)
           (= (tv-to-nat x)
              (bv-to-nat (tv-to-bv x)))))

(defun b-xor (a b)
  (declare (xargs :guard t))
  (if a (if b nil t) (if b t nil)))

(defun b-xor3 (a b c)
  (declare (xargs :guard t))
  (b-xor (b-xor a b) c))

(defun b-or (a b)
  (declare (xargs :guard t))
  (if a t (if b t nil)))

(defun b-and (a b)
  (declare (xargs :guard t))
  (if a (if b t nil) nil))

(defun b-if (c a b)
  (declare (xargs :guard t))
  (if c (if a t nil) (if b t nil)))

(defun b-carry (a b c)
  (declare (xargs :guard t))
  (if a (b-or b c) (b-and b c)))

;; the following function defines an adder for tv's.
;; c   the input carry
;; xv  the first input bv
;; yv  the second input bv
(defun tv-adder (c a b)
  (declare (xargs :guard (eq-tv-struct a b)))
  (if (or (atom a) (atom b))
      (cons (b-xor c (b-xor a b))
            (b-carry c a b))
    (let* ((left-ans    (tv-adder c (car a) (car b)))
           (left-vec    (car left-ans))
           (left-carry  (cdr left-ans))
           (right-ans   (tv-adder left-carry (cdr a) (cdr b)))
           (right-vec   (car right-ans))
           (right-carry (cdr right-ans)))
      (cons (cons left-vec
                  right-vec)
            right-carry))))

(defthm tv-adder-really-adds
  (implies (and (tvp a) (tvp b) (eq-tv-struct a b))
           (equal (tv-to-nat (tv-adder c a b))
                  (+ (if c 1 0)
                     (tv-to-nat a)
                     (tv-to-nat b)))))

(defun bv-adder (c a b)
  (if (atom a)
      (list c)
    (cons (b-xor3 c (car a) (car b))
	  (bv-adder (b-carry c (car a) (car b))
		   (cdr a)
		   (cdr b)))))

;; here we define a tv adder which takes arbitrary
;; tv's and converts them to bv's and uses the bv-adder
(defun tv-adder2 (c a b)
  (bv-adder c (tv-to-bv a) (tv-to-bv b)))

(defthm tv-adder2-really-adds-lemma-0
  (equal (append (tv-to-bv a)
                 (tv-to-bv b))
         (tv-to-bv (cons a b))))

(defthm tv-adder2-really-adds
  (implies (and (booleanp c)
                (= (tv-cnt a)
                   (tv-cnt b)))
           (equal (bv-to-nat (tv-adder2 c a b))
                  (+ (if c 1 0)
                     (tv-to-nat a)
                     (tv-to-nat b)))))

;; this is what lemma needs to be proved
;; we have a situation that looks like
;; (bv-to-nat (bv-adder x (tv-to-bv a) (tv-to-bv b)))
;; we need to drive the bv-to-

(defthm bv-adder-really-adds
  (implies (equal (len a)
                  (len b))
	   (equal (bv-to-nat (bv-adder c a b))
		  (+ (if c 1 0)
		     (bv-to-nat a)
		     (bv-to-nat b)))))

(defthm append-tv-to-bv
  (implies (and (tvp a)
                (tvp b))
           (equal (append (tv-to-bv a)
                          (tv-to-bv b))
                  (tv-to-bv (cons a b)))))
