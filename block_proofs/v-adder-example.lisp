#||

                Introduction to Hardware Verification
                Using the ACL2 Theorem-Proving System

                         Warren A. Hunt, Jr.
                           September, 1996
                        Updated, January 2003

This set of ACL2 definitions and theroems (collectively known as
events) introduces the modeling of hardware designs with a formal
logic and proving the correctness of hardware designs with a
mechanical theorem prover.  We may later discuss how this approach can
be used to reverse-engineer netlists.

We represent the Boolean values true and false with T and NIL,
resepectively.  We represent a Boolean bit-vector as a list of
Boolean values.  Boolean operations transform a set of Boolean
inputs to a set of Boolean outputs.  We begin by giving the ACL2
definitions for several simple Boolean functions.

(defun not (x)   (if x nil t))

(defun and (x y) (if x (if y t nil) nil))  ; Wrong, over simplfied.

(defun or  (x y) (if x t (if y t nil)))    ; Wrong, over simplfied.

The definitions for AND and OR are actually simplifed from their real
definitions; ACL2 actually allows AND and OR to take an arbitrary
number of inputs.  Further, ACL2 (and Common Lisp) does not
necessarily return only Boolean values.

We may execute a function by constructing a function call where each
formal parameter is given an explict value (i.e., a constant).  For
instance, we write the logical negation of T as (NOT T).  We can
evaluate such function calls by submitting them to ACL2 by typing
(NOT T) to the ACL2 prompt.  To request ACL2 to compute the logical
and of T and NIL one would submit (AND T NIL).

The evaluation of functions may be nested to arbitrary depths.  The
logical negation of the logical and of T and NIL can be specified as
(NOT (AND T NIL)).

We define new functions as compositions of primitive functions and/or
other previously defined functions.  For instance, we could define the
logical-nand function as shown.

(defun nand (x y) (not (and x y)))

We represent a bit-vector as a right-associated list of Boolean values.
To measure the size of a bit-vector we use the primitive function LEN.

(defun len (x)
  (declare (xargs :guard t))
  (if (consp x)
      (+ 1 (len (cdr x)))
    0))


The length of an empty bit-vector is zero, and the length of a
bit-vector with at least one "bit" is one more than the length of the
length of the rest of the bit-vector.

Function LEN is recursive; that is, the body of the function refers to
the function being defined.  The ACL2 system only admits such
functions if the ACL2 system can prove that evaluation of such a
definition will always terminate.  In some cases, the type of input
parameters can determine whether a recursive computation will indeed
terminate.  For each ACL2 function, the ACL2 system includes a guard
which may restrict the formal parameters to specific classes of
objects.  The guard for the function LEN is given as T, indicating
that this definition should compute without error given any kind of
formal parameter.  We will ignore this issue for the remainder of this
note.

ACL2 has a built-in (primitive) function that recognizes a well-formed
Boolean bit-vector.  We give its definition below.

(defun boolean-listp (lst)
  (declare (xargs :guard t))
  (if (atom lst)
      (eq lst nil)
    (and (or (eq (car lst) t)
             (eq (car lst) nil))
         (boolean-listp (cdr lst)))))


||#

;  We now give the definitions for several simple Boolean functions.
;  We define NAND and NOR in such a way that they can accept an
;  arbitrary number of inputs.

(defmacro nand (&rest args)
 `(not (and ,@args)))

(defmacro nor (&rest args)
 `(not (or ,@args)))

;  The function XOR has two formal parameters, XOR3 takes three formal
;  parameters.

; (defun xor (a b)
;   (if a (if b nil t) (if b t nil)))

(defun xor3 (a b c)
  (xor a (xor b c)))

;  We now define a vector exclusive-or function.  We will generally
;  use V-XOR on two Boolean bit-vectors of the same length, although
;  this is not necessary.  What is the (LEN (V-XOR A B))?

(defun v-xor (a b)
  (if (atom a)
      nil
    (cons (xor (car a) (car b))
          (v-xor (cdr a) (cdr b)))))

(thm (equal (LEN (V-XOR A B)) (len a)))
(thm (boolean-listp (V-XOR A B)))



;  Below is the definition of a ripple-carry adder for arbitrary
;  length vectors.

(defun b-carry (a b c)
  (if a (or b c) (and b c)))

(defun v-adder (c a b)
  (if (atom a)
      (list c)
    (cons (xor3 c (car a) (car b))
	  (v-adder (b-carry c (car a) (car b))
		   (cdr a)
		   (cdr b)))))

(thm (equal (len (v-adder c a b)) (1+ (len a))))

(thm (implies
      (and (booleanp c)
           (boolean-listp a)
           (boolean-listp b)
           )
      (boolean-listp (v-adder c a b))))

;  We now define a fixed width two-bit adder.

(defun two-bit-adder (c a b)
  (let ((a0 (car a))
	(a1 (cadr a))
	(b0 (car b))
	(b1 (cadr b)))
    (let ((s0 (xor3 c a0 b0))
	  (c1 (b-carry c a0 b0)))
      (let ((s1 (xor3 c1 a1 b1))
	    (c2 (b-carry c1 a1 b1)))
	(list s0 s1 c2)))))

(defthm two-bit-adder-ok
  (equal (two-bit-adder c (list a0 a1) (list b0 b1))
	 (v-adder       c (list a0 a1) (list b0 b1))))

;  For later use, we prove some unwinding theorems.

(defthm v-adder-cons
  (equal (v-adder c (cons ai a) (cons bi b))
         (cons (xor3 c ai bi)
               (v-adder (b-carry c ai bi) a b))))

(defthm v-adder-nil
  (equal (v-adder c nil nil)
         (cons c nil)))

(defthm v-xor-cons
  (equal (v-xor (cons ai a) (cons bi b))
         (cons (xor ai bi)
               (v-xor a b))))

(defthm v-xor-nil
  (equal (v-xor nil nil)
         nil))


;  We now prove the correctness of our two-bit adder using BDDs.

(thm (let ((a (list a0 a1))
           (b (list b0 b1)))
       (implies (and (boolean-listp a)
                     (boolean-listp b)
                     (booleanp c))
                (equal (two-bit-adder c a b)
                       (v-adder c a b))))
     :hints (("Goal" :bdd (:vars nil))))


;  The next theorem is used to help prove the following theorem.

(defthm fold-constants-in-plus
  (implies (and (syntaxp (quotep x))
                (syntaxp (quotep y)))
           (equal (+ x y z)
                  (+ (+ x y) z))))

(defthm nth-add1-bdd
  (equal (nth (+ 1 n) x)
         (if* (zp (1+ n))
              (car x)
              (nth n (cdr x)))))


;  We now define a three-bit adder.

(defun a-3-bit-adder (c a b)
  (let* ((a0 (nth 0 a))
         (a1 (nth 1 a))
         (a2 (nth 2 a))
         (b0 (nth 0 b))
         (b1 (nth 1 b))
         (b2 (nth 2 b))
         (s1 (xor3 c a0 b0))
         (c1 (b-carry c a0 b0))
         (s2 (xor3 c1 a1 b1))
         (c2 (b-carry c1 a1 b1))
         (s3 (xor3 c2 a2 b2))
         (c3 (b-carry c2 a2 b2)))
        (list s1 s2 s3 c3)))

;  We now prove the correctness of our three-bit adder using BDDs.

#||
(thm (let ((a (list a0 a1 a2))
           (b (list b0 b1 b2)))
       (implies (and (boolean-listp a)
                     (boolean-listp b)
                     (booleanp c))
                (equal (a-3-bit-adder c a b)
                       (v-adder c a b))))
     :hints (("Goal" :bdd (:vars nil))))
||#



;  To make a more interesting example, we will now define a number of
;  functions that specify the 74181 ALU.  We first define two helper
;  functions, and then we define each output bit as a function.

(defun f74181-q0 (a b s0 s1 s2 s3)
  (declare (ignore s0 s1))
  (nor (and b s3 a)
       (and a s2 (not b))))

(defun f74181-q1 (a b s0 s1 s2 s3)
  (declare (ignore s2 s3))
  (nor (and (not b) s1)
       (and s0 b)
       a))

(defun f74181-f0 (cin a0 b0 m s0 s1 s2 s3)
  (let ((m~ (not m)))
    (xor (nand cin m~)
         (xor (f74181-q0 a0 b0 s0 s1 s2 s3)
              (f74181-q1 a0 b0 s0 s1 s2 s3)))))

(defun f74181-f1 (cin a0 a1 b0 b1 m s0 s1 s2 s3)
  (let ((m~ (not m)))
    (xor (nor (and m~ (f74181-q1 a0 b0 s0 s1 s2 s3))
              (and m~ (f74181-q0 a0 b0 s0 s1 s2 s3) cin))
         (xor (f74181-q1 a1 b1 s0 s1 s2 s3)
              (f74181-q0 a1 b1 s0 s1 s2 s3)))))

(defun f74181-f2 (cin a0 a1 a2 b0 b1 b2 m s0 s1 s2 s3)
  (let ((m~ (not m)))
    (xor (nor (and m~ (f74181-q1 a1 b1 s0 s1 s2 s3))
              (and m~
                   (f74181-q1 a0 b0 s0 s1 s2 s3)
                   (f74181-q0 a1 b1 s0 s1 s2 s3))
              (and m~
                   (f74181-q0 a0 b0 s0 s1 s2 s3)
                   (f74181-q0 a1 b1 s0 s1 s2 s3)
                   cin))
         (xor (f74181-q1 a2 b2 s0 s1 s2 s3)
              (f74181-q0 a2 b2 s0 s1 s2 s3)))))

(defun f74181-f3 (cin a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3)
  (let ((m~ (not m)))
    (xor (nor (and m~ (f74181-q1 a2 b2 s0 s1 s2 s3))
              (and m~
                   (f74181-q1 a1 b1 s0 s1 s2 s3)
                   (f74181-q0 a2 b2 s0 s2 s2 s3))
              (and m~
                   (f74181-q1 a0 b0 s0 s1 s2 s3)
                   (f74181-q0 a1 b1 s0 s1 s2 s3)
                   (f74181-q0 a2 b2 s0 s1 s2 s3))
              (and m~
                   (f74181-q0 a0 b0 s0 s1 s2 s3)
                   (f74181-q0 a1 b1 s0 s1 s2 s3)
                   (f74181-q0 a2 b2 s0 s1 s2 s3)
                   cin))
         (xor (f74181-q1 a3 b3 s0 s1 s2 s3)
              (f74181-q0 a3 b3 s0 s1 s2 s3)))))



;  The "extra outputs"of the 74181.

(defun f74181-a=b (cin a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3)
  (and (f74181-f0 cin a0 b0 m s0 s1 s2 s3)
       (f74181-f1 cin a0 a1 b0 b1 m s0 s1 s2 s3)
       (f74181-f2 cin a0 a1 a2 b0 b1 b2 m s0 s1 s2 s3)
       (f74181-f3 cin a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3)))

(defun f74181-prop~ (cin a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3)
  (declare (ignore cin m))
  (nand (f74181-q0 a0 b0 s0 s1 s2 s3)
        (f74181-q0 a1 b1 s0 s1 s2 s3)
        (f74181-q0 a2 b2 s0 s1 s2 s3)
        (f74181-q0 a3 b3 s0 s1 s2 s3)))

(defun f74181-gen~ (cin a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3)
  (declare (ignore cin m))
  (nor (and (f74181-q0 a3 b3 s0 s1 s2 s3)
            (f74181-q0 a2 b2 s0 s1 s2 s3)
            (f74181-q0 a1 b1 s0 s1 s2 s3)
            (f74181-q1 a0 b0 s0 s1 s2 s3))
       (and (f74181-q0 a3 b3 s0 s1 s2 s3)
            (f74181-q0 a2 b2 s0 s1 s2 s3)
            (f74181-q1 a1 b1 s0 s1 s2 s3))
       (and (f74181-q0 a3 b3 s0 s1 s2 s3)
            (f74181-q1 a2 b2 s0 s1 s2 s3))
       (f74181-q1 a3 b3 s0 s1 s2 s3)))

(defun f74181-cout~ (cin a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3)
  (or (not (f74181-gen~ cin a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3))
      (not (nand (not (f74181-prop~ cin a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3))
                 cin))))

;  We define several output functions with multiple outputs

(defun f74181-fout (cin a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3)
  (list (f74181-f0    cin a0 b0 m s0 s1 s2 s3)
        (f74181-f1    cin a0 a1 b0 b1 m s0 s1 s2 s3)
        (f74181-f2    cin a0 a1 a2 b0 b1 b2 m s0 s1 s2 s3)
        (f74181-f3    cin a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3)))

(defun f74181-sumout (cin a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3)
  (list (f74181-f0    cin a0 b0 m s0 s1 s2 s3)
        (f74181-f1    cin a0 a1 b0 b1 m s0 s1 s2 s3)
        (f74181-f2    cin a0 a1 a2 b0 b1 b2 m s0 s1 s2 s3)
        (f74181-f3    cin a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3)
        (f74181-cout~ cin a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3)))

(defun f74181-out (cin a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3)
  (list (f74181-f0    cin a0 b0 m s0 s1 s2 s3)
        (f74181-f1    cin a0 a1 b0 b1 m s0 s1 s2 s3)
        (f74181-f2    cin a0 a1 a2 b0 b1 b2 m s0 s1 s2 s3)
        (f74181-f3    cin a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3)
        (f74181-cout~ cin a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3)
        (f74181-prop~ cin a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3)
        (f74181-gen~  cin a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3)
        (f74181-a=b   cin a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3)))



;  We now prove that the 74181 can implement an exclusive-or function.

(thm (let* ((a (list a0 a1 a2 a3))
            (b (list b0 b1 b2 b3))
            (s (list nil t t nil))
            (s0 (car s))
            (s1 (cadr s))
            (s2 (caddr s))
            (s3 (cadddr s))
            (m t))
       (implies (and (boolean-listp a)
                     (boolean-listp b)
                     (boolean-listp s)
                     (booleanp m)
                     (booleanp cin))
                (equal (f74181-fout cin a0 a1 a2 a3 b0 b1 b2 b3
                                    m s0 s1 s2 s3)
                       (v-xor a b))))
     :hints (("Goal" :bdd (:vars nil))))


;  We state and prove that the 74181 can add.

(thm (let* ((a (list a0 a1 a2 a3))
            (b (list b0 b1 b2 b3))
            (s (list t nil nil t))
            (s0 (car s))
            (s1 (cadr s))
            (s2 (caddr s))
            (s3 (cadddr s))
            (m nil)
            (output (f74181-out (not cin)
                                a0 a1 a2 a3
                                b0 b1 b2 b3
                                m s0 s1 s2 s3))
            (out0 (nth 0 output))
            (out1 (nth 1 output))
            (out2 (nth 2 output))
            (out3 (nth 3 output))
            (out4 (nth 4 output))
            (cout (not out4)))
       (implies (and (boolean-listp a)
                     (boolean-listp b)
                     (boolean-listp s)
                     (booleanp m)
                     (booleanp cin))
                (equal (list out0 out1 out2 out3 cout)
                       (v-adder cin a b))))
     :hints (("Goal" :bdd (:vars nil))))



;  Below is a "netlist" version of the 74181.

(defun f74181-netlist (c~ a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3)
  (let* ((w0  (not m))
         (w1  (not b0))
         (w2  (not b1))
         (w3  (not b2))
         (w4  (not b3))
         (w5  (and a0))
         (w6  (and b0 s0))
         (w7  (and s1 w1))
         (w8  (and w1 s2 a0))
         (w9  (and a0 s3 b0))
         (w10 (and a1))
         (w11 (and b1 s0))
         (w12 (and s1 w2))
         (w13 (and w2 s2 a1))
         (w14 (and a1 s3 b1))
         (w15 (and a2))
         (w16 (and b2 s0))
         (w17 (and s1 w3))
         (w18 (and w3 s2 a2))
         (w19 (and a2 s3 b2))
         (w20 (and a3))
         (w21 (and b3 s0))
         (w22 (and s1 w4))
         (w23 (and w4 s2 a3))
         (w24 (and a3 s3 b3))
         (w25 (nor w5 w6 w7))
         (w26 (nor w8 w9))
         (w27 (nor w10 w11 w12))
         (w28 (nor w13 w14))
         (w29 (nor w15 w16 w17))
         (w30 (nor w18 w19))
         (w31 (nor w20 w21 w22))
         (w32 (nor w23 w24))
         (w33 (xor w25 w26))
         (w34 (xor w27 w28))
         (w35 (xor w29 w30))
         (w36 (xor w31 w32))
         (w37 (nand w0 c~))
         (w38 (and w0 w25))
         (w39 (and w0 w26 c~))
         (w40 (and w0 w27))
         (w41 (and w0 w25 w28))
         (w42 (and w0 w28 w26 c~))
         (w43 (and w0 w29))
         (w44 (and w0 w27 w30))
         (w45 (and w0 w25 w30 w28))
         (w46 (and w0 w30 w28 w26 c~))
         (w47 (nand w26 w28 w30 w32))
         (w48 (nand c~ w26 w28 w30 w32))
         (w49 (and w25 w28 w30 w32))
         (w50 (and w27 w30 w32))
         (w51 (and w29 w32))
         (w52 (and w31))
         (w53 w37)
         (w54 (nor w38 w39))
         (w55 (nor w40 w41 w42))
         (w56 (nor w43 w44 w45 w46))
         (w57 (nor w49 w50 w51 w52))
         (w58 (xor w53 w33))
         (w59 (xor w54 w34))
         (w60 (xor w55 w35))
         (w61 (xor w56 w36))
         (w62 (or (not w48) (not w57)))
         (w63 (and w58 w59 w60 w61))
         (f0  w58)
         (f1  w59)
         (f2  w60)
         (f3  w61)
         (a=b w63)
         (p~  w47)
         (cout~ w62)
         (g~  w57))
    (list f0 f1 f2 f3 cout~ p~ g~ a=b)))


;  We can show that the "netlist" version works exactly like our
;  more abstract 74181 function F74181-OUT.

(thm (let* ((a (list a0 a1 a2 a3))
            (b (list b0 b1 b2 b3))
            (s (list s0 s1 s2 s3)))
       (implies
        (and (boolean-listp a)
             (boolean-listp b)
             (boolean-listp s)
             (booleanp m)
             (booleanp cin))
        (equal (f74181-out cin a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3)
               (f74181-netlist cin a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3))))
     :hints (("Goal" :bdd (:vars nil))))



;;;  We will now consider what ripple-carry addition means.  We first
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



;;;  The function V-TO-NAT converts bit-vector A into a natural number.
;;;  This defines the significance of the bits in a bit-vector.

(defun v-to-nat (a)
  (declare (xargs :guard t))
  (if (atom a)
      0
    (+ (if (car a) 1 0)
       (* 2 (v-to-nat (cdr a))))))


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


;;;  The function XOR has two formal parameters, XOR3 takes three
;;;  formal parameters.

(defun xor3 (a b c)
  (xor a (xor b c)))


;;;  Below is the definition of a ripple-carry adder for arbitrary
;;;  length vectors.

(defun b-carry (a b c)
  (if a (or b c) (and b c)))

(defun v-adder (c a b)
  (if (atom a)
      (list c)
    (cons (xor3 c (car a) (car b))
          (v-adder (b-carry c (car a) (car b))
                   (cdr a)
                   (cdr b)))))

;;;  We now prove that our ripple-carry adder V-ADDER really does
;;;  addition.

(defthm v-adder-really-adds
  (implies (equal (len a)
		  (len b))
	   (equal (v-to-nat (v-adder c a b))
		  (+ (if c 1 0)
		     (v-to-nat a)
		     (v-to-nat b)))))
