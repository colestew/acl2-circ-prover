(ld "v-adder-example.lisp")

;; mode bits for netlist-f74181
(defconst *M-LOW* nil)
(defconst *S-ADD* (list t nil nil t))


;; f74182 from the TTL v3 from Texas Instruments. It is a lookahead-carry for
;; the f74181's in add mode. We will use this to connect 4 f74181's to create a
;; 32-bit adder with lookahead and prove its correctness.

;; modeling these netlists is like being santa. You make a list, check it
;; twice, and you want to find out if it's naughty or nice.

(defun f74182-netlist (c~ p0 p1 p2 p3 g0 g1 g2 g3)
  (let* (
         ;; output for P in w4
         (w0 p0)
         (w1 p1)
         (w2 p2)
         (w3 p3)
         (w4 (or w0 w1 w2 w3))

         ;; output for g in w13
         (w5 g0)
         (w6 g1)
         (w7 g2)
         (w8 g3)
         (w9 (and w5 w6 w7 w8))
         (w10 (and w6 w7 w8 w1))
         (w11 (and w7 w8 w2))
         (w12 (and w3 w8))
         (w13 (or w9 w10 w11 w12))

         ;; output for c~+z in w19
         (w14 (not c~))
         (w15 (and w14 w5 w6 w7))
         (w16 (and w5 w6 w7 w0))
         (w17 (and w6 w7 w1))
         (w18 (and w7 w2))
         (w19 (nor w15 w16 w17 w18))

         ;; output for c~+y in w23
         (w20 (and w14 w5 w6))
         (w21 (and w5 w6 w0))
         (w22 (and w1 w6))
         (w23 (nor w20 w21 w22))

         ;; output for c~+x in w26
         (w24 (and w14 w5)) ;; and (not c~) g0
         (w25 (and w5 w0))  ;; and g0 p0
         (w26 (nor w24 w25))

         ;; outputs of 74182
         (p~ w4)
         (g~ w13)
         (c~+z w19)
         (c~+y w23)
         (c~+x w26))
    (list p~ g~ c~+x c~+y c~+z)))

;; first we need to define a generic adder which returns a propagate and
;; generate bit

(defun v-propagate (a b)
  (if (atom a)
      nil
    (or (and (car a) (car b))
        (v-propagate (cdr a) (cdr b)))))

(defun v-generate-r (a b prev)
  (if (atom a)
      prev
    (v-generate-r (cdr a) (cdr b)
                  (if prev
                      (or (car a) (car b))
                    (and (car a) (car b))))))

(defun v-generate (a b)
  (v-generate-r a b t))

;; now we provide some unwinding theorems for the BDD algorithm

(defthm v-propagate-cons
  (equal (v-propagate (cons ai a) (cons bi b))
         (or (and ai bi) (v-propagate a b))))

(defthm v-generate-cons
  (equal (v-generate-r (cons ai a) (cons bi b) prev)
         (v-generate-r a b
                       (if prev
                           (or ai bi)
                         (and ai bi)))))

;; now let's make a wrapper for our generic functions and make a 1:1 mapping to
;; the f74181 for m=0 and s=1001 [add] using the propagate and generate
;; functions we just defined

(defun v-adder-^c (c a b)
  (if (atom a)
      (list (not c))
    (cons (xor3 c (car a) (car b))
          (v-adder-^c (b-carry c (car a) (car b))
                   (cdr a)
                   (cdr b)))))

(defthm v-adder-^c-cons
  (equal (v-adder-^c c (cons ai a) (cons bi b))
         (cons (xor3 c ai bi)
               (v-adder-^c (b-carry c ai bi) a b))))

(defun v-adder-pg (c~ a-v b-v)
  (let ((sum (v-adder-^c (not c~) a-v b-v))
        (p (v-propagate a-v b-v))
        (g (v-generate a-v b-v)))
    (list sum p g)))

(defun f74181-generic-add (c~ a0 a1 a2 a3 b0 b1 b2 b3)
  (let* ((a (list a0 a1 a2 a3))
         (b (list b0 b1 b2 b3))
         (add (v-adder-pg c~ a b))
         (sum (car add))
         (sum-0 (nth 0 sum))
         (sum-1 (nth 1 sum))
         (sum-2 (nth 2 sum))
         (sum-3 (nth 3 sum))
         (cout (nth 4 sum))
         (p~ (cadr add))
         (g~ (caddr add))
         (a=b (and sum-0 sum-1 sum-2 sum-3)))
    (list sum-0 sum-1 sum-2 sum-3 cout p~ g~ a=b)))

;; we now show that our generic version defined by our functions has the same
;; add functionality as the circuit defined by the f74181 netlist

(defthm f74181-is-correct
  (let ((a (list a0 a1 a2 a3))
        (b (list b0 b1 b2 b3)))
    (implies (and (boolean-listp a)
                  (boolean-listp b)
                  (booleanp c~))
             (equal (f74181-netlist     c~ a0 a1 a2 a3 b0 b1 b2 b3 nil t nil nil t)
                    (f74181-generic-add c~ a0 a1 a2 a3 b0 b1 b2 b3)))))


;; while we're at it, we'll go ahead and make our own model of the lookahead
;; carry circuit (f74182). It will take N propagate and generate inputs, output N-1
;; carries and output a propagate and generate bit. It will have the same
;; output as the f74182 when N=4

;; the output propagate bit is true if any of the input propagate bits are
;; high. So this v-or function should suffice

(defun v-or (a)
  (if (atom a)
      nil
    (or (car a) (v-or (cdr a)))))

;; we'll need v-and later for the lookahead carry outputs

(defun v-and (a)
  (if (atom a)
      t
    (and (car a) (v-and (cdr a)))))

;; The circuit for the generate bit looks like the following
;; (or (and g0 g1 g2 g3)
;;     (and p1 g1 g2 g3)
;;     (and p2 g2 g3)
;;     (and p3 g3))
;;
;; so we'll transform this into a recursive pattern

(defun v-lkahead-generate-r (p g prev)
  (if (atom p)
      prev
    (v-lkahead-generate-r (cdr p) (cdr g)
                  (if prev
                      (car g)
                    (and (car p) (car g))))))

(defun v-lkahead-generate (p g)
  (v-lkahead-generate-r p g t))

;; we now need a function to model the carries
;; we notice the f74182 has the following pattern
;; (nor (and p0 g0)
;;      (and cin g0))

;; (nor (and p1 g1)
;;      (and p0 g0 g1)
;;      (and cin g0 g1))

;; (nor (and p2 g2)
;;      (and p1 g1 g2)
;;      (and p0 g0 g1 g2)
;;      (and cin g0 g1 g2))

;; (nor (and p3 g3)
;;      (and p2 g2 g3)
;;      (and p1 g1 g2 g3)
;;      (and p0 g0 g1 g2 g3)
;;      (and cin g0 g1 g2 g3))

(defun rem-last (x)
  (if (atom x)
      nil
    (if (atom (cdr x))
        nil
      (cons (car x) (rem-last (cdr x))))))

(defun v-lkahead-carries-clause-r (p g)
  (if (atom p)
      nil
    (or (and (car p) (v-and g))
        (v-lkahead-carries-clause-r (cdr p) (cdr g)))))

(defun v-lkahead-carries-clause (cin p g)
  (not (or (and (not cin) (v-and g))
           (v-lkahead-carries-clause-r p g))))

(defun v-lkahead-carries (cin p g)
  (if (atom p)
      nil
    (cons (v-lkahead-carries-clause cin p g)
          (v-lkahead-carries cin (rem-last p) (rem-last g)))))

;; and some more unwinding theorems

(defthm v-or-cons
  (equal (v-or (cons ai a))
         (or ai (v-or a))))

(defthm v-and-cons
  (equal (v-and (cons ai a))
         (and ai (v-and a))))

(defthm v-lkahead-generate-cons
  (equal (v-lkahead-generate-r (cons p-i p)
                               (cons gi g) prev)
         (v-lkahead-generate-r p g
                               (if prev
                                   gi
                                 (and p-i gi)))))

(defthm v-lkahead-carries-clause-cons
  (equal (v-lkahead-carries-clause-r (cons p-i p)
                                     (cons gi g))
         (or (and p-i (and gi (v-and g)))
             (v-lkahead-carries-clause-r p g))))

(defun v-lookahead (cin p g)
  (let ((p~ (v-or p))
        (g~ (v-lkahead-generate p g))
        (carries (v-lkahead-carries cin (rem-last p) (rem-last g))))
    (list carries p~ g~)))

;; now we will create a 1:1 generic model of f74182 and prove its correctness

(defun f74182-generic (cin p0 p1 p2 p3 g0 g1 g2 g3)
  (let* ((p (list p0 p1 p2 p3))
         (g (list g0 g1 g2 g3))
         (out (v-lookahead cin p g))
         (carries (car out))
         (cz (car carries))
         (cy (cadr  carries))
         (cx (caddr carries))
         (p~ (cadr out))
         (g~ (caddr out)))
    (list p~ g~ cx cy cz)))


(defthm f74182-generic-correct
  (let ((p (list p0 p1 p2 p3))
        (g (list g0 g1 g2 g3)))
    (implies (and (boolean-listp p)
                  (boolean-listp g)
                  (booleanp cin))
             (equal (f74182-netlist cin p0 p1 p2 p3 g0 g1 g2 g3)
                    (f74182-generic cin p0 p1 p2 p3 g0 g1 g2 g3)))))


;; the following functions will aid in providing the correct arguments to the
;; f74181 and f74182 in the lookahead-carry.

;; function which takes the output to a f74182 and produces the necessary input
;; vector for a f74181.
;; c~i is the carry type where
;; 0 => c~+x
;; 1 => c~+y
;; 2 => c~+z

(defun f74182-to-f74181-v (f74182-output
                           c~i
                           a0 a1 a2 a3
                           b0 b1 b2 b3
                           m s0 s1 s2 s3)
  (list (nth (+ c~i 2) f74182-output)
        a0 a1 a2 a3
        b0 b1 b2 b3
        m
        s0 s1 s2 s3))


;; and a couple of helper functions for bit field extraction

(defun f74181-get-cpg (f74181-output)
  (list (nth 4 f74181-output)
        (nth 5 f74181-output)
        (nth 6 f74181-output)))

(defun f74181-get-fout (f74181-output)
  (list (nth 0 f74181-output)
        (nth 1 f74181-output)
        (nth 2 f74181-output)
        (nth 3 f74181-output)))

;; now we define the 16-bit lookahead-carry as presented in the TTL.

(defun lookahead-adder-generic-16 (cin a b)
  (let* ((a0 (nth 0 a))
         (a1 (nth 1 a))
         (a2 (nth 2 a))
         (a3 (nth 3 a))
         (a4 (nth 4 a))
         (a5 (nth 5 a))
         (a6 (nth 6 a))
         (a7 (nth 7 a))
         (a8 (nth 8 a))
         (a9 (nth 9 a))
         (a10 (nth 10 a))
         (a11 (nth 11 a))
         (a12 (nth 12 a))
         (a13 (nth 13 a))
         (a14 (nth 14 a))
         (a15 (nth 15 a))
         (b0 (nth 0 b))
         (b1 (nth 1 b))
         (b2 (nth 2 b))
         (b3 (nth 3 b))
         (b4 (nth 4 b))
         (b5 (nth 5 b))
         (b6 (nth 6 b))
         (b7 (nth 7 b))
         (b8 (nth 8 b))
         (b9 (nth 9 b))
         (b10 (nth 10 b))
         (b11 (nth 11 b))
         (b12 (nth 12 b))
         (b13 (nth 13 b))
         (b14 (nth 14 b))
         (b15 (nth 15 b))

         ;; adder 0
         (add-0 (f74181-generic-add cin
                                  a0 a1 a2 a3
                                  b0 b1 b2 b3))
         (add-0-f0  (car add-0))
         (add-0-f1  (cadr add-0))
         (add-0-f2  (caddr add-0))
         (add-0-f3  (cadddr add-0))
         (add-0-cpg (f74181-get-cpg add-0))
         (p0 (nth 1 add-0-cpg))
         (g0 (nth 2 add-0-cpg))
         (cx (v-lkahead-carries-clause cin (list p0) (list g0)))

         ;; adder 1
         (add-1 (f74181-generic-add cx
                                a4 a5 a6 a7
                                b4 b5 b6 b7))
         (add-1-f0  (car add-1))
         (add-1-f1  (cadr add-1))
         (add-1-f2  (caddr add-1))
         (add-1-f3  (cadddr add-1))
         (add-1-cpg (f74181-get-cpg add-1))
         (p1 (nth 1 add-1-cpg))
         (g1 (nth 2 add-1-cpg))
         (cy (v-lkahead-carries-clause cin (list p0 p1) (list g0 g1)))

         ;; adder 2
         (add-2 (f74181-generic-add cy
                                a8 a9 a10 a11
                                b8 b9 b10 b11))
         (add-2-f0  (car add-2))
         (add-2-f1  (cadr add-2))
         (add-2-f2  (caddr add-2))
         (add-2-f3  (cadddr add-2))
         (add-2-cpg (f74181-get-cpg add-2))
         (p2 (nth 1 add-2-cpg))
         (g2 (nth 2 add-2-cpg))
         (cz (v-lkahead-carries-clause cin (list p0 p1 p2) (list g0 g1 g2)))

         ;; adder 3
         (add-3 (f74181-generic-add cz
                                  a12 a13 a14 a15
                                  b12 b13 b14 b15))

         (add-3-f0  (car add-3))
         (add-3-f1  (cadr add-3))
         (add-3-f2  (caddr add-3))
         (add-3-f3  (cadddr add-3))
         (cpg-3 (f74181-get-cpg add-3))
         (p3 (nth 1 cpg-3))
         (g3 (nth 2 cpg-3))

         ;; p and g output
         (p~ (v-or (list p0 p1 p2)))
         (g~ (v-lkahead-generate (list p0 p1 p2 p3) (list g0 g1 g2 g3))))

    (list (list add-0-f0 add-0-f1 add-0-f2 add-0-f3
                add-1-f0 add-1-f1 add-1-f2 add-1-f3
                add-2-f0 add-2-f1 add-2-f2 add-2-f3
                add-3-f0 add-3-f1 add-3-f2 add-3-f3)
          (list p~ g~ cx cy cz)
          (car cpg-3))))

;; Now let's see if the carry-lookahead adder really works!
;; we'll compare the proof times between the netlist and the generic adders

;; specifying vars to the BDD algorithm speeds us up from 17 seconds to ~6!

(defthm lookahead-adder-generic-16-really-adds
  (let* ((a (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15))
         (b (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15))
         (output (lookahead-adder-generic-16 (not cin) a b))
         (sum (car output))
         (out0 (nth 0 sum))
         (out1 (nth 1 sum))
         (out2 (nth 2 sum))
         (out3 (nth 3 sum))
         (out4 (nth 4 sum))
         (out5 (nth 5 sum))
         (out6 (nth 6 sum))
         (out7 (nth 7 sum))
         (out8 (nth 8 sum))
         (out9 (nth 9 sum))
         (out10 (nth 10 sum))
         (out11 (nth 11 sum))
         (out12 (nth 12 sum))
         (out13 (nth 13 sum))
         (out14 (nth 14 sum))
         (out15 (nth 15 sum))
         (cout (not (caddr output))))
    (implies (and (boolean-listp a)
                  (boolean-listp b)
                  (booleanp cin)
                  (boolean-listp sum))
             (equal (list out0 out1 out2 out3 out4 out5 out6 out7
                          out8 out9 out10 out11 out12 out13 out14 out15 cout)
                    (v-adder cin a b))))
   :hints (("Goal" :bdd (:vars (cin
                                a0 a1 a2 a3 a4 a5 a6 a7
                                a8 a9 a10 a11 a12 a13 a14 a15
                                b0 b1 b2 b3 b4 b5 b6 b7
                                b8 b9 b10 b11 b12 b13 b14 b15)))))


;; we are going to show that with one lookahead unit the circuit works
;; correctly. Showing the circuit works with 64 bits of input turns out to be
;; too large for the BDD algorithm to process, so we will instead show that the
;; propagate and generate bits which output from the f74182 are correct in
;; comparison the propagate and generate bits to a generic 16 bit adder.

;; so first we need to make a 16 bit adder with no lookahead

(defthm f74182-propagate-generate-correct
  (let* ((a (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15))
         (b (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15))
         (g-gen (v-generate a b))

         (output (lookahead-adder-generic-16 nil a b))
         (lk-output (cadr output))
         (g-check (cadr lk-output)))
    (implies (and (boolean-listp a)
                  (boolean-listp b)
                  (booleanp cin))
             (equal g-gen g-check)))
   :hints (("Goal" :bdd (:vars (
                                a0 a1 a2 a3 a4 a5 a6 a7
                                a8 a9 a10 a11 a12 a13 a14 a15
                                b0 b1 b2 b3 b4 b5 b6 b7
                                b8 b9 b10 b11 b12 b13 b14 b15)))))


(defun lookahead-adder-32 (cin a b)
  (let* (
         (a0 (list (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a)
                   (nth 4 a) (nth 5 a) (nth 6 a) (nth 7 a)
                   (nth 8 a) (nth 9 a) (nth 10 a) (nth 11 a)
                   (nth 12 a) (nth 13 a) (nth 14 a) (nth 15 a)))
         (a16 (list (nth 16 a) (nth 17 a) (nth 18 a) (nth 19 a)
                   (nth 20 a) (nth 21 a) (nth 22 a) (nth 23 a)
                   (nth 24 a) (nth 25 a) (nth 26 a) (nth 27 a)
                   (nth 28 a) (nth 29 a) (nth 30 a) (nth 31 a)))
         (b0 (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b)
                   (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b)
                   (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b)
                   (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)))
         (b16 (list (nth 16 b) (nth 17 b) (nth 18 b) (nth 19 b)
                    (nth 20 b) (nth 21 b) (nth 22 b) (nth 23 b)
                    (nth 24 b) (nth 25 b) (nth 26 b) (nth 27 b)
                    (nth 28 b) (nth 29 b) (nth 30 b) (nth 31 b)))

         (add-0 (lookahead-adder-generic-16 cin a0 b0))
         (add-0-cpg (f74181-get-cpg add-0))
         (p0 (nth 1 add-0-cpg))
         (g0 (nth 2 add-0-cpg))
         (cx (v-lkahead-carries-clause cin (list p0) (list g0)))

         (add-1 (lookahead-adder-generic-16 cx a16 b16))
         (add-1-cpg (f74181-get-cpg add-1)))

    (list (list
           (nth 0 add-0) (nth 1 add-0) (nth 2 add-0) (nth 3 add-0)
           (nth 4 add-0) (nth 5 add-0) (nth 6 add-0) (nth 7 add-0)
           (nth 8 add-0) (nth 9 add-0) (nth 10 add-0) (nth 11 add-0)
           (nth 12 add-0) (nth 13 add-0) (nth 14 add-0) (nth 15 add-0)
           (nth 0 add-1) (nth 1 add-1) (nth 2 add-1) (nth 3 add-1)
           (nth 4 add-1) (nth 5 add-1) (nth 6 add-1) (nth 7 add-1)
           (nth 8 add-1) (nth 9 add-1) (nth 10 add-1) (nth 11 add-1)
           (nth 12 add-1) (nth 13 add-1) (nth 14 add-1) (nth 15 add-1)
          nil
          (car add-1-cpg)))))

(defthm lookahead-adder-generic-16-cx-is-correct
  (let* (
         (a (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15))
         (b (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15))

         (output (lookahead-adder-generic-16 cin a b))

         (carries (cadr output))
         (p~ (car carries))
         (g~ (cadr carries))
         (cout (caddr output))

         (cout-check (v-lkahead-carries-clause cin (list p~) (list g~))))
    (implies (and (boolean-listp a)
                  (boolean-listp b)
                  (booleanp cin))
             (equal cout cout-check)))
  :hints (("Goal" :bdd (:vars (
                               cin
                               a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
                               b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
                               )))))






