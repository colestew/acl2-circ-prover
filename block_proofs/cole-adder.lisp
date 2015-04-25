(ld "v-adder-example.lisp")

;; mode bits for netlist-f74181
(defconst *M-LOW* nil)
(defconst *S-ADD* (list t nil nil t))

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

;; let's prove our propagate and generate functions are identical to the
;; f74181's p~ and g~ output

;; start with p~
(thm (let* ((a (list a0 a1 a2 a3))
            (b (list b0 b1 b2 b3))
            (s *S-ADD*)
            (s0 (car s))
            (s1 (cadr s))
            (s2 (caddr s))
            (s3 (cadddr s))
            (m nil)
            (output (f74181-netlist cin
                                a0 a1 a2 a3
                                b0 b1 b2 b3
                                m s0 s1 s2 s3))
            (p~ (nth 5 output)))
       (implies (and (boolean-listp a)
                     (boolean-listp b)
                     (boolean-listp s)
                     (boolean-listp output)
                     (booleanp m)
                     (booleanp cin))
                (equal p~ (v-propagate a b))))
     :hints (("Goal" :bdd (:vars nil))))

;; then a little g~
(thm (let* ((a (list a0 a1 a2 a3))
            (b (list b0 b1 b2 b3))
            (s *S-ADD*)
            (s0 (car s))
            (s1 (cadr s))
            (s2 (caddr s))
            (s3 (cadddr s))
            (m nil)
            (output (f74181-netlist cin
                                a0 a1 a2 a3
                                b0 b1 b2 b3
                                m s0 s1 s2 s3))
            (g~ (nth 6 output)))
       (implies (and (boolean-listp a)
                     (boolean-listp b)
                     (boolean-listp s)
                     (boolean-listp output)
                     (booleanp m)
                     (booleanp cin))
                (equal g~ (v-generate a b))))
     :hints (("Goal" :bdd (:vars nil))))


;; now let's make a wrapper for our generic functions and make a 1:1 mapping to
;; the f74181 for m=0 and s=1001 [add]
;;
;; for reference:
;; (f74181-netlist (c~ a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3))
;; -> (f0 f1 f2 f3 cout~ p~ g~ a=b)))

(defun f74181-generic-add (c~ a0 a1 a2 a3 b0 b1 b2 b3)
  (let* ((a (list a0 a1 a2 a3))
         (b (list b0 b1 b2 b3))
         (c (not c~))
         (add (v-adder c a b))
         (sum-0 (nth 0 add))
         (sum-1 (nth 1 add))
         (sum-2 (nth 2 add))
         (sum-3 (nth 3 add))
         (cout (not (nth 4 add)))
         (p~ (v-propagate a b))
         (g~ (v-generate a b))
         (a=b (and sum-0 sum-1 sum-2 sum-3)))
    (list sum-0 sum-1 sum-2 sum-3 cout p~ g~ a=b)))


(defthm f74181-generic-is-correct-c~=nil
  (let ((a (list a0 a1 a2 a3))
        (b (list b0 b1 b2 b3)))
    (implies (and (boolean-listp a)
                  (boolean-listp b)
                  (booleanp c~))
             (equal (f74181-netlist     nil a0 a1 a2 a3 b0 b1 b2 b3 nil t nil nil t)
                    (f74181-generic-add nil a0 a1 a2 a3 b0 b1 b2 b3))))
  :hints (("Goal" :bdd (:vars nil))))

(defthm f74181-generic-is-correct-c~=t
  (let ((a (list a0 a1 a2 a3))
        (b (list b0 b1 b2 b3)))
    (implies (and (boolean-listp a)
                  (boolean-listp b)
                  (booleanp c~))
             (equal (f74181-netlist     t a0 a1 a2 a3 b0 b1 b2 b3 nil t nil nil t)
                    (f74181-generic-add t a0 a1 a2 a3 b0 b1 b2 b3))))
  :hints (("Goal" :bdd (:vars nil))))

;; Note, doing cases here speeds this up by a large factor. I don't understand
;; why the BDD algorithm can't understand this by itself though.

(defthm f74181-generic-is-correct
  (let ((a (list a0 a1 a2 a3))
        (b (list b0 b1 b2 b3)))
    (implies (and (boolean-listp a)
                  (boolean-listp b)
                  (booleanp c~))
             (equal (f74181-netlist     c~ a0 a1 a2 a3 b0 b1 b2 b3 nil t nil nil t)
                    (f74181-generic-add c~ a0 a1 a2 a3 b0 b1 b2 b3))))
  :hints (("Goal" :cases ((equal c~ nil) (equal c~ t)))))


(defun f74181-generic-v (inputs)
  (f74181-generic-add
    (nth 0 inputs)
    (nth 1 inputs) (nth 2 inputs) (nth 3 inputs) (nth 4 inputs)
    (nth 5 inputs) (nth 6 inputs) (nth 7 inputs) (nth 8 inputs)))


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
         (w24 (and w14 w5))
         (w25 (and w5 w0))
         (w26 (nor w24 w25))

         ;; outputs of 74182
         (p~ w4)
         (g~ w13)
         (c~+z w19)
         (c~+y w23)
         (c~+x w26))
    (list p~ g~ c~+x c~+y c~+z)))


;; We create wrappers which accept vectors as input in the wrapper functions
;; below to make it easier to define the lookahead-carry adder

;; (f74181-netlist (c~ a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3))
;; -> (f0 f1 f2 f3 cout~ p~ g~ a=b)))

(defun f74181-netlist-v (inputs)
  (f74181-netlist (nth 0 inputs)
                  (nth 1 inputs)
                  (nth 2 inputs)
                  (nth 3 inputs)
                  (nth 4 inputs)
                  (nth 5 inputs)
                  (nth 6 inputs)
                  (nth 7 inputs)
                  (nth 8 inputs)
                  (nth 9 inputs)
                  (nth 10 inputs)
                  (nth 11 inputs)
                  (nth 12 inputs)
                  (nth 13 inputs)))

;; (f74182-netlist (c~ p0 p1 p2 p3 g0 g1 g2 g3))
;; -> (p~ g~ c~+x c~+y c~+z)

(defun f74182-netlist-v (inputs)
  (f74182-netlist (nth 0 inputs)
                  (nth 1 inputs)
                  (nth 2 inputs)
                  (nth 3 inputs)
                  (nth 4 inputs)
                  (nth 5 inputs)
                  (nth 6 inputs)
                  (nth 7 inputs)
                  (nth 8 inputs)))


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

(defun lookahead-adder-16 (c a b m s0 s1 s2 s3)
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
         (add-0 (f74181-netlist c
                                  a0 a1 a2 a3
                                  b0 b1 b2 b3
                                  m s0 s1 s2 s3))
         (add-0-f0  (car add-0))
         (add-0-f1  (cadr add-0))
         (add-0-f2  (caddr add-0))
         (add-0-f3  (cadddr add-0))
         (add-0-cpg (f74181-get-cpg add-0))
         (lookahead-0 (f74182-netlist (car add-0-cpg)
                                      (cadr add-0-cpg) nil nil nil
                                      (caddr add-0-cpg) nil nil nil))

         ;; adder 1
         (add-1 (f74181-netlist-v (f74182-to-f74181-v
                                   lookahead-0 0
                                   a4 a5 a6 a7
                                   b4 b5 b6 b7
                                   m s0 s1 s2 s3)))
         (add-1-f0  (car add-1))
         (add-1-f1  (cadr add-1))
         (add-1-f2  (caddr add-1))
         (add-1-f3  (cadddr add-1))
         (add-1-cpg (f74181-get-cpg add-1))
         (lookahead-1 (f74182-netlist
                       (car add-0-cpg)
                       (cadr add-0-cpg) (cadr add-1-cpg) nil nil
                       (caddr add-0-cpg) (caddr add-1-cpg) nil nil))

         ;; adder 2
         (add-2 (f74181-netlist-v (f74182-to-f74181-v
                                   lookahead-1 1
                                   a8 a9 a10 a11
                                   b8 b9 b10 b11
                                   m s0 s1 s2 s3)))
         (add-2-f0  (car add-2))
         (add-2-f1  (cadr add-2))
         (add-2-f2  (caddr add-2))
         (add-2-f3  (cadddr add-2))
         (add-2-cpg (f74181-get-cpg add-2))
         (lookahead-2
          (f74182-netlist
           (car add-0-cpg)
           (cadr add-0-cpg) (cadr add-1-cpg) (cadr add-2-cpg) nil
           (caddr add-0-cpg) (caddr add-1-cpg) (caddr add-2-cpg) nil))

         ;; adder 3
         (add-3 (f74181-netlist-v (f74182-to-f74181-v
                                   lookahead-2 2
                                   a12 a13 a14 a15
                                   b12 b13 b14 b15
                                   m s0 s1 s2 s3)))
         (add-3-f0  (car add-3))
         (add-3-f1  (cadr add-3))
         (add-3-f2  (caddr add-3))
         (add-3-f3  (cadddr add-3))
         (cpg-3 (f74181-get-cpg add-3))
         (lookahead-3
          (f74182-netlist
           (car add-0-cpg)
           (cadr add-0-cpg) (cadr add-1-cpg) (cadr add-2-cpg) (cadr cpg-3)
           (caddr add-0-cpg) (caddr add-1-cpg) (caddr add-2-cpg) (caddr cpg-3))))

    (list (list add-0-f0 add-0-f1 add-0-f2 add-0-f3
                add-1-f0 add-1-f1 add-1-f2 add-1-f3
                add-2-f0 add-2-f1 add-2-f2 add-2-f3
                add-3-f0 add-3-f1 add-3-f2 add-3-f3)
          lookahead-3
          (car cpg-3))))

(defun lookahead-adder-generic-16 (c a b m s0 s1 s2 s3)
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
         (add-0 (f74181-generic-add c
                                  a0 a1 a2 a3
                                  b0 b1 b2 b3))
         (add-0-f0  (car add-0))
         (add-0-f1  (cadr add-0))
         (add-0-f2  (caddr add-0))
         (add-0-f3  (cadddr add-0))
         (add-0-cpg (f74181-get-cpg add-0))
         (lookahead-0 (f74182-netlist (car add-0-cpg)
                                      (cadr add-0-cpg) nil nil nil
                                      (caddr add-0-cpg) nil nil nil))

         ;; adder 1
         (add-1 (f74181-generic-v (f74182-to-f74181-v
                                   lookahead-0 0
                                   a4 a5 a6 a7
                                   b4 b5 b6 b7
                                   m s0 s1 s2 s3)))
         (add-1-f0  (car add-1))
         (add-1-f1  (cadr add-1))
         (add-1-f2  (caddr add-1))
         (add-1-f3  (cadddr add-1))
         (add-1-cpg (f74181-get-cpg add-1))
         (lookahead-1 (f74182-netlist
                       (car add-0-cpg)
                       (cadr add-0-cpg) (cadr add-1-cpg) nil nil
                       (caddr add-0-cpg) (caddr add-1-cpg) nil nil))

         ;; adder 2
         (add-2 (f74181-generic-v (f74182-to-f74181-v
                                   lookahead-1 1
                                   a8 a9 a10 a11
                                   b8 b9 b10 b11
                                   m s0 s1 s2 s3)))
         (add-2-f0  (car add-2))
         (add-2-f1  (cadr add-2))
         (add-2-f2  (caddr add-2))
         (add-2-f3  (cadddr add-2))
         (add-2-cpg (f74181-get-cpg add-2))
         (lookahead-2
          (f74182-netlist
           (car add-0-cpg)
           (cadr add-0-cpg) (cadr add-1-cpg) (cadr add-2-cpg) nil
           (caddr add-0-cpg) (caddr add-1-cpg) (caddr add-2-cpg) nil))

         ;; adder 3
         (add-3 (f74181-generic-v (f74182-to-f74181-v
                                   lookahead-2 2
                                   a12 a13 a14 a15
                                   b12 b13 b14 b15
                                   m s0 s1 s2 s3)))
         (add-3-f0  (car add-3))
         (add-3-f1  (cadr add-3))
         (add-3-f2  (caddr add-3))
         (add-3-f3  (cadddr add-3))
         (cpg-3 (f74181-get-cpg add-3))
         (lookahead-3
          (f74182-netlist
           (car add-0-cpg)
           (cadr add-0-cpg) (cadr add-1-cpg) (cadr add-2-cpg) (cadr cpg-3)
           (caddr add-0-cpg) (caddr add-1-cpg) (caddr add-2-cpg) (caddr cpg-3))))

    (list (list add-0-f0 add-0-f1 add-0-f2 add-0-f3
                add-1-f0 add-1-f1 add-1-f2 add-1-f3
                add-2-f0 add-2-f1 add-2-f2 add-2-f3
                add-3-f0 add-3-f1 add-3-f2 add-3-f3)
          lookahead-3
          (car cpg-3))))

;; Now let's see if the carry-lookahead adder really works!
;; we'll compare the proof times between the netlist and the generic adders

;; just take my word for it that this one works. It takes about 36 seconds on
;; my machine. We'll just use the models with the generic 16 bit lookaheads
;; from here on out. The generic version of this proof (next) takes about 12 seconds.
(skip-proofs
 (defthm lookahead-adder-16-really-adds
   (let* ((a (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15))
          (b (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15))
          (s *S-ADD*)
          (s0 (car s))
          (s1 (cadr s))
          (s2 (caddr s))
          (s3 (cadddr s))
          (m *M-LOW*)
          (output (lookahead-adder-16 (not cin) a b m s0 s1 s2 s3))
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
                   (boolean-listp s)
                   (boolean-listp sum)
                   (booleanp m)
                   (booleanp cin)
                   (booleanp cout))
              (equal (list out0 out1 out2 out3 out4 out5 out6 out7
                           out8 out9 out10 out11 out12 out13 out14 out15 cout)
                     (v-adder cin a b))))
   :hints (("Goal" :bdd (:vars nil)))))

(defthm lookahead-adder-generic-16-really-adds
  (let* ((a (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15))
         (b (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15))
         (s *S-ADD*)
         (s0 (car s))
         (s1 (cadr s))
         (s2 (caddr s))
         (s3 (cadddr s))
         (cin nil)
         (m *M-LOW*)
         (output (lookahead-adder-generic-16 (not cin) a b m s0 s1 s2 s3))
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
                  (boolean-listp s)
                  (boolean-listp sum)
                  (booleanp m)
                  (booleanp cout))
             (equal (list out0 out1 out2 out3 out4 out5 out6 out7
                          out8 out9 out10 out11 out12 out13 out14 out15 cout)
                    (v-adder cin a b))))
  :hints (("Goal" :bdd (:vars nil))))

;; Now we will define a 64-bit carry-lookahead adder using 4 16 bit lookahead
;; adders and another carry lookahead unit.
;; (cin a b m s0 s1 s2 s3)
;; -> ((sum) (p~ g~ c~+y c~+z) cout)

(defun lookahead-adder-64 (cin a b m s0 s1 s2 s3)
  (let* (
         (a0 (list (nth 0 a) (nth 1 a) (nth 2 a) (nth 3 a)
                   (nth 4 a) (nth 5 a) (nth 6 a) (nth 7 a)
                   (nth 8 a) (nth 9 a) (nth 10 a) (nth 11 a)
                   (nth 12 a) (nth 13 a) (nth 14 a) (nth 15 a)))
         (a16 (list (nth 16 a) (nth 17 a) (nth 18 a) (nth 19 a)
                   (nth 20 a) (nth 21 a) (nth 22 a) (nth 23 a)
                   (nth 24 a) (nth 25 a) (nth 26 a) (nth 27 a)
                   (nth 28 a) (nth 29 a) (nth 30 a) (nth 31 a)))
         (a32 (list (nth 32 a) (nth 33 a) (nth 34 a) (nth 35 a)
                    (nth 36 a) (nth 37 a) (nth 38 a) (nth 39 a)
                    (nth 40 a) (nth 41 a) (nth 42 a) (nth 43 a)
                    (nth 44 a) (nth 45 a) (nth 46 a) (nth 47 a)))
         (a48 (list (nth 48 a) (nth 49 a) (nth 50 a) (nth 51 a)
                    (nth 52 a) (nth 53 a) (nth 54 a) (nth 55 a)
                    (nth 56 a) (nth 57 a) (nth 58 a) (nth 59 a)
                    (nth 60 a) (nth 61 a) (nth 62 a) (nth 63 a)))
         (b0 (list (nth 0 b) (nth 1 b) (nth 2 b) (nth 3 b)
                   (nth 4 b) (nth 5 b) (nth 6 b) (nth 7 b)
                   (nth 8 b) (nth 9 b) (nth 10 b) (nth 11 b)
                   (nth 12 b) (nth 13 b) (nth 14 b) (nth 15 b)))
         (b16 (list (nth 16 b) (nth 17 b) (nth 18 b) (nth 19 b)
                    (nth 20 b) (nth 21 b) (nth 22 b) (nth 23 b)
                    (nth 24 b) (nth 25 b) (nth 26 b) (nth 27 b)
                    (nth 28 b) (nth 29 b) (nth 30 b) (nth 31 b)))
         (b32 (list (nth 32 b) (nth 33 b) (nth 34 b) (nth 35 b)
                    (nth 36 b) (nth 37 b) (nth 38 b) (nth 39 b)
                    (nth 40 b) (nth 41 b) (nth 42 b) (nth 43 b)
                    (nth 44 b) (nth 45 b) (nth 46 b) (nth 47 b)))
         (b48 (list (nth 48 b) (nth 49 b) (nth 50 b) (nth 51 b)
                    (nth 52 b) (nth 53 b) (nth 54 b) (nth 55 b)
                    (nth 56 b) (nth 57 b) (nth 58 b) (nth 59 b)
                    (nth 60 b) (nth 61 b) (nth 62 b) (nth 63 b)))

         (add-0 (lookahead-adder-generic-16 cin a0 b0 m s0 s1 s2 s3))
         (add-0-cpg (f74181-get-cpg add-0) )
         (look-0 (f74182-netlist
                  cin
                  (cadr add-0-cpg) nil nil nil
                  (caddr add-0-cpg) nil nil nil))

         (add-1 (lookahead-adder-generic-16 (nth 2 look-0) a16 b16 m s0 s1 s2 s3))
         (add-1-cpg (f74181-get-cpg add-1))
         (look-1 (f74182-netlist
                  cin
                  (cadr add-0-cpg) (cadr add-1-cpg) nil nil
                  (caddr add-0-cpg) (caddr add-1-cpg) nil nil))

         (add-2 (lookahead-adder-generic-16 (nth 3 look-1) a32 b32 m s0 s1 s2 s3))
         (add-2-cpg (f74181-get-cpg add-2))
         (look-2 (f74182-netlist
                  cin
                  (cadr add-0-cpg) (cadr add-1-cpg) (cadr add-2-cpg) nil
                  (caddr add-0-cpg) (caddr add-1-cpg) (caddr add-2-cpg) nil))

         (add-3 (lookahead-adder-generic-16 (nth 4 look-2) a48 b48 m s0 s1 s2 s3))
         (cpg-3 (f74181-get-cpg add-3))
         (look-3 (f74182-netlist
                  cin
                  (cadr add-0-cpg) (cadr add-1-cpg) (cadr add-2-cpg) (cadr cpg-3)
                  (caddr add-0-cpg) (caddr add-1-cpg) (caddr add-2-cpg) (caddr
                                                                         cpg-3))))
    (list (list
           (nth 0 add-0) (nth 1 add-0) (nth 2 add-0) (nth 3 add-0)
           (nth 4 add-0) (nth 5 add-0) (nth 6 add-0) (nth 7 add-0)
           (nth 8 add-0) (nth 9 add-0) (nth 10 add-0) (nth 11 add-0)
           (nth 12 add-0) (nth 13 add-0) (nth 14 add-0) (nth 15 add-0)
           (nth 0 add-1) (nth 1 add-1) (nth 2 add-1) (nth 3 add-1)
           (nth 4 add-1) (nth 5 add-1) (nth 6 add-1) (nth 7 add-1)
           (nth 8 add-1) (nth 9 add-1) (nth 10 add-1) (nth 11 add-1)
           (nth 12 add-1) (nth 13 add-1) (nth 14 add-1) (nth 15 add-1)
           (nth 0 add-2) (nth 1 add-2) (nth 2 add-2) (nth 3 add-2)
           (nth 4 add-2) (nth 5 add-2) (nth 6 add-2) (nth 7 add-2)
           (nth 8 add-2) (nth 9 add-2) (nth 10 add-2) (nth 11 add-2)
           (nth 12 add-2) (nth 13 add-2) (nth 14 add-2) (nth 15 add-2)
           (nth 0 add-3) (nth 1 add-3) (nth 2 add-3) (nth 3 add-3)
           (nth 4 add-3) (nth 5 add-3) (nth 6 add-3) (nth 7 add-3)
           (nth 8 add-3) (nth 9 add-3) (nth 10 add-3) (nth 11 add-3)
           (nth 12 add-3) (nth 13 add-3) (nth 14 add-3) (nth 15 add-3))
          look-3
          (car cpg-3))))

;; Now we show that our 64-bit adder can actually add

(defthm lookahead-adder-generic-64-really-adds
  (let* (
         (a (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
                  a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31
                  a32 a33 a34 a35 a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47
                  a48 a49 a50 a51 a52 a53 a54 a55 a56 a57 a58 a59 a60 a61 a62 a63))
         (b (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
                  b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31
                  b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47
                  b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63))

         (s *S-ADD*)
         (s0 (car s))
         (s1 (cadr s))
         (s2 (caddr s))
         (s3 (cadddr s))
         (m *M-LOW*)
         (output (lookahead-adder-64 (not cin) a b m s0 s1 s2 s3))
         (s (car output))

         (s-0 (nth 0 s)) (s-1 (nth 1 s)) (s-2 (nth 2 s)) (s-3 (nth 3 s))
         (s-4 (nth 4 s)) (s-5 (nth 5 s)) (s-6 (nth 6 s)) (s-7 (nth 7 s))
         (s-8 (nth 8 s)) (s-9 (nth 9 s)) (s-10 (nth 10 s)) (s-11 (nth 11 s))
         (s-12 (nth 12 s)) (s-13 (nth 13 s)) (s-14 (nth 14 s)) (s-15 (nth 15 s))
         (s-16 (nth 16 s)) (s-17 (nth 17 s)) (s-18 (nth 18 s)) (s-19 (nth 19 s))
         (s-20 (nth 20 s)) (s-21 (nth 21 s)) (s-22 (nth 22 s)) (s-23 (nth 23 s))
         (s-24 (nth 24 s)) (s-25 (nth 25 s)) (s-26 (nth 26 s)) (s-27 (nth 27 s))
         (s-28 (nth 28 s)) (s-29 (nth 29 s)) (s-30 (nth 30 s)) (s-31 (nth 31 s))
         (s-32 (nth 32 s)) (s-33 (nth 33 s)) (s-34 (nth 34 s)) (s-35 (nth 35 s))
         (s-36 (nth 36 s)) (s-37 (nth 37 s)) (s-38 (nth 38 s)) (s-39 (nth 39 s))
         (s-40 (nth 40 s)) (s-41 (nth 41 s)) (s-42 (nth 42 s)) (s-43 (nth 43 s))
         (s-44 (nth 44 s)) (s-45 (nth 45 s)) (s-46 (nth 46 s)) (s-47 (nth 47 s))
         (s-48 (nth 48 s)) (s-49 (nth 49 s)) (s-50 (nth 50 s)) (s-51 (nth 51 s))
         (s-52 (nth 52 s)) (s-53 (nth 53 s)) (s-54 (nth 54 s)) (s-55 (nth 55 s))
         (s-56 (nth 56 s)) (s-57 (nth 57 s)) (s-58 (nth 58 s)) (s-59 (nth 59 s))
         (s-60 (nth 60 s)) (s-61 (nth 61 s)) (s-62 (nth 62 s)) (s-63 (nth 63 s))

         (cout (not (caddr output))))
    (implies (and (boolean-listp a)
                  (boolean-listp b)
                  (boolean-listp s)
                  (booleanp m)
                  (booleanp cin))
             (equal (list
                     s-0 s-1 s-2 s-3 s-4 s-5 s-6 s-7
                     s-8 s-9 s-10 s-11 s-12 s-13 s-14 s-15
                     s-16 s-17 s-18 s-19 s-20 s-21 s-22 s-23
                     s-24 s-25 s-26 s-27 s-28 s-29 s-30 s-31
                     s-32 s-33 s-34 s-35 s-36 s-37 s-38 s-39
                     s-40 s-41 s-42 s-43 s-44 s-45 s-46 s-47
                     s-48 s-49 s-50 s-51 s-52 s-53 s-54 s-55
                     s-56 s-57 s-58 s-59 s-60 s-61 s-62 s-63
                     cout)
                    (v-adder cin a b))))
  :hints (("Goal" :bdd (:vars nil))))




;; Prove that the adder is an adder for any size. This will require writing a
;; function to generate N-bit adders where N is a factor of 16. 

;; for reference
;;
;; (f74182-netlist (c~ p0 p1 p2 p3 g0 g1 g2 g3))
;; -> (p~ g~ c~+x c~+y c~+z)
;;
;; (lookahead-64 (cin a b m s0 s1 s2 s3))
;; -> ((sum) (p~ g~ c~+y c~+z) cout)

(defun next-halfword (x)
  (nthcdr 16 x))

(defun f74182-get-c~ (f74182-out N)
  (nth (+ 2 (mod (1+ N) 3)) f74182-out))


;; this is the helper function for the lookahead-carry adder generator. The
;; first argument is the result from a previous set of inputs. We are required
;; to pull in the propagate and generate bits from the previous computation to
;; the c~+x. Then we compute the carry for c~+y and c~+z. If there is still
;; more input after that, the result is fed into another lookahead unit (this
;; helper function) and the process continues.

(defun lookahead-adder-16*N-helper (result-0
                                    p0 p1 p2 p3
                                    g0 g1 g2 g3
                                    cin
                                    a b
                                    N)
  (if (zp N)
      result-0
    (let* (
           ;; what index are we working at?
           (lk-i (- 3 (mod N 3)))

           ;; assemble the old p and g vectors
           (p-v-old (list p0 p1 p2 p3))
           (g-v-old (list g0 g1 g2 g3))

           ;; fetch p and g from the previous block
           (p-prev (nth 0 (cadr result-0)))
           (g-prev (nth 1 (cadr result-0)))

           ;; create the new propagate and generate vectors
           (p-v (update-nth lk-i p-prev p-v-old))
           (g-v (update-nth lk-i g-prev g-v-old))

           (lk-result (f74182-netlist
                       cin
                       (nth 0 p-v) (nth 1 p-v) (nth 2 p-v) (nth 3 p-v)
                       (nth 0 g-v) (nth 1 g-v) (nth 2 g-v) (nth 3 g-v)))

           (result-1 (lookahead-adder-16
                      (f74182-get-c~ lk-result lk-i)
                      a b
                      *M-LOW* t nil nil t ))
           (next-step (lookahead-adder-16*N-helper
                       result-1
                       (nth 0 p-v) (nth 1 p-v) (nth 2 p-v) (nth 3 p-v)
                       (nth 0 g-v) (nth 1 g-v) (nth 2 p-v) (nth 3 p-v)
                       cin
                       (next-halfword a) (next-halfword b)
                       (1- N))))
      (list (append (car result-0)
                    (car next-step))
            (cadr  next-step)
            (caddr next-step)))))

;; this function seeds the helper function with a result from a single 16 bit
;; adder with lookahead.

(defun lookahead-adder-16*N (cin a b)
  (let ((adder-0 (lookahead-adder-16 cin a b *M-LOW* t nil nil t))
        (next-N (/ (len a) 16)))
    (lookahead-adder-16*N-helper adder-0
                                 nil nil nil nil
                                 nil nil nil nil
                                 cin
                                 (next-halfword a) (next-halfword b)
                                 next-N)))

(lookahead-adder-16*N t (nat-to-v 1 128) (nat-to-v 4 128))


;; How about a 16 bit generated adder? Let's start simple

(defthm generated-lookahead-adder-16-really-adds
  (let* ((a '(a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15))
         (b '(b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15))
         (output (lookahead-adder-16*N (not cin) a b))
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
         (cout (caddr sum)))
    (implies (and (boolean-listp a)
                  (boolean-listp b)
                  (booleanp cin))
             (equal (list out0 out1 out2 out3 out4 out5 out6 out7
                          out8 out9 out10 out11 out12 out13 out14 out15 cout)
                    (v-adder cin a b))))
  :hints (("Goal" :bdd (:vars nil))))


;; now let's try a 64 bit

(defthm generated-lookahead-adder-64-really-adds
  (let* (
         (a (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
                  a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31
                  a32 a33 a34 a35 a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47
                  a48 a49 a50 a51 a52 a53 a54 a55 a56 a57 a58 a59 a60 a61 a62 a63))
         (b (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
                  b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31
                  b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47
                  b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63))
         (output (lookahead-adder-16*N (not cin) a b))
         (s (car output))
         (s-0 (nth 0 s)) (s-1 (nth 1 s)) (s-2 (nth 2 s)) (s-3 (nth 3 s))
         (s-4 (nth 4 s)) (s-5 (nth 5 s)) (s-6 (nth 6 s)) (s-7 (nth 7 s))
         (s-8 (nth 8 s)) (s-9 (nth 9 s)) (s-10 (nth 10 s)) (s-11 (nth 11 s))
         (s-12 (nth 12 s)) (s-13 (nth 13 s)) (s-14 (nth 14 s)) (s-15 (nth 15 s))
         (s-16 (nth 16 s)) (s-17 (nth 17 s)) (s-18 (nth 18 s)) (s-19 (nth 19 s))
         (s-20 (nth 20 s)) (s-21 (nth 21 s)) (s-22 (nth 22 s)) (s-23 (nth 23 s))
         (s-24 (nth 24 s)) (s-25 (nth 25 s)) (s-26 (nth 26 s)) (s-27 (nth 27 s))
         (s-28 (nth 28 s)) (s-29 (nth 29 s)) (s-30 (nth 30 s)) (s-31 (nth 31 s))
         (s-32 (nth 32 s)) (s-33 (nth 33 s)) (s-34 (nth 34 s)) (s-35 (nth 35 s))
         (s-36 (nth 36 s)) (s-37 (nth 37 s)) (s-38 (nth 38 s)) (s-39 (nth 39 s))
         (s-40 (nth 40 s)) (s-41 (nth 41 s)) (s-42 (nth 42 s)) (s-43 (nth 43 s))
         (s-44 (nth 44 s)) (s-45 (nth 45 s)) (s-46 (nth 46 s)) (s-47 (nth 47 s))
         (s-48 (nth 48 s)) (s-49 (nth 49 s)) (s-50 (nth 50 s)) (s-51 (nth 51 s))
         (s-52 (nth 52 s)) (s-53 (nth 53 s)) (s-54 (nth 54 s)) (s-55 (nth 55 s))
         (s-56 (nth 56 s)) (s-57 (nth 57 s)) (s-58 (nth 58 s)) (s-59 (nth 59 s))
         (s-60 (nth 60 s)) (s-61 (nth 61 s)) (s-62 (nth 62 s)) (s-63 (nth 63 s))
         (cout (caddr output)))
    (implies (and (boolean-listp a)
                  (boolean-listp b)
                  (booleanp cin))
             (equal (list
                     s-0 s-1 s-2 s-3 s-4 s-5 s-6 s-7
                     s-8 s-9 s-10 s-11 s-12 s-13 s-14 s-15
                     s-16 s-17 s-18 s-19 s-20 s-21 s-22 s-23
                     s-24 s-25 s-26 s-27 s-28 s-29 s-30 s-31
                     s-32 s-33 s-34 s-35 s-36 s-37 s-38 s-39
                     s-40 s-41 s-42 s-43 s-44 s-45 s-46 s-47
                     s-48 s-49 s-50 s-51 s-52 s-53 s-54 s-55
                     s-56 s-57 s-58 s-59 s-60 s-61 s-62 s-63
                     cout)
                    (v-adder cin a b))))
  :hints (("Goal" :bdd (:vars nil))))


;; Now let's have some fun
;; Let's make a 128-bit adder

(defthm generated-lookahead-adder-128-really-adds
  (let* ((a (list a0 a1 a2 a3 a4 a5 a6 a7
                  a8 a9 a10 a11 a12 a13 a14 a15
                  a16 a17 a18 a19 a20 a21 a22 a23
                  a24 a25 a26 a27 a28 a29 a30 a31
                  a32 a33 a34 a35 a36 a37 a38 a39
                  a40 a41 a42 a43 a44 a45 a46 a47
                  a48 a49 a50 a51 a52 a53 a54 a55
                  a56 a57 a58 a59 a60 a61 a62 a63
                  a64 a65 a66 a67 a68 a69 a70 a71
                  a72 a73 a74 a75 a76 a77 a78 a79
                  a80 a81 a82 a83 a84 a85 a86 a87
                  a88 a89 a90 a91 a92 a93 a94 a95
                  a96 a97 a98 a99 a100 a101 a102 a103
                  a104 a105 a106 a107 a108 a109 a110 a111
                  a112 a113 a114 a115 a116 a117 a118 a119
                  a120 a121 a122 a123 a124 a125 a126 a127))
         (b (list b0 b1 b2 b3 b4 b5 b6 b7
                  b8 b9 b10 b11 b12 b13 b14 b15
                  b16 b17 b18 b19 b20 b21 b22 b23
                  b24 b25 b26 b27 b28 b29 b30 b31
                  b32 b33 b34 b35 b36 b37 b38 b39
                  b40 b41 b42 b43 b44 b45 b46 b47
                  b48 b49 b50 b51 b52 b53 b54 b55
                  b56 b57 b58 b59 b60 b61 b62 b63
                  b64 b65 b66 b67 b68 b69 b70 b71
                  b72 b73 b74 b75 b76 b77 b78 b79
                  b80 b81 b82 b83 b84 b85 b86 b87
                  b88 b89 b90 b91 b92 b93 b94 b95
                  b96 b97 b98 b99 b100 b101 b102 b103
                  b104 b105 b106 b107 b108 b109 b110 b111
                  b112 b113 b114 b115 b116 b117 b118 b119
                  b120 b121 b122 b123 b124 b125 b126 b127))

         (output (lookahead-adder-16*N (not cin) a b))
         (s (car output))

         (s-0 (nth 0 s)) (s-1 (nth 1 s)) (s-2 (nth 2 s)) (s-3 (nth 3 s))
         (s-4 (nth 4 s)) (s-5 (nth 5 s)) (s-6 (nth 6 s)) (s-7 (nth 7 s))
         (s-8 (nth 8 s)) (s-9 (nth 9 s)) (s-10 (nth 10 s)) (s-11 (nth 11 s))
         (s-12 (nth 12 s)) (s-13 (nth 13 s)) (s-14 (nth 14 s)) (s-15 (nth 15 s))
         (s-16 (nth 16 s)) (s-17 (nth 17 s)) (s-18 (nth 18 s)) (s-19 (nth 19 s))
         (s-20 (nth 20 s)) (s-21 (nth 21 s)) (s-22 (nth 22 s)) (s-23 (nth 23 s))
         (s-24 (nth 24 s)) (s-25 (nth 25 s)) (s-26 (nth 26 s)) (s-27 (nth 27 s))
         (s-28 (nth 28 s)) (s-29 (nth 29 s)) (s-30 (nth 30 s)) (s-31 (nth 31 s))
         (s-32 (nth 32 s)) (s-33 (nth 33 s)) (s-34 (nth 34 s)) (s-35 (nth 35 s))
         (s-36 (nth 36 s)) (s-37 (nth 37 s)) (s-38 (nth 38 s)) (s-39 (nth 39 s))
         (s-40 (nth 40 s)) (s-41 (nth 41 s)) (s-42 (nth 42 s)) (s-43 (nth 43 s))
         (s-44 (nth 44 s)) (s-45 (nth 45 s)) (s-46 (nth 46 s)) (s-47 (nth 47 s))
         (s-48 (nth 48 s)) (s-49 (nth 49 s)) (s-50 (nth 50 s)) (s-51 (nth 51 s))
         (s-52 (nth 52 s)) (s-53 (nth 53 s)) (s-54 (nth 54 s)) (s-55 (nth 55 s))
         (s-56 (nth 56 s)) (s-57 (nth 57 s)) (s-58 (nth 58 s)) (s-59 (nth 59 s))
         (s-60 (nth 60 s)) (s-61 (nth 61 s)) (s-62 (nth 62 s)) (s-63 (nth 63 s))
         (s-64 (nth 64 s)) (s-65 (nth 65 s)) (s-66 (nth 66 s)) (s-67 (nth 67 s))
         (s-68 (nth 68 s)) (s-69 (nth 69 s)) (s-70 (nth 70 s)) (s-71 (nth 71 s))
         (s-72 (nth 72 s)) (s-73 (nth 73 s)) (s-74 (nth 74 s)) (s-75 (nth 75 s))
         (s-76 (nth 76 s)) (s-77 (nth 77 s)) (s-78 (nth 78 s)) (s-79 (nth 79 s))
         (s-80 (nth 80 s)) (s-81 (nth 81 s)) (s-82 (nth 82 s)) (s-83 (nth 83 s))
         (s-84 (nth 84 s)) (s-85 (nth 85 s)) (s-86 (nth 86 s)) (s-87 (nth 87 s))
         (s-88 (nth 88 s)) (s-89 (nth 89 s)) (s-90 (nth 90 s)) (s-91 (nth 91 s))
         (s-92 (nth 92 s)) (s-93 (nth 93 s)) (s-94 (nth 94 s)) (s-95 (nth 95 s))
         (s-96 (nth 96 s)) (s-97 (nth 97 s)) (s-98 (nth 98 s)) (s-99 (nth 99 s))
         (s-100 (nth 100 s)) (s-101 (nth 101 s)) (s-102 (nth 102 s)) (s-103 (nth 103 s))
         (s-104 (nth 104 s)) (s-105 (nth 105 s)) (s-106 (nth 106 s)) (s-107 (nth 107 s))
         (s-108 (nth 108 s)) (s-109 (nth 109 s)) (s-110 (nth 110 s)) (s-111 (nth 111 s))
         (s-112 (nth 112 s)) (s-113 (nth 113 s)) (s-114 (nth 114 s)) (s-115 (nth 115 s))
         (s-116 (nth 116 s)) (s-117 (nth 117 s)) (s-118 (nth 118 s)) (s-119 (nth 119 s))
         (s-120 (nth 120 s)) (s-121 (nth 121 s)) (s-122 (nth 122 s)) (s-123 (nth 123 s))
         (s-124 (nth 124 s)) (s-125 (nth 125 s)) (s-126 (nth 126 s)) (s-127 (nth 127 s)) 
         (cout (caddr output)))
    (implies (and (boolean-listp a)
                  (boolean-listp b)
                  (booleanp cin))
             (equal (list
                     s-0 s-1 s-2 s-3 s-4 s-5 s-6 s-7
                     s-8 s-9 s-10 s-11 s-12 s-13 s-14 s-15
                     s-16 s-17 s-18 s-19 s-20 s-21 s-22 s-23
                     s-24 s-25 s-26 s-27 s-28 s-29 s-30 s-31
                     s-32 s-33 s-34 s-35 s-36 s-37 s-38 s-39
                     s-40 s-41 s-42 s-43 s-44 s-45 s-46 s-47
                     s-48 s-49 s-50 s-51 s-52 s-53 s-54 s-55
                     s-56 s-57 s-58 s-59 s-60 s-61 s-62 s-63
                     s-64 s-65 s-66 s-67 s-68 s-69 s-70 s-71
                     s-72 s-73 s-74 s-75 s-76 s-77 s-78 s-79
                     s-80 s-81 s-82 s-83 s-84 s-85 s-86 s-87
                     s-88 s-89 s-90 s-91 s-92 s-93 s-94 s-95
                     s-96 s-97 s-98 s-99 s-100 s-101 s-102 s-103
                     s-104 s-105 s-106 s-107 s-108 s-109 s-110 s-111
                     s-112 s-113 s-114 s-115 s-116 s-117 s-118 s-119
                     s-120 s-121 s-122 s-123 s-124 s-125 s-126 s-127
                     cout)
                    (v-adder cin a b))))
  :hints (("Goal" :bdd (:vars nil))))
