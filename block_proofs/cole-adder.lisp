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
;; -> (list f0 f1 f2 f3 cout~ p~ g~ a=b)))

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
;; -> (list p~ g~ c~+x c~+y c~+z)

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

(defun lookahead-carry-16 (c a b m s0 s1 s2 s3)
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


;; Now let's see if the carry-lookahead adder really works!

(defthm lookahead-adder-16-really-adds
  (let* ((a '(a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15))
         (b '(b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15))
         (s *S-ADD*)
         (s0 (car s))
         (s1 (cadr s))
         (s2 (caddr s))
         (s3 (cadddr s))
         (m *M-LOW*)
         (output (lookahead-carry-16 (not cin) a b m s0 s1 s2 s3))
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
                  (boolean-listp s)
                  (booleanp m)
                  (booleanp cin))
             (equal (list out0 out1 out2 out3 out4 out5 out6 out7
                          out8 out9 out10 out11 out12 out13 out14 out15 cout)
                    (v-adder cin a b))))
  :hints (("Goal" :bdd (:vars nil))))


;; Now we will define a 64-bit carry-lookahead adder using 4 16 bit lookahead
;; adders and another carry lookahead unit.

(defun lookahead-adder-64 (cin a b m s0 s1 s2 s3)
  (let* ((a0 a)
         (b0 b)
         (a16 (nthcdr 16 a))
         (b16 (nthcdr 16 b))
         (a32 (nthcdr 32 a))
         (b32 (nthcdr 32 b))
         (a48 (nthcdr 48 a))
         (b48 (nthcdr 48 b))

         (add-0 (lookahead-carry-16 cin a0 b0 m s0 s1 s2 s3))
         ()
