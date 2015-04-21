(ld "v-adder-example.lisp")

;; mode bits for netlist-f74181
(defconst *M-ADD* nil)
(defconst *S-ADD* (list t nil nil t))


;; f74182 from the TTL v3 from Texas Instruments. It is a lookahead-carry for
;; the f74181's in add mode. We will use this to connect 4 f74181's to create a
;; 32-bit adder with lookahead and prove its correctness.

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
    (list p~ g~ c~+z c~+y c~+x)))


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
;; -> (list p~ g~ c~+z c~+y c~+x)

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
;; 0 => c~+z
;; 1 => c~+y
;; 2 => c~+x

(defun f74182-to-f74181-v (f74182-output
                           c~i
                           a0 a1 a2 a3
                           b0 b1 b2 b3
                           m s-v)
  (list (nth (+ c~i 3) f74182-output)
        a0 a1 a2 a3
        b0 b1 b2 b3
        m
        (nth 0 s-v) (nth 1 s-v) (nth 2 s-v) (nth 3 s-v)))


;; and a couple of helper functions for bit field extraction

(defun f74181-get-cpg (f74181-output)
  (list (nth f74181-output 4)
        (nth f74181-output 5)
        (nth f74181-output 6)))

(defun f74181-get-sum (f74181-output)
  (list (nth f74181-output 0)
        (nth f74181-output 1)
        (nth f74181-output 2)
        (nth f74181-output 3)))


;; now we define the 16-bit lookahead-carry as presented in the TTL.

(defun look-ahead-carry-16 (a b)
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
         (add-0 (f74181-netlist-v (append (list nil
                                                a0 a1 a2 a3
                                                b0 b1 b2 b3)
                                          *M-ADD*
                                          *S-ADD*)))
         (add-0-cpg (f74181-get-cpg add-0))
         (lookahead-0 (f74182-netlist (car   add-0-cpg)
                                      (cadr  add-0-cpg) nil nil nil
                                      (caadr add-0-cpg) nil nil nil))

         ;; adder 1
         (add-1 (f74181-netlist-v (f74182-to-f74181-v
                                   lookahead-0 0
                                   a4 a5 a6 a7
                                   b4 b5 b6 b7
                                   *M-ADD* *S-ADD*)))
         (add-1-cpg (f74181-get-cpg add-1))
         (lookahead-1 (f74182-netlist
                       (car add-1-cpg)
                       (cadr add-0-cpg) (cadr add-1-cpg) nil nil
                       (caadr add-0-cpg) (caadr add-1-cpg) nil nil))

         ;; adder 2
         (add-2 (f74181-netlist-v(f74182-to-f74181-v
                                  lookahead-1 1
                                  a8 a9 a10 a11
                                  b8 b9 b10 b11
                                  *M-ADD* *S-ADD*)))
         (add-2-cpg (f74181-get-cpg add-2))
         (lookahead-2
          (f74182-netlist
           (car add-2-cpg)
           (cadr add-0-cpg) (cadr add-1-cpg) (cadr add-2-cpg) nil
           (caadr add-0-cpg) (caadr add-1-cpg) (caadr add-2-cpg) nil))

         ;; adder 3
         (add-3 (f74181-netlist-v (f74182-to-f74181-v
                                   lookahead-2 2
                                   a12 a13 a14 a15
                                   b12 b13 b14 b15
                                   *M-ADD* *S-ADD*)))
         (cpg-3 (f74181-get-cpg add-3))
         (lookahead-3
          (f74182-netlist
           (car cpg-3)
           (cadr add-0-cpg) (cadr add-1-cpg) (cadr add-2-cpg) (cadr cpg-3)
           (caadr add-0-cpg) (caadr add-1-cpg) (caadr add-2-cpg) (caadr cpg-3))))

    (list (append (f74181-get-sum add-0)
                  (f74181-get-sum add-1)
                  (f74181-get-sum add-2)
                  (f74181-get-sum add-3))
          lookahead-3)))

;; (defun f74182-to-f74181-v (f74182-output
;;                              c~i
;;                              a0 a1 a2 a3
;;                              b0 b1 b2 b3
;;                              m s-v)
;; (f74182-netlist (c~ p0 p1 p2 p3 g0 g1 g2 g3))
;; -> (list p~ g~ c~+z c~+y c~+x)
