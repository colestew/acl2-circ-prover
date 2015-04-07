(defun xor3 (a b c)
  (xor a (xor b c)))

(defun b-carry (a b c)
  (if a (or b c) (and b c)))

(defun v-adder (c a b)
  (if (atom a)
      (list c)
    (cons (xor3 c (car a) (car b))
          (v-adder (b-carry c (car a) (car b))
                   (cdr a)
                   (cdr b)))))

(defun four-bit-adder (x0 x1 x2 x3 y0 y1 y2 y3 Ci)
  (v-adder Ci (list x0 x1 x2 x3) (list y0 y1 y2 y3)))

; Generated netlist for 4-bit-adder block from Cedar
(defun four-bit-adder-netlist (X3 X2 X1 X0 Y3 Y2 Y1 Y0 Ci )
  (let* (
         (S0 (nth 0 (four-bit-adder X0 X1 X2 X3 Y0 Y1 Y2 Y3 Ci)))
         (S1 (nth 1 (four-bit-adder X0 X1 X2 X3 Y0 Y1 Y2 Y3 Ci)))
         (S2 (nth 2 (four-bit-adder X0 X1 X2 X3 Y0 Y1 Y2 Y3 Ci)))
         (S3 (nth 3 (four-bit-adder X0 X1 X2 X3 Y0 Y1 Y2 Y3 Ci)))
         (Co (nth 4 (four-bit-adder X0 X1 X2 X3 Y0 Y1 Y2 Y3 Ci)))
         (V (nth 5 (four-bit-adder X0 X1 X2 X3 Y0 Y1 Y2 Y3 Ci)))
        )
    (list S0 S1 S2 S3 Co V)))

;(thm (equal (four-bit-adder-netlist x3 x2 x1 x0 y3 y2 y1 y0 Ci)
;            (append (four-bit-adder x0 x1 x2 x3 y0 y1 y2 y3 Ci) (list nil))))
