;; Here we will describe how we will model cyclic circuits in our model
;; generator. We will start by modeling a basic S-R latch.

;; The input to cyclic circuits is an association list of wires to values.
;; We can associate a certain output name to a wirename. The input and output
;; to a circuit is this association list.

(defun next-st (st oracle)
  (if (atom oracle)
      state
    (next-st (combinational-update st (car oracle))
             (cdr oracle))))

(defun nor (x y)
  (not (or x y)))

(defun input-netlist (inputs circuit-state)
  (list inputs (nth 1 circuit-state) (nth 2 circuit-state)))

(defun netlist-output (circuit-state)
  (nth 2 circuit-state))

(defun sr-latch-netlist (circuit-state)
  (let ((inputs (nth 0 circuit-state))
        (wires (nth 1 circuit-state))
        (outputs (nth 2 circuit-state)))
    (let ((s (nth 0 inputs))
          (r (nth 1 inputs))
          (w0 (nth 0 wires))
          (x (nth 0 outputs)))
      (let* ((x+ (nor w0 r))
             (w0+ (nor s x)))
        (list (list s r)
              (list w0+)
              (list x+))))))

(defthm latch-stays-one
  (equal
   (nth 0
        (netlist-output
         (sr-latch-netlist
          (input-netlist '(nil nil)
                         (sr-latch-netlist (list '(_)
                                                 '(_)
                                                 '(t)))))))
   t))
