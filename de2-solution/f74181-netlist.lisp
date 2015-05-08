(defconst *f74181-netlist*
        '((f74181
           (c~ a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3)
           (f0 f1 f2 f3 cout~ p~ g~ a=b)
           ()
           (
            (g-w0    (w0)    not   (m))
            (g-w1    (w1)    not   (b0))
            (g-w2    (w2)    not   (b1))
            (g-w3    (w3)    not   (b2))
            (g-w4    (w4)    not   (b3))
            (g-w5    (w5)    buf   (a0))
            (g-w6    (w6)    and   (b0 s0))
            (g-w7    (w7)    and   (s1 w1))
            (g-w8    (w8)    and3  (w1 s2 a0))
            (g-w9    (w9)    and3  (a0 s3 b0))
            (g-w10   (w10)   buf   (a1))
            (g-w11   (w11)   and   (b1 s0))
            (g-w12   (w12)   and   (s1 w2))
            (g-w13   (w13)   and3  (w2 s2 a1))
            (g-w14   (w14)   and3  (a1 s3 b1))
            (g-w15   (w15)   buf   (a2))
            (g-w16   (w16)   and   (b2 s0))
            (g-w17   (w17)   and   (s1 w3))
            (g-w18   (w18)   and3  (w3 s2 a2))
            (g-w19   (w19)   and3  (a2 s3 b2))
            (g-w20   (w20)   buf   (a3))
            (g-w21   (w21)   and   (b3 s0))
            (g-w22   (w22)   and   (s1 w4))
            (g-w23   (w23)   and3  (w4 s2 a3))
            (g-w24   (w24)   and3  (a3 s3 b3))
            (g-w25   (w25)   nor3  (w5 w6 w7))
            (g-w26   (w26)   nor   (w8 w9))
            (g-w27   (w27)   nor3  (w10 w11 w12))
            (g-w28   (w28)   nor   (w13 w14))
            (g-w29   (w29)   nor3  (w15 w16 w17))
            (g-w30   (w30)   nor   (w18 w19))
            (g-w31   (w31)   nor3  (w20 w21 w22))
            (g-w32   (w32)   nor   (w23 w24))
            (g-w33   (w33)   xor   (w25 w26))
            (g-w34   (w34)   xor   (w27 w28))
            (g-w35   (w35)   xor   (w29 w30))
            (g-w36   (w36)   xor   (w31 w32))
            (g-w37   (w37)   nand  (w0 c~))
            (g-w38   (w38)   and   (w0 w25))
            (g-w39   (w39)   and3  (w0 w26 c~))
            (g-w40   (w40)   and   (w0 w27))
            (g-w41   (w41)   and3  (w0 w25 w28))
            (g-w42   (w42)   and4  (w0 w28 w26 c~))
            (g-w43   (w43)   and   (w0 w29))
            (g-w44   (w44)   and3  (w0 w27 w30))
            (g-w45   (w45)   and4  (w0 w25 w30 w28))
            (g-w46a  (w46a)  and   (w0 w30))
            (g-w46   (w46)   and4  (w46a w28 w26 c~))
            (g-w47   (w47)   nand4 (w26 w28 w30 w32))
            (g-w48a  (w48a)  and   (c~ w26))
            (g-w48   (w48)   nand4 (w48a w28 w30 w32))
            (g-w49   (w49)   and4  (w25 w28 w30 w32))
            (g-w50   (w50)   and3  (w27 w30 w32))
            (g-w51   (w51)   and   (w29 w32))
            (g-w52   (w52)   buf   (w31))
            (g-w53   (w53)   buf   (w37))
            (g-w54   (w54)   nor   (w38 w39))
            (g-w55   (w55)   nor3  (w40 w41 w42))
            (g-w56   (w56)   nor4  (w43 w44 w45 w46))
            (g-w57   (w57)   nor4  (w49 w50 w51 w52))
            (g-w58   (w58)   xor   (w53 w33))
            (g-w59   (w59)   xor   (w54 w34))
            (g-w60   (w60)   xor   (w55 w35))
            (g-w61   (w61)   xor   (w56 w36))
            (g-w62a  (w62a)  not   (w48))
            (g-w62b  (w62b)  not   (w57))
            (g-w62   (w62)   or    (w62a w62b))
            (g-w63   (w63)   and4  (w58 w59 w60 w61))
            (g-f0    (f0)    buf   (w58))
            (g-f1    (f1)    buf   (w59))
            (g-f2    (f2)    buf   (w60))
            (g-f3    (f3)    buf   (w61))
            (g-a=b   (a=b)   buf   (w63))
            (g-p~    (p~)    buf   (w47))
            (g-cout~ (cout~) buf   (w62))
            (g-g~    (g~)    buf   (w57)))
           )))

(defun f74181-netlist (c~ a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3)
  (let* ((w0  (q-not m))
         (w1  (q-not b0))
         (w2  (q-not b1))
         (w3  (q-not b2))
         (w4  (q-not b3))
         (w5  a0)
         (w6  (q-and b0 s0))
         (w7  (q-and s1 w1))
         (w8  (q-and w1 (q-and s2 a0)))
         (w9  (q-and a0 (q-and s3 b0)))
         (w10 a1)
         (w11 (q-and b1 s0))
         (w12 (q-and s1 w2))
         (w13 (q-and w2 (q-and s2 a1)))
         (w14 (q-and a1 (q-and s3 b1)))
         (w15 a2)
         (w16 (q-and b2 s0))
         (w17 (q-and s1 w3))
         (w18 (q-and w3 (q-and s2 a2)))
         (w19 (q-and a2 (q-and s3 b2)))
         (w20 a3)
         (w21 (q-and b3 s0))
         (w22 (q-and s1 w4))
         (w23 (q-and w4 (q-and s2 a3)))
         (w24 (q-and a3 (q-and s3 b3)))
         (w25 (q-not (q-or w5 (q-or w6 w7))))
         (w26 (q-not (q-or w8 w9)))
         (w27 (q-not (q-or w10 (q-or w11 w12))))
         (w28 (q-not (q-or w13 w14)))
         (w29 (q-not (q-or w15 (q-or w16 w17))))
         (w30 (q-not (q-or w18 w19)))
         (w31 (q-not (q-or w20 (q-or w21 w22))))
         (w32 (q-not (q-or w23 w24)))
         (w33 (q-xor w25 w26))
         (w34 (q-xor w27 w28))
         (w35 (q-xor w29 w30))
         (w36 (q-xor w31 w32))
         (w37 (q-not (q-and w0 c~)))
         (w38 (q-and w0 w25))
         (w39 (q-and w0 (q-and w26 c~)))
         (w40 (q-and w0 w27))
         (w41 (q-and w0 (q-and w25 w28)))
         (w42 (q-and w0 (q-and w28 (q-and w26 c~))))
         (w43 (q-and w0 w29))
         (w44 (q-and w0 (q-and w27 w30)))
         (w45 (q-and w0 (q-and w25 (q-and w30 w28))))
         (w46 (q-and w0 (q-and w30 (q-and w28 (q-and w26 c~)))))
         (w47 (q-not (q-and w26 (q-and w28 (q-and w30 w32)))))
         (w48 (q-not (q-and c~ (q-and w26 (q-and w28 (q-and w30 w32))))))
         (w49 (q-and w25 (q-and w28 (q-and w30 w32))))
         (w50 (q-and w27 (q-and w30 w32)))
         (w51 (q-and w29 w32))
         (w52 w31)
         (w53 w37)
         (w54 (q-not (q-or w38 w39)))
         (w55 (q-not (q-or w40 (q-or w41 w42))))
         (w56 (q-not (q-or w43 (q-or w44 (q-or w45 w46)))))
         (w57 (q-not (q-or w49 (q-or w50 (q-or w51 w52)))))
         (w58 (q-xor w53 w33))
         (w59 (q-xor w54 w34))
         (w60 (q-xor w55 w35))
         (w61 (q-xor w56 w36))
         (w62 (q-or (q-not w48) (q-not w57)))
         (w63 (q-and w58 (q-and w59 (q-and w60 w61))))
         (f0  w58)
         (f1  w59)
         (f2  w60)
         (f3  w61)
         (a=b w63)
         (p~  w47)
         (cout~ w62)
         (g~  w57))
    (list f0 f1 f2 f3 cout~ p~ g~ a=b)))

(defthm net-syntax-okp-f74181-netlist
  (net-syntax-okp *f74181-netlist*)
  :rule-classes nil)

(defthm net-arity-okp-f74181-netlist
  (net-arity-okp *f74181-netlist*)
  :rule-classes nil)

(defthm f74181-netlist-is-same-as-f74181
  (let* ((a (list (qv 6) (qv 8) (qv 10) (qv 12)))
         (b (list (qv 7) (qv 9) (qv 11) (qv 13)))
         (c (qv 5))
         (m (qv 4))
         (s (list (qv 0) (qv 1) (qv 2) (qv 3)))
         (a0 (car a))
         (a1 (cadr a))
         (a2 (caddr a))
         (a3 (cadddr a))
         (b0 (car b))
         (b1 (cadr b))
         (b2 (caddr b))
         (b3 (cadddr b))
         (cin c)
         (s0 (car s))
         (s1 (cadr s))
         (s2 (caddr s))
         (s3 (cadddr s))
         (netlist *f74181-netlist*))
     (equal (se 'f74181
                (list cin a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3)
                nil
                netlist)
            (f74181-netlist cin a0 a1 a2 a3 b0 b1 b2 b3 m s0 s1 s2 s3))))