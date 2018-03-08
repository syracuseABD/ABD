prove problem1Thm  p ==> (p ==> q) ==> (q ==> r) ==>r

val th1 = ASSUME ``p:bool``;
val th2 = ASSUME ``p ==> q``;
val th3 = MP th2 th1;
val th4 = ASSUME ``q ==> r``;
val th5 = MP th4 th3;
val th6 = DISCH (hd(hyp(th4))) th5;
val th7 = DISCH (hd(hyp(th2))) th6;
val th8 = DISCH (hd(hyp(th1))) th7;

val problem1Thm =
let
 val th1 = ASSUME ``p:bool``
 val th2 = ASSUME ``p ==> q``
 val th3 = MP th2 th1
 val th4 = ASSUME ``q ==> r``
 val th5 = MP th4 th3
 val th6 = DISCH (hd(hyp(th4))) th5
 val th7 = DISCH (hd(hyp(th2))) th6
in
 DISCH (hd(hyp(th1))) th7
end;