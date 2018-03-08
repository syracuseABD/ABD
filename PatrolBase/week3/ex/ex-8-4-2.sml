Prove p /\ q <=> q /\ p

val th1 = ASSUME ``p /\ q``;
val th2 = CONJUNCT1 th1;
val th3 = CONJUNCT2 th1;
val th4 = CONJ th3 th2;
val th5 = DISCH (hd(hyp(th1))) th4;
val th6 = ASSUME ``q /\ p``;
val th7 = CONJUNCT1 th6;
val th8 = CONJUNCT2 th6;
val th9 = CONJ th8 th7;
val th10 = DISCH (hd(hyp(th6))) th9;
val th11 = IMP_ANTISYM_RULE th5 th10;





%%val th3 = IMP_ANTISYM_RULE th1 th2;
%%val th4 = DISCH (hd(hyp(th2))) th3;
%%val th5 = DISCH (hd(hyp(th1))) th4;

val conjSymThm =
let
 val th1 = ASSUME ``p /\ q``
 val th2 = CONJUNCT1 th1
 val th3 = CONJUNCT2 th1
 val th4 = CONJ th3 th2
 val th5 = DISCH (hd(hyp(th1))) th4
 val th6 = ASSUME ``q /\ p``
 val th7 = CONJUNCT1 th6
 val th8 = CONJUNCT2 th6
 val th9 = CONJ th8 th7
 val th10 = DISCH (hd(hyp(th6))) th9
in
 IMP_ANTISYM_RULE th5 th10
end;