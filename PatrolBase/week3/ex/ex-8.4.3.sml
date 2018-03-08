prove !p q. p /\ q <=> q /\ p;

val conjSymThmAll =
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
 val th11 = IMP_ANTISYM_RULE th5 th10
in
 GENL [``p:bool``, ``q:bool``] th11
end;