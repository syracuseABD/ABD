(* -------------------------------------------------------------------------- *)
(* This is the sequent proof done in "Proofs using sequents"                  *)
(* Author: Shiu-Kai Chin                                                      *)
(* Date September 2016                                                        *)
(* -------------------------------------------------------------------------- *)


(* -------------------------------------------------------------------------- *)
(* We follow the proof in the module exactly                                  *)
(* -------------------------------------------------------------------------- *)
val th1 = ASSUME``A /\ B``;
val th2 = ASSUME``(A \/ C) ==> D``;
val th3 = CONJUNCT1 th1;
val th4 = DISJ1  th3 ``C:bool``;
val th5 = MP th2 th4;
val th6 = CONJ th3 th5;
val th7 = DISCH ``(A \/ C) ==> D`` th6;
val th8 = DISCH ``A /\ B`` th7;