(********************************************************)
(* Lab 8                                                *)
(* Shiu-Kai Chin                                        *)
(* 19 September 2013                                    *)
(* Make sure you turn off unicode, turn on assumptions, *)
(* and turn on types as needed!                         *)
(********************************************************)

(***********************************)
(* Example 1: The simplest theorem *)
(***********************************)
TRUTH;

(***********************************)
(* Example 2: decomposing theorems *)
(***********************************)
hyp;
concl;

hyp TRUTH;
concl TRUTH;

(***************************)
(* Example 3: using ASSUME *)
(***************************)
val th1 = ASSUME``t:bool``;
val asList = hyp th1;
val concl1 = concl th1;

(**************************)
(* Example 4: using DISCH *)
(**************************)
val th1 = ASSUME ``p:bool``;
val th2 = DISCH``p:bool`` th1;
DISCH (hd(hyp th1)) th1;

val th1 = ``foo``;

(*************************)
(* Example 5: tidying up *)
(*************************)
val example5Thm =
let
 val theorem1 = ASSUME ``p:bool``
in
 DISCH(hd(hyp theorem1)) theorem1
end;

(*************)
(* Example 6 *)
(*************)
(* Interactively do the proof *)
val th1 = ASSUME``A /\ B``;
val th2 = ASSUME``(A \/ C) ==> D``;
val th3 = CONJUNCT1 th1;
val th4 = DISJ1 th3 ``C:bool``;
val th5 = MP th2 th4;
val th6 = DISCH (hd(hyp(th2))) th5;
val th7 = DISCH (hd(hyp(th1))) th6;

(***********************************)
(* Package it up into one function *)
(***********************************)
val example6Thm =
let
 val th1 = ASSUME``A /\ B``
 val th2 = ASSUME``(A \/ C) ==> D``
 val th3 = CONJUNCT1 th1
 val th4 = DISJ1 th3 ``C:bool``
 val th5 = MP th2 th4
 val th6 = DISCH (hd(hyp(th2))) th5
in
 DISCH (hd(hyp(th1))) th6
end;

(************************************************)
(* Example 7: introducing universal quantifiers *)
(************************************************)
val example7Thm = 
 GENL [``A:bool``,``B:bool``,``C:bool``,``D:bool``] example6Thm;
 