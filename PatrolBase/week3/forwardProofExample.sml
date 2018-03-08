

(* -------------------------------------------------------------------------- *)
(* !p q.p ==> (p ==> q) ==> q                                                 *)
(* In this proof, p is an assumption and p ==> q is an assumption.            *)
(* In HOL, we create theorems ASSUMEing p and p ==> q                         *)
(* -------------------------------------------------------------------------- *)
val th1 = ASSUME ``p:bool``

(* -------------------------------------------------------------------------- *)
(* Note that we needed to constrain the type of p to boolean.                 *)
(* -------------------------------------------------------------------------- *)
val th2 = ASSUME ``p ==> q``

(* -------------------------------------------------------------------------- *)
(* Apply MP to th1 and th2                                                    *)
(* -------------------------------------------------------------------------- *)
val th3 = MP th2 th1

(* -------------------------------------------------------------------------- *)
(* We need to discharge the assumptions in the assumption list. We will do    *)
(* this by manipulating the assumptions in theorems th1 and th2.              *)
(* -------------------------------------------------------------------------- *)
val terma = hd (hyp th2)
val th4 = DISCH terma th3
val termb = hd (hyp th1)
val th5 = DISCH termb th4
GENL [``p:bool``,``q:bool``] th5

(* -------------------------------------------------------------------------- *)
(* Make all of our intermediate values and variables local to a proof function*)
(* Do this with let expressions.                                              *)
(* -------------------------------------------------------------------------- *)
val prob1Theorem =
let
  val th1 = ASSUME ``p:bool``
  val th2 = ASSUME ``p ==> q``
  val th3 = MP th2 th1
  val terma = hd (hyp th2)
  val th4 = DISCH terma th3
  val termb = hd (hyp th1)
  val th5 = DISCH termb th4
in
  GENL [``p:bool``,``q:bool``] th5
end

(* -------------------------------------------------------------------------- *)
(* A preview of decision procedures (which you are NOT allowed to use on      *)
(* this assignment)                                                           *)
(* PROVE is a decision procedure that works for 1st-order logic               *)
(* -------------------------------------------------------------------------- *)
val demoTheorem = PROVE [] (concl prob1Theorem)
