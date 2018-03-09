

(* ========================================================================== *)
(* Chapter 3 exercises                                                        *)
(* Shiu-Kai Chin                                                              *)
(* 22 June 2014                                                               *)
(* ========================================================================== *)
(* only necessary when working interactively
app load ["acl_infRules","aclDrulesTheory","aclrulesTheory"]
*)

(* The following structure is similar to the module command in Haskell *)
structure chapter3Script = struct

open HolKernel boolLib Parse bossLib (* used by Holmake, not in interactive  *)
open acl_infRules aclDrulesTheory aclrulesTheory   (* used by Holmake and interactive mode *)

(***********
* create a new theory
***********)
val _ = new_theory "chapter3"



(* -------------------------------------------------------------------------- *)
(* Exercise 3.2.1                                                             *)
(* Shiu-Kai Chin                                                              *)
(* 22 June 2014                                                               *)
(* -------------------------------------------------------------------------- *)
val exercise3_2_1_thm =
let
 val th1 = ACL_ASSUM``(p1 impf p2):('a,'c,'d,'e)Form``
 val th2 = ACL_ASSUM``(p2 impf p3):('a,'c,'d,'e)Form``
 val th3 = ACL_TAUT``((p1 impf p2) impf ((p2 impf p3) impf (p1 impf p3))):('a,'c,'d,'e)Form``
 val th4 = ACL_MP th1 th3
 val th5 = ACL_MP th2 th4
 val th6 = DISCH(hd(hyp th2)) th5
in
 DISCH(hd(hyp th1)) th6
end

val _ = save_thm("exercise3_2_1_thm",exercise3_2_1_thm)



(* -------------------------------------------------------------------------- *)
(* Exercise 3.2.3                                                             *)
(* Shiu-Kai Chin                                                              *)
(* 22 June 2014                                                               *)
(* -------------------------------------------------------------------------- *)
val exercise3_2_3_thm =
let
 val th1 = ACL_ASSUM``(P speaks_for Q):('a,'c,'d,'e)Form``
 val th2 = ACL_ASSUM``(P says f):('a,'c,'d,'e)Form``
 val th3 = SPEC_ALL Speaks_For
 val th4 = ACL_MP th1 th3
 val th5 = ACL_MP th2 th4
 val th6 = DISCH(hd(hyp th2)) th5
in
 DISCH(hd(hyp th1)) th6
end

val _ = save_thm("exercise3_2_3_thm",exercise3_2_3_thm)



(* -------------------------------------------------------------------------- *)
(* Exercise 3.2.4                                                             *)
(* Shiu-Kai Chin                                                              *)
(* 22 June 2014                                                               *)
(* -------------------------------------------------------------------------- *)
val exercise3_2_4_thm =
let
 val th1 = ACL_ASSUM``(P speaks_for Q):('a,'c,'d,'e)Form``
 val th2 = ACL_ASSUM``(Q controls f):('a,'c,'d,'e)Form``
 val th3 = SPEC_ALL Speaks_For
 val th4 = ACL_MP th1 th3
 val th5 = REWRITE_RULE[Controls_Eq]th2
 val th6 = HS th4 th5
 val th7 = REWRITE_RULE[GSYM Controls_Eq] th6
 val th8 = DISCH(hd(hyp th2))th7
in
 DISCH(hd(hyp th1))th8
end

val _ = save_thm("exercise3_2_4_thm",exercise3_2_4_thm)

(*******************************)
(* Print and export the theory *)
(*******************************)
val _ = print_theory "-";

val _ = export_theory();

end (* structure *)
