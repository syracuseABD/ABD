(* ========================================================================== *)
(* Tests of the eqf substitution rules                                        *)
(* Shiu-Kai Chin                                                              *)
(* 29 June 2014                                                               *)
(* ========================================================================== *)
(* only necessary when working interactively
app load ["acl_infRules","aclDrulesTheory","aclrulesTheory"]
*)

(* The following structure is similar to the module command in Haskell *)
structure eqfScript = struct

open HolKernel boolLib Parse bossLib (* used by Holmake, not in interactive  *)
open acl_infRules aclDrulesTheory aclrulesTheory   (* used by Holmake and interactive mode *)

(***********
* create a new theory
***********)
val _ = new_theory "eqf"

(* -------------------------------------------------------------------------- *)
(* EQF_ANDF1                                                                  *)
(*                                                                            *)
(* EQF_ANDF1 : thm -> thm -> thm                                              *)
(*                                                                            *)
(* SYNOPSIS                                                                   *)
(* Applies eqf_andf1 to substitute an equivalent term for another in the left *)
(* conjunct.                                                                  *)
(*                                                                            *)
(* DESCRIPTION                                                                *)
(*                                                                            *)
(*    A1 |- (M,Oi,Os) sat f eqf f'                                            *)
(*    A2 |- (M,Oi,Os) sat f andf g                                            *)
(* ---------------------------------- EQF_ANDF1                               *)
(* A1 u A2 |- (M,Oi,Os) sat f' andf g                                         *)
(*                                                                            *)
(* FAILURE                                                                    *)
(* Fails unless the first theorem is an equivance and the second theorem is   *)
(* a conjunction.  Fails unless all the types are consistent.                 *)
(* -------------------------------------------------------------------------- *)
val EQF_ANDF1_Test =
let
 val th1 = ACL_ASSUM``(p1 eqf p1'):('a,'c,'d,'e)Form``
 val th2 = ACL_ASSUM``(p1 andf p2):('a,'c,'d,'e)Form``
 val th3 = EQF_ANDF1 th1 th2
 val th4 = DISCH (hd(hyp th2)) th3
in
 DISCH(hd(hyp th1)) th4
end

(* -------------------------------------------------------------------------- *)
(* EQF_ANDF2                                                                  *)
(*                                                                            *)
(* EQF_ANDF2 : thm -> thm -> thm                                              *)
(*                                                                            *)
(* SYNOPSIS                                                                   *)
(* Applies eqf_andf2 to substitute an equivalent term for another in the left *)
(* conjunct.                                                                  *)
(*                                                                            *)
(* DESCRIPTION                                                                *)
(*                                                                            *)
(*    A1 |- (M,Oi,Os) sat f eqf f'                                            *)
(*    A2 |- (M,Oi,Os) sat f andf g                                            *)
(* ---------------------------------- EQF_ANDF2                               *)
(* A1 u A2 |- (M,Oi,Os) sat f' andf g                                         *)
(*                                                                            *)
(* FAILURE                                                                    *)
(* Fails unless the first theorem is an equivance and the second theorem is   *)
(* a conjunction.  Fails unless all the types are consistent.                 *)
(* -------------------------------------------------------------------------- *)
val EQF_ANDF2_Test =
let
 val th1 = ACL_ASSUM``(p2 eqf p2'):('a,'c,'d,'e)Form``
 val th2 = ACL_ASSUM``(p1 andf p2):('a,'c,'d,'e)Form``
 val th3 = EQF_ANDF2 th1 th2
 val th4 = DISCH (hd(hyp th2)) th3
in
 DISCH(hd(hyp th1)) th4
end

(*******************************)
(* Print and export the theory *)
(*******************************)
val _ = print_theory "-";

val _ = export_theory();

end (* structure *)
