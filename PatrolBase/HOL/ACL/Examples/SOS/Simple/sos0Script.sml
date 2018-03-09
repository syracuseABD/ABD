(***********************************************)
(* High-Level Structural Operational Semantics:*)
(* Created by S-K Chin, 19 February 2012       *)
(***********************************************)

(***********
* Load necessary theories
***********)
(* Interactive mode
app load ["listTheory","acl_infRules","foundationTheory"];
*)

structure sos0Script = struct

(* Note: in interactive mode no need to open HolKernel boolLib Parse bossLib *)
open HolKernel boolLib Parse bossLib
open listTheory acl_infRules foundationTheory;

(***********
* create a new theory
***********)
val _ = new_theory "sos0";


(* The simplest model is transitions occur when the *)
(* controller concludes a transition should occur   *)

val (TR0_rules,TR0_ind,TR0_cases) = 
 Hol_reln
  `(((M:(Statements,'worlds,Roles,'Int,'Sec)Kripke),(Oi:'Int po),(Os:'Sec po)) sat ((prop (MODE RDY)):(Statements,Roles,'Int,'Sec)Form) ==>
   TR0 ((M:(Statements,'worlds,Roles,'Int,'Sec)Kripke),(Oi:'Int po),(Os:'Sec po)) STBY RDY) /\
   (((M:(Statements,'worlds,Roles,'Int,'Sec)Kripke),(Oi:'Int po),(Os:'Sec po)) sat ((prop (MODE STBY)):(Statements,Roles,'Int,'Sec)Form) ==>
   TR0 ((M:(Statements,'worlds,Roles,'Int,'Sec)Kripke),(Oi:'Int po),(Os:'Sec po)) RDY STBY)`;

(* Safety property: (TR0 (M,Oi,Os) M1 M2) ==> ((M,Oi,Os) sat (prop (MODE M2))) *)
(* That is, any transition to M2 implies we can justify it in the access       *)
(* control logic.                                                              *)

val SOS0_Security_thm =
TAC_PROOF(
([],
 ``!(M:(Statements,'worlds,Roles,'Int,'Sec)Kripke)(Oi:'Int po)(Os:'Sec po)(M1:modes)(M2:modes).
   (TR0 (M,Oi,Os) M1 M2) ==> ((M,Oi,Os) sat (prop (MODE M2)))``),
(REWRITE_TAC[TR0_cases] THEN
 REPEAT STRIP_TAC THEN 
  ASM_REWRITE_TAC []));

val _ = save_thm("SOS0_Security_thm",SOS0_Security_thm);

val _ = export_theory ();
val _ = print_theory "sos0";

end (* structure *)