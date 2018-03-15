(*************************************************)
(* repsExample: Shiu-Kai Chin, 19 September 2012 *)
(* Partners: none                                *)
(* Acknowledgements:                             *)
(*  (1) Reps proof from acdDrulesScript.sml      *)
(*  (2) REPS inference rule from acl_infRules.sml*)
(*************************************************)

(* Interactive mode
app load ["pred_setTheory", "pred_setLib", "relationTheory", 
          "aclfoundationTheory","aclsemanticsTheory", 
          "aclrulesTheory","aclDrulesTheory","acl_infRules"];
*)


(*********Load the theories on which the inference rules are based******)
open HolKernel boolLib Parse;
open bossLib pred_setLib pred_setTheory;
open aclfoundationTheory aclsemanticsTheory aclrulesTheory;
open aclDrulesTheory relationTheory acl_infRules;

(* The proof for Reps *)
(*****************************
* Reps
*
*  Q controls f    reps P Q f    P quoting Q says f
*   --------------------------------------------
*                                  f
*****************************)
val Reps = 
let
	val a1 = ACL_ASSUM ``(Q:'c Princ) controls (f:('a,'c,'d,'e)Form) ``
	val a2 = ACL_ASSUM ``reps (P:'c Princ) (Q:'c Princ) (f:('a,'c,'d,'e)Form)``
	val a3 = ACL_ASSUM ``((P:'c Princ) quoting (Q:'c Princ)) says (f:('a,'c,'d,'e)Form)``
	val th4 = REWRITE_RULE [Reps_Eq] a2
	val th5 = ACL_MP a3 th4
	val th6 = REWRITE_RULE [Controls_Eq] a1
	val th7 = ACL_MP th5 th6
	val th8 = GENL [``(M :('a, 'b, 'c, 'd, 'e) Kripke)``,``(Oi :'d po)``,``(Os :'e po)``,
	               	     ``(P :'c Princ)``,``(Q: 'c Princ)``,``(f :('a, 'c, 'd, 'e) Form)``]
		      	     (DISCH_ALL th7)
in
	save_thm("Reps",th8)
end;

(* The inference rule REPS *)
(***********************************************************
* REPS
*
* REPS : thm -> thm -> thm -> thm
*
* SYNOPSIS
* Concludes statement f given theorems on delegation, quoting, and 
* jurisdiction.
*
* DESCRIPTION
*
* A1 |- (M,Oi,Os) sat reps P Q f  A2 |- (M,Oi,Os) sat (P quoting Q) says f
*                            A3 |- (M,Oi,Os) sat Q controls f
*     --------------------------------------------------------  REPS
*                             A1 u A2 u A3 |- (M,Oi,Os) sat f
*
* FAILURE
* Fails unless M, Oi, Os, P, Q, and f match in all three theorems.
***********************************************************)
fun REPS th1 th2 th3 = 
    MATCH_MP(MATCH_MP (MATCH_MP (SPEC_ALL Reps) th1) th2) th3;


(****************************************************************)
(* We prove the Delegates theorem using the REPS inference rule *)
(****************************************************************)
val Delegates = 
let
	val term = ``(R1:'c Princ) quoting (R2:'c Princ)``
	val a1 = ACL_ASSUM ``(Q:'c Princ) controls (f:('a,'c,'d,'e)Form) ``
	val a2 = ACL_ASSUM ``reps (P:'c Princ) (Q:'c Princ) (f:('a,'c,'d,'e)Form)``
	val a3 = ACL_ASSUM ``((P:'c Princ) quoting (Q:'c Princ)) says (f:('a,'c,'d,'e)Form)``
	val a4 = ACL_ASSUM ``(f impf g):('a,'c,'d,'e)Form``
	val th1 = REPS a2 a3 a1
	val th2 = ACL_MP th1 a4
	val th3 = SAYS term th2
in
	GENL [``(R1 :'c Princ)``,``(R2: 'c Princ)``,``(M :('a, 'b, 'c, 'd, 'e) Kripke)``,
              ``(Oi :'d po)``,``(Os :'e po)``,``(P :'c Princ)``,``(Q: 'c Princ)``,
              ``(f :('a, 'c, 'd, 'e) Form)``,``(g :('a, 'c, 'd, 'e) Form)``]
	     (DISCH_ALL th3)
end;

(*****************************************************************************)
(* Important implementation detail:                                          *)
(* Note the use of ISPECL instead of SPECL as ISPECL does type instantiation *)
(*****************************************************************************)
fun DELEGATES P Role th1 th2 th3 th4 = 
    MATCH_MP(MATCH_MP (MATCH_MP (MATCH_MP(SPEC_ALL (ISPECL [P,Role] Delegates)) th1) th2) th3) th4;

(*********************************************************************)
(* An example of Bob as Blue Forces Operator receiving Alice's order *)
(* and ordering a launch.                                            *)
(*********************************************************************)
val person = ``(Bob:'pName Princ)``;
val role = ``(Operator:'pName Princ)``;
val repsThm = ACL_ASSUM``(reps Alice BFC go):('prop,'pName,'Int,'Sec)Form``;
val goThm = ACL_ASSUM``((Alice quoting BFC) says go):('prop,'pName,'Int,'Sec)Form``;
val policyThm = ACL_ASSUM``(go impf launch):('prop,'pName,'Int,'Sec)Form``;
val jurisdictionThm = ACL_ASSUM``(BFC controls go):('prop,'pName,'Int,'Sec)Form``;
val launchThm = 
 DELEGATES person role repsThm goThm policyThm jurisdictionThm;

