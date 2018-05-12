

(******************************************************************************)
(* OMNIScript								      *)
(* Author: Lori Pickering                                                     *)
(* Date: 10 May 2018                                                          *)
(* This file is intended to allow for integration among the ssms.  The idea   *)
(* is to provide an OMNI-level integrating theory, in the sense of a super-   *)
(* conscious that knows when each ssm is complete and provides that info to   *)
(* higher-level state machines.	      	 	      	       	    	      *)
(******************************************************************************)


structure OMNIScript = struct

(* ==== Interactive Mode =====
app load ["TypeBase","listTheory", "optionTheory",
    	  "OMNITypeTheory",
	  "acl_infRules","aclDrulesTheory","aclrulesTheory"];
open TypeBase listTheory optionTheory
     OMNITypeTheory
     acl_infRules aclDrulesTheory aclrulesTheory
 ====  End Interactive Mode ====  *)

open HolKernel Parse boolLib bossLib;
open TypeBase listTheory optionTheory
open OMNITypeTheory
open acl_infRules aclDrulesTheory aclrulesTheory

val _ = new_theory "OMNI";
(******************************************************************************)
(* Define slCommands for OMNI.						      *)
(******************************************************************************)
(* ==== Area 52 ===========

val _=
Datatype `stateRole = Omni`

val _= 
Datatype `omniCommand = ssmPlanPBComplete
	 	    | ssmMoveToORPComplete
		    | ssmConductORPComplete
		    | ssmMoveToPBComplete
		    | ssmConductPBComplete`

val omniCommand_distinct_clauses = distinct_of``:omniCommand``
val _= save_thm("omniCommand_distinct_clauses",
		 omniCommand_distinct_clauses)

val _=
Datatype `slCommand = OMNI omniCommand`


val omniAuthentication_def = 
Define
`(omniAuthentication
	(Name Omni says prop (cmd:((slCommand command) option))
	:((slCommand command) option, stateRole, 'd,'e)Form) = T) /\
 (omniAuthentication _ = F)`

val omniAuthorization_def =
Define
`(omniAuthorization
	(Name Omni controls prop (cmd:((slCommand command) option))
	:((slCommand command) option, stateRole, 'd,'e)Form) = T) /\
 (omniAuthorization _ = F)`

	

This may not be necessary...But, it is interesting.  Save for a later time.
(******************************************************************************)
(* Prove that								      *)
(*  Omni says omniCommand ==> omniCommand				      *)
(******************************************************************************)

set_goal([],
    ``(Name Omni says prop (cmd:((slCommand command) option))
	:((slCommand command) option, stateRole, 'd,'e)Form) ==>
		     prop (cmd:((slCommand command) option))``)




val th1 = ASSUME``(Name Omni says prop (cmd:((slCommand command) option))
	:((slCommand command) option, stateRole, 'd,'e)Form) = TT``
val th2 = REWRITE_RULE[omniAuthentication_def]th1

 ========= End Area 52 ==== *)

val _= export_theory();
end