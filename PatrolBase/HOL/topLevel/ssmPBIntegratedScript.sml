(******************************************************************************)
(* ssmPBIntegratedTheory                                                      *)
(* Author: Lori Pickering                                                     *)
(* Date: 7 May 2018                                                           *)
(* This theory aims to integrate the topLevel ssm with the sublevel ssms.  It *)
(* does this by adding a condition to the security context.  In particular,   *)
(* it requires that the "COMPLETE" state in the subLevel ssm must preceede    *)
(* transition to the next state at the topLeve.  I.e.,                        *)
(*   planPBComplete ==>                                                       *)
(*   PlatoonLeader controls crossLD.                                          *)
(* In the ssmPlanPB ssm, the last state is COMPLETE.  This is reached when the*)
(* the appropriate authority says complete and the transition is made.        *)
(* Note that following the ACL, if P says x and P controls x, then x.         *)
(* Therefore, it is not necessary for anyone to say x at the topLevel, because*)
(* it is already proved at the lower level.                                   *)
(* However, indicating that at the topLevel remains something to workout.     *)
(******************************************************************************)


structure ssmPBIntegratedScript = struct

(* ===== Interactive Mode ====
app load  ["TypeBase", "listTheory","optionTheory","listSyntax",
          "acl_infRules","aclDrulesTheory","aclrulesTheory",
	  "aclsemanticsTheory", "aclfoundationTheory",
    	  "satListTheory","ssmTheory","ssminfRules","uavUtilities",
	  "OMNITypeTheory", "PBTypeIntegratedTheory","PBIntegratedDefTheory",
	  "ssmPBIntegratedTheory"];

open TypeBase listTheory optionTheory listSyntax
     acl_infRules aclDrulesTheory aclrulesTheory
     aclsemanticsTheory aclfoundationTheory
     satListTheory ssmTheory ssminfRules uavUtilities
     OMNITypeTheory PBTypeIntegratedTheory PBIntegratedDefTheory
     ssmPBIntegratedTheory
 ==== end Interactive Mode ==== *)

open HolKernel Parse boolLib bossLib;
open TypeBase listTheory optionTheory 
open acl_infRules aclDrulesTheory aclrulesTheory
open satListTheory ssmTheory ssminfRules uavUtilities
open OMNITypeTheory PBTypeIntegratedTheory PBIntegratedDefTheory


val _ = new_theory  "ssmPBIntegrated";


(******************************************************************************)
(* Define next-state and next-output functions                                *)
(******************************************************************************)
val PBNS_def =
Define`
(PBNS PLAN_PB     (exec [SOME (SLc (PL crossLD))])    = MOVE_TO_ORP) /\
(PBNS MOVE_TO_ORP (exec [SOME (SLc (PL conductORP))]) = CONDUCT_ORP) /\
(PBNS CONDUCT_ORP (exec [SOME (SLc (PL moveToPB))])   = MOVE_TO_PB)  /\
(PBNS MOVE_TO_PB  (exec [SOME (SLc (PL conductPB))]) =  CONDUCT_PB)  /\
(PBNS CONDUCT_PB  (exec [SOME (SLc (PL completePB))]) = COMPLETE_PB) /\
(PBNS (s:slState) (trap _)    = s) /\
(PBNS (s:slState) (discard _) = s)`

val PBOut_def =
Define`
(PBOut PLAN_PB     (exec [SOME (SLc (PL crossLD))])    = MoveToORP) /\
(PBOut MOVE_TO_ORP (exec [SOME (SLc (PL conductORP))]) = ConductORP) /\
(PBOut CONDUCT_ORP (exec [SOME (SLc (PL moveToPB))])   = MoveToPB)  /\
(PBOut MOVE_TO_PB  (exec [SOME (SLc (PL conductPB))]) =  ConductPB)  /\
(PBOut CONDUCT_PB  (exec [SOME (SLc (PL completePB))]) = CompletePB) /\
(PBOut (s:slState) (trap _)    = unAuthorized) /\
(PBOut (s:slState) (discard _) = unAuthenticated)`

(******************************************************************************)
(* Define authentication function                                             *)
(******************************************************************************)
val inputOK_def =
Define`
(inputOK (((Name PlatoonLeader) says prop (cmd:((slCommand command)option)))
	   :((slCommand command)option, stateRole,'d,'e)Form) = T) /\
(inputOK (((Name Omni)          says prop (cmd:((slCommand command)option)))
	   :((slCommand command)option, stateRole,'d,'e)Form) = T) /\
(inputOK _ = F)`


(******************************************************************************)
(* Prove that commands are rejected unless that are requested by a properly   *)
(* authenticated principal. 	    	   	    	      	   	      *)
(******************************************************************************)

val inputOK_cmd_reject_lemma =
Q.prove(`!cmd. ~(inputOK
	         ((prop (SOME cmd))))`,
		 	      (PROVE_TAC[inputOK_def]))



(* ===== Just playing around with this ====
val inputOK_not_reject_lemma =
Q.prove(`!cmd.
        ~(
	  (inputOK (((Name PlatoonLeader) says prop (cmd:((slCommand command)option)))
	   :((slCommand command)option, stateRole,'d,'e)Form)) \/
	  (inputOK (((Name Omni)          says prop (cmd:((slCommand command)option)))
	   :((slCommand command)option, stateRole,'d,'e)Form)))

 ==== OK, done fooling around ==== *)


val _ = export_theory();

end