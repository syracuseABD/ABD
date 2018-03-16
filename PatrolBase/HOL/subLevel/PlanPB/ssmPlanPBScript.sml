(******************************************************************************)
(* ssmPlanPB describes the secure state machine derived from the PLAN_PB      *)
(* state at the top-level.  This is the first secure state machine to use the *)
(* new ssm parameterizable secure state machine.     	   	              *)
(* Contributors: Lori Pickering (HOL Implementation)			      *)
(* 		 Jesse Nathaniel Hall (subject matter)			      *)
(******************************************************************************)

structure ssmPlanPBScript = struct

(* ===== Interactive Mode ====
app load  ["TypeBase", "listTheory","optionTheory",
          "acl_infRules","aclDrulesTheory","aclrulesTheory",
    	  "satListTheory","ssmTheory","ssminfRules",
	  "OMNITypeTheory", "PlanPBTypeTheory"];

open TypeBase listTheory optionTheory
     acl_infRules aclDrulesTheory aclrulesTheory
     satListTheory ssmTheory ssminfRules
     OMNITypeTheory PlanPBTypeTheory
 ==== end Interactive Mode ==== *)

open HolKernel Parse boolLib bossLib;
open TypeBase listTheory optionTheory
open acl_infRules aclDrulesTheory aclrulesTheory
open satListTheory ssmTheory ssminfRules
open OMNITypeTheory PlanPBTypeTheory

val _ = new_theory "ssmPlanPB";

(* -------------------------------------------------------------------------- *)
(* Define the next state function for the state machine.                      *)
(* -------------------------------------------------------------------------- *)
val planPBNS_def = Define
`(* exec *)
(planPBNS PLAN_PB         (exec ([PL receiveMission])) = RECEIVE_MISSION) /\
(planPBNS RECEIVE_MISSION (exec ([PL warno]))          = WARNO)     /\ 
(planPBNS WARNO           (exec ([PL tentativePlan;
	  		  	 PSG initiateMovement;
				 PL recon]))           = REPORT1)   /\
(planPBNS REPORT1         (exec ([PL completePlan]))   = COMPLETE_PLAN) /\
(planPBNS COMPLETE_PLAN   (exec ([PL opoid]))          = OPOID)     /\
(planPBNS OPOID           (exec ([PL supervise]))      = SUPERVISE) /\
(planPBNS SUPERVISE       (exec ([PL report2]))        = REPORT2)   /\
(planPBNS REPORT2         (exec ([PL complete]))       = COMPLETE)  /\
(planPBNS (s:slState)     (trap ([PL  plCommand]))     = s)         /\
(planPBNS (s:slState)     (trap ([PSG psgCommand]))    = s)         /\
(planPBNS (s:slState)     (discard ([PL  plCommand]))  = s)         /\
(planPBNS (s:slState)     (discard ([PSG psgCommand])) = s)`


val planPBOut_def = Define
`(* exec *)
(planPBOut PLAN_PB         (exec ([PL receiveMission])) = ReceiveMission) /\
(planPBOut RECEIVE_MISSION (exec ([PL warno]))          = Warno)     /\ 
(planPBOut WARNO           (exec ([PL tentativePlan;
	  		  	 PSG initiateMovement;
				 PL recon]))            = Report1)   /\
(planPBOut REPORT1         (exec ([PL completePlan]))   = CompletePlan) /\
(planPBOut COMPLETE_PLAN   (exec ([PL opoid]))          = Opoid)     /\
(planPBOut OPOID           (exec ([PL supervise]))      = Supervise) /\
(planPBOut SUPERVISE       (exec ([PL report2]))        = Report2)   /\
(planPBOut REPORT2         (exec ([PL complete]))       = Complete)  /\
(planPBOut (s:slState)     (trap ([PL  plCommand]))     = unAuthorized) /\
(planPBOut (s:slState)     (trap ([PSG psgCommand]))    = unAuthorized) /\
(planPBOut (s:slState)     (discard ([PL  plCommand]))  = unAuthenticated) /\
(planPBOut (s:slState)     (discard ([PSG psgCommand])) = unAuthenticated)`



(* -------------------------------------------------------------------------- *)
(* Define authentication test                                                 *)
(* -------------------------------------------------------------------------- *)
val authenticationTest_def = Define
`(authenticationTest
	(((Name PlatoonLeader) says (prop  (cmd:((slCommand command)option))))
	       :((slCommand command)option, stateRole, 'd,'e)Form) = T)  /\

(authenticationTest
	(((Name PlatoonSergeant) says (prop  (cmd:((slCommand command)option))))
	       :((slCommand command)option, stateRole, 'd,'e)Form) = T)  /\
(authenticationTest _ = F)`

val authenticationTest_cmd_reject_lemma =
TAC_PROOF(
  ([],
   ``!cmd. ~(authenticationTest
   	   ((prop (SOME cmd)):((slCommand command)option, stateRole, 'd,'e)Form))``),
  PROVE_TAC[authenticationTest_def])

(* ==== Testing here ====
(* -------------------------------------------------------------------------- *)
(* Define authentication test                                                 *)
(* -------------------------------------------------------------------------- *)
 ==== End Testing Here ==== *)
val _ = export_theory();

end