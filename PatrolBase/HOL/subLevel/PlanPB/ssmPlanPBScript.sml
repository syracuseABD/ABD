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
val inputOK_def = Define
`(inputOK
	(((Name PlatoonLeader) says (prop  (cmd:((slCommand command)option))))
	       :((slCommand command)option, stateRole, 'd,'e)Form) = T)  /\
(inputOK
	(((Name PlatoonSergeant) says (prop  (cmd:((slCommand command)option))))
	       :((slCommand command)option, stateRole, 'd,'e)Form) = T)  /\
(inputOK _ = F)`

val inputOK_cmd_reject_lemma =
TAC_PROOF(
  ([],
   ``!cmd. ~(inputOK
   	   ((prop (SOME cmd)):((slCommand command)option, stateRole, 'd,'e)Form))``),
  PROVE_TAC[inputOK_def])


(* -------------------------------------------------------------------------- *)
(* state Interpretation function                                              *)
(* -------------------------------------------------------------------------- *)
val stateInterp_def = Define
`stateInterp (slState:slState) =
	     (TT:((slCommand command)option, stateRole, 'd,'e)Form)`


(* -------------------------------------------------------------------------- *)
(* Security context                                                           *)
(* -------------------------------------------------------------------------- *)
val secContext_def = Define
`secContext (plCommand:plCommand)(psgCommand:psgCommand) =
	    [((Name PlatoonLeader) controls (prop (SOME (SLc (PL plCommand)))))
	    :((slCommand command)option, stateRole, 'd,'e)Form;
	    ((Name PlatoonSergeant) controls (prop (SOME (SLc (PSG psgCommand)))))
	    :((slCommand command)option, stateRole, 'd,'e)Form]`

(* ==== Testing here ====
(* -------------------------------------------------------------------------- *)
(* PlatoonLeader is authorized on any plCommand                               *)
(* -------------------------------------------------------------------------- *)
val PlatoonLeader_exec_plCommand =
let
  val th1 =
  ISPECL
  [``inputOK:((slCommand command)option, stateRole, 'd,'e)Form -> bool``,
  ``secContext (plCommand:plCommand)(psgCommand:psgCommand):
       ((slCommand command)option, stateRole, 'd,'e)Form list``,
  ``stateInterp: slState ->
       ((slCommand command)option, stateRole, 'd,'e)Form``,
  ``[(Name PlatoonLeader) says (prop (SOME (plCommand:plCommand)))]``
  ``ins:((slCommand command)option, stateRole, 'd,'e)Form list list``,
  ``(s:slState)``,
  ``outs:(slOutput output trType list)``     `,
] 


 ==== End Testing Here ==== *)
val _ = export_theory();

end