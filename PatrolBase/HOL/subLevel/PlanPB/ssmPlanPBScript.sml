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
	  "OMNITypeTheory", "PlanPBTypeTheory","ssmPlanPBTheory"];

open TypeBase listTheory optionTheory
     acl_infRules aclDrulesTheory aclrulesTheory
     satListTheory ssmTheory ssminfRules
     OMNITypeTheory PlanPBTypeTheory ssmPlanPBTheory
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
(* this line should be corrected 
(planPBNS WARNO           (exec ([PL tentativePlan;
	  		  	 PSG initiateMovement;
				 PL recon;
				 PL report1]))         = REPORT1)   /\
*)
(planPBNS WARNO           (exec ([PL report1]))        = REPORT1)   /\
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
(* ==== old stateInterp function ===
val stateInterp_def = Define
`stateInterp (slState:slState) =
	     (TT:((slCommand command)option, stateRole, 'd,'e)Form)`
 === End old stateInterp function === *)


(* This function doesn't do anything but is necessary to specialize other    *)
(* theorems.                                                                 *)
val secContextNull_def = Define `
    secContextNull (x:((slCommand command)option, stateRole, 'd,'e)Form list) =
        (TT:((slCommand command)option, stateRole, 'd,'e)Form)`


(* -------------------------------------------------------------------------- *)
(* Security context                                                           *)
(* This is actually a state interpretation function...confused!               *)
(* -------------------------------------------------------------------------- *)
(* === Old way of doing this ====
 ==== End old way of doing this ==== *)
val secList_def = Define
`secList (plCommand:plCommand)(psgCommand:psgCommand) =
	    [((Name PlatoonLeader) controls (prop (SOME (SLc (PL plCommand)))))
	    :((slCommand command)option, stateRole, 'd,'e)Form;
	    ((Name PlatoonSergeant) controls (prop (SOME (SLc (PSG psgCommand)))))
	    :((slCommand command)option, stateRole, 'd,'e)Form]`


(* Make a function to check for elements in the list *)
val getRecon_def = Define `
    (getRecon ([]:((slCommand command)option, stateRole, 'd,'e)Form list) =
    	      [NONE]) /\
    (getRecon (x::xs) = if (x = (Name PlatoonLeader) says (prop (SOME (SLc (PL recon)))))
    	      	        then [SOME (SLc (PL recon))]
			else getRecon xs)`

val getTenativePlan_def = Define `
    (getTenativePlan ([]:((slCommand command)option, stateRole, 'd,'e)Form list) =
    	      [NONE]) /\
    (getTenativePlan (x::xs) = if (x = (Name PlatoonLeader) says (prop (SOME (SLc (PL tentativePlan)))))
    	      	        then [SOME (SLc (PL tentativePlan))]
			else getTenativePlan xs)`

val getReport_def = Define `
    (getReport ([]:((slCommand command)option, stateRole, 'd,'e)Form list) =
    	      [NONE]) /\
    (getReport (x::xs) = if (x = (Name PlatoonLeader) says (prop (SOME (SLc (PL report1)))))
    	      	        then [SOME (SLc (PL report1))]
			else getReport xs)`

val getInitMove_def = Define `
    (getInitMove ([]:((slCommand command)option, stateRole, 'd,'e)Form list) =
    	      [NONE]) /\
    (getInitMove (x::xs) = if (x = (Name PlatoonLeader) says (prop (SOME (SLc (PSG initiateMovement)))))
    	      	        then [SOME (SLc (PSG initiateMovement))]
			else getInitMove xs)`

val getPlCom_def = Define `
    (getPlCom ([]:((slCommand command)option, stateRole, 'd,'e)Form list) =
    	      plIncomplete)
    /\
    (getPlCom (((Name PlatoonLeader) says (prop (SOME (SLc (PL cmd)))))::xs) =
    	      	      cmd)
    /\
    (getPlCom (_::xs) = getPlCom xs)`

val getPsgCom_def = Define `
    (getPsgCom ([]:((slCommand command)option, stateRole, 'd,'e)Form list) =
    	      psgIncomplete)
    /\
    (getPsgCom (((Name PlatoonSergeant) says (prop (SOME (SLc (PSG cmd)))))::xs) =
    	      	      cmd)
    /\
    (getPsgCom (_::xs) = getPsgCom xs)`

(* ==== Failed attempt ====
val secContext_def = Define `
secContext (s:slState) (x:((slCommand command)option, stateRole, 'd,'e)Form list) =
    if (s = WARNO) then
        (if (getRecon         x = [SOME (SLc (PL recon))] ) /\
	    (getTenativePlan  x = [SOME (SLc (PL tentativePlan))]) /\
            (getReport        x = [SOME (SLc (PL report1))]) /\
	    (getInitMove      x = [SOME (SLc (PSG initiateMovement))])
         then [(Name PlatoonLeader) controls prop (SOME (SLc (PL report1)))
	       :((slCommand command)option, stateRole, 'd,'e)Form]
	 else [(prop NONE):((slCommand command)option, stateRole, 'd,'e)Form])
    else (! (plCommand:plCommand) (psgCommand:psgCommand).
        [((Name PlatoonLeader) controls (prop (SOME (SLc (PL plCommand)))))
	    :((slCommand command)option, stateRole, 'd,'e)Form;
         ((Name PlatoonSergeant) controls (prop (SOME (SLc (PSG psgCommand)))))
	    :((slCommand command)option, stateRole, 'd,'e)Form])`
 ==== End Failed Attempt ==== *)
 
val secContext_def = Define `
secContext (s:slState) (x:((slCommand command)option, stateRole, 'd,'e)Form list) =
    if (s = WARNO) then
        (if (getRecon         x = [SOME (SLc (PL recon))] ) /\
	    (getTenativePlan  x = [SOME (SLc (PL tentativePlan))]) /\
            (getReport        x = [SOME (SLc (PL report1))]) /\
	    (getInitMove      x = [SOME (SLc (PSG initiateMovement))])
         then [(Name PlatoonLeader) controls prop (SOME (SLc (PL report1)))
	       :((slCommand command)option, stateRole, 'd,'e)Form]
	 else [(prop NONE):((slCommand command)option, stateRole, 'd,'e)Form])
    else secList (getPlCom x) (getPsgCom x)`


(* ==== New way of doing this ====
=== End new way of doing this ==== *)

(* === Start testing here ====
(* -------------------------------------------------------------------------- *)
(* PlatoonLeader is authorized on any plCommand                               *)
(* -------------------------------------------------------------------------- *)
val PlatoonLeader_exec_plCommand =
let
  val th1 =
  ISPECL
  [``inputOK:((slCommand command)option, stateRole, 'd,'e)Form -> bool``,
  ``secCon :(slState) ->
      ((slCommand command)option, stateRole, 'd,'e)Form list ->
      ((slCommand command)option, stateRole, 'd,'e)Form list``,
  ``stateInterp: (slState) ->
       ((slCommand command)option, stateRole, 'd,'e)Form``,
  ``[(Name PlatoonLeader) says (prop (SOME (SLc (PL plCommand):(slCommand command))))]``,
  ``ins:((slCommand command)option, stateRole, 'd,'e)Form list list``,
  ``(s:slState)``,
  ``outs:(slOutput output list)``] TR_exec_cmd_rule


 ==== End Testing Here ==== *)
val _ = export_theory();

end