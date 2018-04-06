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
    	  "satListTheory","ssmTheory","ssminfRules","uavUtilities",
	  "OMNITypeTheory", "PlanPBTypeTheory","ssmPlanPBTheory"];

open TypeBase listTheory optionTheory
     acl_infRules aclDrulesTheory aclrulesTheory
     satListTheory ssmTheory ssminfRules uavUtilities
     OMNITypeTheory PlanPBTypeTheory ssmPlanPBTheory
 ==== end Interactive Mode ==== *)

open HolKernel Parse boolLib bossLib;
open TypeBase listTheory optionTheory
open acl_infRules aclDrulesTheory aclrulesTheory
open satListTheory ssmTheory ssminfRules uavUtilities
open OMNITypeTheory PlanPBTypeTheory

val _ = new_theory "ssmPlanPB";

(* -------------------------------------------------------------------------- *)
(* Define the next state function for the state machine.                      *)
(* -------------------------------------------------------------------------- *)
val planPBNS_def = Define
`(* exec *)
(planPBNS PLAN_PB         (exec ([PL receiveMission])) = RECEIVE_MISSION) /\
(planPBNS RECEIVE_MISSION (exec ([PL warno]))          = WARNO)     /\ 
(planPBNS WARNO           (exec ([PL recon;
	  		  	 PL tentativePlan;
				 PSG initiateMovement;
				 PL report1]))         = REPORT1)   /\

(*(planPBNS WARNO           (exec ([PL report1]))        = REPORT1)   /\*)
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
        [(TT:((slCommand command)option, stateRole, 'd,'e)Form)]`


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


(* mimick Prof. Chin's C2_L1R1_RB_Auth_def *)
val PL_WARNO_Auth_def = Define `
    PL_WARNO_Auth =
    ^(impfTermList
    [``(prop (SOME (SLc (PL recon))))
         :((slCommand command)option, stateRole, 'd,'e)Form``,
     ``(prop (SOME (SLc (PL tentativePlan))))
         :((slCommand command)option, stateRole, 'd,'e)Form``,
     ``(prop (SOME (SLc (PSG initiateMovement))))
         :((slCommand command)option, stateRole, 'd,'e)Form``,
     ``(Name PlatoonLeader) controls prop (SOME (SLc (PL report1)))
         :((slCommand command)option, stateRole, 'd,'e)Form``]
     ``:((slCommand command)option, stateRole, 'd,'e)Form``)`



val PL_notWARNO_Auth_def = Define `
    PL_notWARNO_Auth (cmd:plCommand) =
    if (cmd = report1)
    then
      (prop NONE):((slCommand command)option, stateRole, 'd,'e)Form
    else
      ((prop (SOME (SLc (PL cmd)))
       :((slCommand command)option, stateRole, 'd,'e)Form) impf
      (((Name PlatoonLeader) controls prop (SOME (SLc (PL cmd))))
      :((slCommand command)option, stateRole, 'd,'e)Form)) `

(* ===== Working section =====
===== End working section ==== *)



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


val context_def = Define `
context (s:slState) (x:((slCommand command)option, stateRole, 'd,'e)Form list) =
    if (s = WARNO) then
        (if (getRecon         x = [SOME (SLc (PL recon))] ) /\
	    (getTenativePlan  x = [SOME (SLc (PL tentativePlan))]) /\
            (getReport        x = [SOME (SLc (PL report1))]) /\
	    (getInitMove      x = [SOME (SLc (PSG initiateMovement))])
         then [PL_WARNO_Auth:((slCommand command)option, stateRole, 'd,'e)Form]
	 else [(prop NONE):((slCommand command)option, stateRole, 'd,'e)Form])
    else [PL_notWARNO_Auth (getPlCom x)]`

(* ==== New way of doing this ====

=== End new way of doing this ==== *)

(* === Start testing here ====
(* -------------------------------------------------------------------------- *)
(* PlatoonLeader is authorized on any plCommand if not in WARNO state         *)
(* -------------------------------------------------------------------------- *)

val tg = ([],fst(dest_imp(concl th1)))
val tgg = set_goal ([], fst(dest_imp(concl th1)))
val PlatoonLeader_notWARNO_exec_plCommand =
let
  val th1 =
  ISPECL
  [``inputOK:((slCommand command)option, stateRole, 'd,'e)Form -> bool``,
  ``secContextNull :((slCommand command)option, stateRole, 'd,'e)Form list ->
      ((slCommand command)option, stateRole, 'd,'e)Form list``,
  ``secContext: (slState) ->
       ((slCommand command)option, stateRole, 'd,'e)Form list ->
      ((slCommand command)option, stateRole, 'd,'e)Form list``,
  ``[((Name PlatoonLeader) says (prop (SOME (SLc (PL plCommand)))))
     :((slCommand command)option, stateRole, 'd,'e)Form]``,
  ``ins:((slCommand command)option, stateRole, 'd,'e)Form list list``,
  ``(s:slState)``,
  ``outs:slOutput output list trType list``] TR_exec_cmd_rule
in
TAC_PROOF(([], fst(dest_imp(concl th1))),
REWRITE_TAC
[CFGInterpret_def, secContext_def, secContextNull_def,
  getRecon_def, getTenativePlan_def, getReport_def, getInitMove_def,
  getPlCom_def, getPsgCom_def, secList_def,
  inputList_def, extractInput_def, MAP,
  extractPropCommand_def, satList_CONS, satList_nil, GSYM satList_conj]

THEN
REWRITE_TAC
[NOT_NONE_SOME, NOT_SOME_NONE, SOME_11, slCommand_one_one,
 slCommand_distinct_clauses, plCommand_distinct_clauses,
 psgCommand_distinct_clauses, slState_distinct_clauses,
 slOutput_distinct_clauses, slRole_distinct_clauses,
 GSYM slState_distinct_clauses,
 GSYM slOutput_distinct_clauses,
 GSYM slRole_distinct_clauses]

THEN
REWRITE_TAC[satList_CONS, satList_nil]
THEN
PROVE_TAC[Controls, Modus_Ponens]





(* -------------------------------------------------------------------------- *)
(* PlatoonLeader is authorized on any report1 if this is the WARNO state and  *)
(*   PlatoonLeader says recon /\      	      	      	     	   	      *)
(*   PlatoonLeader says tentativePlan /\				      *)
(*   PlatoonSergeant says initiateMovement /\				      *)
(*   PlatoonLeader says report1						      *)
(* -------------------------------------------------------------------------- *)
val PlatoonLeader_WARNO_exec_report1 =
let
  val th1w =
  ISPECL
  [``inputOK:((slCommand command)option, stateRole, 'd,'e)Form -> bool``,
  ``secContextNull :((slCommand command)option, stateRole, 'd,'e)Form list ->
                    ((slCommand command)option, stateRole, 'd,'e)Form list``,
  ``secContext: (slState) ->
       ((slCommand command)option, stateRole, 'd,'e)Form list ->
       ((slCommand command)option, stateRole, 'd,'e)Form list``,
  ``[(Name PlatoonLeader) says (prop (SOME (SLc (PL recon))))
      :((slCommand command)option, stateRole, 'd,'e)Form;
     (Name PlatoonLeader) says (prop (SOME (SLc (PL tentativePlan))))
      :((slCommand command)option, stateRole, 'd,'e)Form;
     (Name PlatoonSergeant) says (prop (SOME (SLc (PSG initiateMovement))))
      :((slCommand command)option, stateRole, 'd,'e)Form;
     (Name PlatoonLeader) says (prop (SOME (SLc (PL report1))))
      :((slCommand command)option, stateRole, 'd,'e)Form]``,
  ``ins:((slCommand command)option, stateRole, 'd,'e)Form list list``,
  ``(s:slState)``,
  ``outs:slOutput output list trType list``] TR_exec_cmd_rule
in
 ==== End Testing Here ==== *)
val _ = export_theory();

end