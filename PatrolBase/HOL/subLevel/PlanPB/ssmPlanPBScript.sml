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
	  "aclsemanticsTheory", "aclfoundationTheory",
    	  "satListTheory","ssmTheory","ssminfRules","uavUtilities",
	  "OMNITypeTheory", "PlanPBTypeTheory","ssmPlanPBTheory"];

open TypeBase listTheory optionTheory
     acl_infRules aclDrulesTheory aclrulesTheory
     aclsemanticsTheory aclfoundationTheory
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

(*  Version 2, using if-then statements *)
(* ==== this would be easier with sequential statements used
;
val planPBNS_def = Define `
(planPBNS WARNO (exec x) =
   if ((getRecon        x = [SOME (SLc (PL recon))] )        /\
      (getTenativePlan  x = [SOME (SLc (PL tentativePlan))]) /\
      (getReport        x = [SOME (SLc (PL report1))])       /\
      (getInitMove      x = [SOME (SLc (PSG initiateMovement))] ))
   then REPORT1
   else WARNO) /\
(planPBNS PLAN_PB         (exec ([(PL receiveMission)])) = RECEIVE_MISSION) /\
(planPBNS RECEIVE_MISSION (exec ([ (PL warno)]))          = WARNO)          /\ 
(planPBNS REPORT1         (exec ([ (PL completePlan)]))   = COMPLETE_PLAN)  /\
(planPBNS COMPLETE_PLAN   (exec ([ (PL opoid)]))          = OPOID)          /\
(planPBNS OPOID           (exec ([(PL supervise)]))      = SUPERVISE)       /\
(planPBNS SUPERVISE       (exec ([ (PL report2)]))        = REPORT2)   /\
(planPBNS REPORT2         (exec ([ (PL complete)]))       = COMPLETE)  /\
(planPBNS (s:slState)     (trap ([ (PL  plCommand)]))     = s)         /\
(planPBNS (s:slState)     (trap ([ (PSG psgCommand)]))    = s)         /\
(planPBNS (s:slState)     (discard ([ (PL  plCommand)]))  = s)         /\
(planPBNS (s:slState)     (discard ([ (PSG psgCommand)])) = s)`


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
 === This would be easier with sequential statements used ==== *)
(* -------------------------------------------------------------------------- *)
(* authentication test function                                               *)
(* -------------------------------------------------------------------------- *)
val inputOK_def = Define
`(inputOK
	(((Name PlatoonLeader) says (prop  (cmd:((slCommand command)option))))
	       :((slCommand command)option, stateRole, 'd,'e)Form) = T)  /\
(inputOK
	(((Name PlatoonSergeant) says (prop  (cmd:((slCommand command)option))))
	       :((slCommand command)option, stateRole, 'd,'e)Form) = T)  /\
(inputOK _ = F)`

(* Any unauthorized command is rejected                                       *)
val inputOK_cmd_reject_lemma =
TAC_PROOF(
  ([],
   ``!cmd. ~(inputOK
   	   ((prop (SOME cmd)):((slCommand command)option, stateRole, 'd,'e)Form))``),
  PROVE_TAC[inputOK_def])


(* -------------------------------------------------------------------------- *)
(* state Interpretation function                                              *)
(* -------------------------------------------------------------------------- *)
(* This function doesn't do anything but is necessary to specialize other     *)
(* theorems.                                                                  *)
val secContextNull_def = Define `
    secContextNull (x:((slCommand command)option, stateRole, 'd,'e)Form list) =
        [(TT:((slCommand command)option, stateRole, 'd,'e)Form)]`


(* -------------------------------------------------------------------------- *)
(* Security context                                                           *)           
(* -------------------------------------------------------------------------- *)
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
    if (cmd = report1) (* report1 exits WARNO state *)
    then
      (prop NONE):((slCommand command)option, stateRole, 'd,'e)Form
    else
      ((Name PlatoonLeader) says (prop (SOME (SLc (PL cmd)))
       :((slCommand command)option, stateRole, 'd,'e)Form) impf
      (((Name PlatoonLeader) controls prop (SOME (SLc (PL cmd))))
      :((slCommand command)option, stateRole, 'd,'e)Form)) `


(* Make a function to check for elements in the list *)
val getRecon_def = Define `
    (getRecon ([]:((slCommand command)option, stateRole, 'd,'e)Form list) =
    	      [NONE]) /\
    (getRecon ((Name PlatoonLeader) says (prop (SOME (SLc (PL recon))))::xs)
    	      	        = [SOME (SLc (PL recon))]) /\
    (getRecon (_::xs) = getRecon xs)`

val getTenativePlan_def = Define `
    (getTenativePlan ([]:((slCommand command)option, stateRole, 'd,'e)Form list) =
    	      [NONE]) /\
    (getTenativePlan ((Name PlatoonLeader) says (prop (SOME (SLc (PL tentativePlan))))::xs)
    	      	        = [SOME (SLc (PL tentativePlan))]) /\
    (getTenativePlan (_::xs) =  getTenativePlan xs)`

val getReport_def = Define `
    (getReport ([]:((slCommand command)option, stateRole, 'd,'e)Form list) =
    	      [NONE]) /\
    (getReport (((Name PlatoonLeader) says (prop (SOME (SLc (PL report1)))))::xs)
    	      	       =  [SOME (SLc (PL report1))]) /\
    (getReport (_::xs) = getReport xs)`

val getInitMove_def = Define `
    (getInitMove ([]:((slCommand command)option, stateRole, 'd,'e)Form list) =
    	      [NONE]) /\
    (getInitMove ((Name Sergeant) says (prop (SOME (SLc (PSG initiateMovement))))::xs)
    	      	     = [SOME (SLc (PSG initiateMovement))]) /\
    (getInitMove (_::xs) = getInitMove xs)`

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


val context_def = Define `
context (s:slState) (x:((slCommand command)option, stateRole, 'd,'e)Form list) =
    if (s = WARNO) then
        (if (getRecon         x = [SOME (SLc (PL recon))] ) /\
	    (getTenativePlan  x = [SOME (SLc (PL tentativePlan))]) /\
            (getReport        x = [SOME (SLc (PL report1))]) /\
	    (getInitMove      x = [SOME (SLc (PSG initiateMovement))])
         then [
	       PL_WARNO_Auth
	        :((slCommand command)option, stateRole, 'd,'e)Form;
		(Name PlatoonLeader) controls prop (SOME (SLc (PL recon)));
		(Name PlatoonLeader) controls prop (SOME (SLc (PL tentativePlan)));
	       (Name PlatoonSergeant) controls prop (SOME (SLc (PSG initiateMovement)))]
	 else [(prop NONE):((slCommand command)option, stateRole, 'd,'e)Form])
    else [PL_notWARNO_Auth (getPlCom x)]`


(* ==== Old way of doing things
(Name PlatoonLeader) controls prop (SOME (SLc (PL recon))),
	       (Name PlatoonLeader) controls prop (SOME (SLc (PL tentativePlan))),
	       (Name PlatoonSergeant) controls prop (SOME (SLc (PSG initiateMovement))),

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

 ==== End old way of doing things ===== *)

(* -------------------------------------------------------------------------- *)
(* PlatoonLeader is authorized on any plCommand if not in WARNO state         *)
(*    and the plCommand is not report1.                                       *)
(* -------------------------------------------------------------------------- *)
(* Helper functions *)
val th1 =
  ISPECL
  [``inputOK:((slCommand command)option, stateRole, 'd,'e)Form -> bool``,
  ``secContextNull :((slCommand command)option, stateRole, 'd,'e)Form list ->
      ((slCommand command)option, stateRole, 'd,'e)Form list``,
  ``context: (slState) ->
       ((slCommand command)option, stateRole, 'd,'e)Form list ->
      ((slCommand command)option, stateRole, 'd,'e)Form list``,
  ``[((Name PlatoonLeader) says (prop (SOME (SLc (PL plCommand)))))
     :((slCommand command)option, stateRole, 'd,'e)Form]``,
  ``ins:((slCommand command)option, stateRole, 'd,'e)Form list list``,
  ``(s:slState)``,
  ``outs:slOutput output list trType list``] TR_exec_cmd_rule

val temp = fst(dest_imp(concl th1))

val PlatoonLeader_notWARNO_notreport1_exec_plCommand_lemma =
TAC_PROOF(
           ([],
            Term `(~((s:slState) = WARNO)) ==>
	          (~((plCommand:plCommand) = report1)) ==> ^temp`),
DISCH_TAC THEN
DISCH_TAC THEN
ASM_REWRITE_TAC
 [CFGInterpret_def, context_def, secContextNull_def,
  getRecon_def, getTenativePlan_def, getReport_def, getInitMove_def,
  getPlCom_def, getPsgCom_def, PL_notWARNO_Auth_def ,
  inputList_def, extractInput_def, MAP,
  propCommandList_def, extractPropCommand_def, satList_CONS,
  satList_nil, GSYM satList_conj]
THEN
PROVE_TAC[Controls, Modus_Ponens])


(* === Start testing here ====
(* -------------------------------------------------------------------------- *)
(* PlatoonLeader is authorized on any report1 if this is the WARNO state and  *)
(*   PlatoonLeader says recon /\      	      	      	     	   	      *)
(*   PlatoonLeader says tentativePlan /\				      *)
(*   PlatoonSergeant says initiateMovement /\				      *)
(*   PlatoonLeader says report1						      *)
(* -------------------------------------------------------------------------- *)
val PlatoonLeader_WARNO_exec_report1_lemma =
let
  val th1w =
  ISPECL
  [``inputOK:((slCommand command)option, stateRole, 'd,'e)Form -> bool``,
  ``secContextNull :((slCommand command)option, stateRole, 'd,'e)Form list ->
                    ((slCommand command)option, stateRole, 'd,'e)Form list``,
  ``context: (slState) ->
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
  ``(WARNO)``,
  ``outs:slOutput output list trType list``] TR_exec_cmd_rule
in
TAC_PROOF(
  set_goal([], fst(dest_imp(concl th1w))),

set_goal([], fst(dest_imp(concl th1w)))
(* 1 *)
ASM_REWRITE_TAC
[CFGInterpret_def, secContextNull_def, context_def,
 propCommandList_def, MAP,extractPropCommand_def ,
 satList_CONS, satList_nil, GSYM satList_conj,
 getRecon_def, getTenativePlan_def, getReport_def, getInitMove_def,
  getPlCom_def, getPsgCom_def, PL_WARNO_Auth_def]

THEN
PROVE_TAC[Controls, Modus_Ponens])
(* 2 *)
ASM_REWRITE_TAC
[NOT_NONE_SOME,NOT_SOME_NONE,SOME_11,slCommand_one_one,
 slCommand_distinct_clauses,plCommand_distinct_clauses,
 psgCommand_distinct_clauses,slState_distinct_clauses,
 GSYM slState_distinct_clauses,
 GSYM slCommand_distinct_clauses,
 GSYM plCommand_distinct_clauses,
 GSYM psgCommand_distinct_clauses]

set_goal ([], fst(dest_imp(concl th1w)))

 ==== End Testing Here ==== *)
val _ = export_theory();

end