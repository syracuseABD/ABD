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
	  "OMNITypeTheory", "PlanPBTypeTheory","ssmPlanPBTheory",
	  "PlanPBDefTheory"];

open TypeBase listTheory optionTheory
     acl_infRules aclDrulesTheory aclrulesTheory
     aclsemanticsTheory aclfoundationTheory
     satListTheory ssmTheory ssminfRules uavUtilities
     OMNITypeTheory PlanPBTypeTheory ssmPlanPBTheory
     PlanPBDefTheory
 ==== end Interactive Mode ==== *)

open HolKernel Parse boolLib bossLib;
open TypeBase listTheory optionTheory
open acl_infRules aclDrulesTheory aclrulesTheory
open satListTheory ssmTheory ssminfRules uavUtilities
open OMNITypeTheory PlanPBTypeTheory PlanPBDefTheory

val _ = new_theory "ssmPlanPB";

(* -------------------------------------------------------------------------- *)
(* Define the next-state & next-output functions for the state machine.       *)
(* -------------------------------------------------------------------------- *)
val planPBNS_def = Define `
(planPBNS WARNO (exec x) =
   if ((getRecon        x = [SOME (SLc (PL recon))] )        /\
      (getTenativePlan  x = [SOME (SLc (PL tentativePlan))]) /\
      (getReport        x = [SOME (SLc (PL report1))])       /\
      (getInitMove      x = [SOME (SLc (PSG initiateMovement))] ))
   then REPORT1
   else WARNO) /\
(planPBNS PLAN_PB         (exec x) = if (getPlCom x = receiveMission)
	  	  	    then RECEIVE_MISSION else PLAN_PB)   /\
(planPBNS RECEIVE_MISSION (exec x) =  if (getPlCom x = warno)
	  	  	     then  WARNO else RECEIVE_MISSION)   /\ 
(planPBNS REPORT1         (exec x) =  if (getPlCom x = completePlan)
	  		    then COMPLETE_PLAN else REPORT1)     /\
(planPBNS COMPLETE_PLAN   (exec x) =  if (getPlCom x = opoid)
	  		    then OPOID else COMPLETE_PLAN) /\
(planPBNS OPOID           (exec x) =  if (getPlCom x = supervise)
	  		    then SUPERVISE else OPOID)     /\
(planPBNS SUPERVISE       (exec x) =  if (getPlCom x = report2)
	  		    then REPORT2 else SUPERVISE)   /\
(planPBNS REPORT2         (exec x) =  if (getPlCom x = complete)
	  		    then COMPLETE else REPORT2)    /\
(planPBNS (s:slState)     (trap _)     = s)                /\
(planPBNS (s:slState)     (discard _)  = s) `


val planPBOut_def = Define `
(planPBOut WARNO (exec x) =
   if ((getRecon        x = [SOME (SLc (PL recon))] )        /\
      (getTenativePlan  x = [SOME (SLc (PL tentativePlan))]) /\
      (getReport        x = [SOME (SLc (PL report1))])       /\
      (getInitMove      x = [SOME (SLc (PSG initiateMovement))] ))
   then Report1
   else unAuthorized) /\
(planPBOut PLAN_PB         (exec x) = if (getPlCom x = receiveMission)
	  	  	    then ReceiveMission else unAuthorized)   /\
(planPBOut RECEIVE_MISSION (exec x) =  if (getPlCom x = warno)
	  	  	     then  Warno else unAuthorized)   /\ 
(planPBOut REPORT1         (exec x) =  if (getPlCom x = completePlan)
	  		    then CompletePlan else unAuthorized)     /\
(planPBOut COMPLETE_PLAN   (exec x) =  if (getPlCom x = opoid)
	  		    then Opoid else unAuthorized) /\
(planPBOut OPOID           (exec x) =  if (getPlCom x = supervise)
	  		    then Supervise else unAuthorized)     /\
(planPBOut SUPERVISE       (exec x) =  if (getPlCom x = report2)
	  		    then Report2 else unAuthorized)   /\
(planPBOut REPORT2         (exec x) =  if (getPlCom x = complete)
	  		    then Complete else unAuthorized)    /\
(planPBOut (s:slState)     (trap _)     = unAuthorized)                /\
(planPBOut (s:slState)     (discard _)  = unAuthenticated) `


(* -------------------------------------------------------------------------- *)
(* inputOK: authentication test function                                      *)
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
(* Lemma: PlatoonLeader is authorized on any plCommand if not in WARNO state  *)
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

(* lemma *)
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



(* -------------------------------------------------------------------------- *)
(* PlatoonLeader is authorized on any report1 if this is the WARNO state and  *)
(*   PlatoonLeader says recon /\      	      	      	     	   	      *)
(*   PlatoonLeader says tentativePlan /\				      *)
(*   PlatoonSergeant says initiateMovement /\				      *)
(*   PlatoonLeader says report1						      *)
(* -------------------------------------------------------------------------- *)

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


val PlatoonLeader_WARNO_exec_report1_lemma =
TAC_PROOF(
  ([], fst(dest_imp(concl th1w))),
ASM_REWRITE_TAC
[CFGInterpret_def, secContextNull_def, context_def,
 propCommandList_def, MAP,extractPropCommand_def ,
 satList_CONS, satList_nil, GSYM satList_conj,
 getRecon_def, getTenativePlan_def, getReport_def, getInitMove_def,
  getPlCom_def, getPsgCom_def, PL_WARNO_Auth_def]
THEN
PROVE_TAC[Controls, Modus_Ponens])

(* === Start testing here ====
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