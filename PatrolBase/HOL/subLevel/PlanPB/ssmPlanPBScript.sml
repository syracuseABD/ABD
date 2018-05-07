(******************************************************************************)
(* ssmPlanPB describes the secure state machine derived from the PLAN_PB      *)
(* state at the top-level.  This is the first secure state machine to use the *)
(* new ssm parameterizable secure state machine.     	   	              *)
(* Contributors: Lori Pickering (HOL Implementation)			      *)
(* 		 Jesse Nathaniel Hall (subject matter)			      *)
(******************************************************************************)

structure ssmPlanPBScript = struct

(* ===== Interactive Mode ====
app load  ["TypeBase", "listTheory","optionTheory","listSyntax",
          "acl_infRules","aclDrulesTheory","aclrulesTheory",
	  "aclsemanticsTheory", "aclfoundationTheory",
    	  "satListTheory","ssmTheory","ssminfRules","uavUtilities",
	  "OMNITypeTheory", "PlanPBTypeTheory","PlanPBDefTheory",
	  "ssmPlanPBTheory"];

open TypeBase listTheory optionTheory listSyntax
     acl_infRules aclDrulesTheory aclrulesTheory
     aclsemanticsTheory aclfoundationTheory
     satListTheory ssmTheory ssminfRules uavUtilities
     OMNITypeTheory PlanPBTypeTheory PlanPBDefTheory
     ssmPlanPBTheory
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
(* Theorem: PlatoonLeader is authorized on any plCommand                      *)
(*      iff not in WARNO state and                                            *)
(*       the plCommand is not report1.                                        *)
(* -------------------------------------------------------------------------- *)

(* Helper functions *)
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

val temp = fst(dest_imp(concl th1))

(* lemma *)
val PlatoonLeader_notWARNO_notreport1_exec_plCommand_lemma =
TAC_PROOF(
          ([],
            Term `(~((s:slState) = WARNO)) ==>
	          (~((plCommand:plCommand) = invalidPlCommand)) ==>
	          (~((plCommand:plCommand) = report1)) ==> ^temp`),
DISCH_TAC THEN
DISCH_TAC THEN
DISCH_TAC THEN
ASM_REWRITE_TAC
 [CFGInterpret_def, secContext_def, secContextNull_def,
  getRecon_def, getTenativePlan_def, getReport_def, getInitMove_def,
  getPlCom_def, getPsgCom_def, PL_notWARNO_Auth_def ,
  inputList_def, extractInput_def, MAP,
  propCommandList_def, extractPropCommand_def, satList_CONS,
  satList_nil, GSYM satList_conj]
THEN
PROVE_TAC[Controls, Modus_Ponens])

val _= save_thm ("PlatoonLeader_notWARNO_notreport1_exec_plCommand_lemma",
       		  PlatoonLeader_notWARNO_notreport1_exec_plCommand_lemma)

(* helper functions *)
val temp2 = snd(dest_imp(concl th1))

(* lemma *)
val PlatoonLeader_notWARNO_notreport1_exec_plCommand_justified_lemma =
TAC_PROOF(
         ([],
            Term `(~((s:slState) = WARNO)) ==>
	    	  (~((plCommand:plCommand) = invalidPlCommand)) ==>
	          (~((plCommand:plCommand) = report1)) ==> ^temp2`),
DISCH_TAC THEN
DISCH_TAC THEN
DISCH_TAC THEN
PROVE_TAC
    [PlatoonLeader_notWARNO_notreport1_exec_plCommand_lemma,
     TR_exec_cmd_rule])

val _= save_thm ("PlatoonLeader_notWARNO_notreport1_exec_plCommand_justified_lemma",
       		  PlatoonLeader_notWARNO_notreport1_exec_plCommand_justified_lemma)

(* Main theorem *)
val PlatoonLeader_notWARNO_notreport1_exec_plCommand_justified_thm =
REWRITE_RULE
[propCommandList_def, inputList_def, extractPropCommand_def,
 extractInput_def, MAP] PlatoonLeader_notWARNO_notreport1_exec_plCommand_justified_lemma 

val _= save_thm("PlatoonLeader_notWARNO_notreport1_exec_plCommand_justified_thm",
          PlatoonLeader_notWARNO_notreport1_exec_plCommand_justified_thm)

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
  ``(WARNO)``,
  ``outs:slOutput output list trType list``] TR_exec_cmd_rule


(* lemma *)
val PlatoonLeader_WARNO_exec_report1_lemma =
TAC_PROOF(
  ([], fst(dest_imp(concl th1w))),
ASM_REWRITE_TAC
[CFGInterpret_def, secContextNull_def, secContext_def,
 propCommandList_def, MAP,extractPropCommand_def ,
 satList_CONS, satList_nil, GSYM satList_conj,
 getRecon_def, getTenativePlan_def, getReport_def, getInitMove_def,
  getPlCom_def, getPsgCom_def, PL_WARNO_Auth_def]
THEN
PROVE_TAC[Controls, Modus_Ponens])

val _= save_thm("PlatoonLeader_WARNO_exec_report1_lemma",
		 PlatoonLeader_WARNO_exec_report1_lemma)

(* lemma *)
val PlatoonLeader_WARNO_exec_report1_justified_lemma =
TAC_PROOF(
 ([], snd(dest_imp(concl th1w))),
 PROVE_TAC
 [PlatoonLeader_WARNO_exec_report1_lemma,
  TR_exec_cmd_rule])

val _= save_thm("PlatoonLeader_WARNO_exec_report1_justified_lemma",
		 PlatoonLeader_WARNO_exec_report1_justified_lemma)


val th23 = REWRITE_RULE
[PlatoonLeader_WARNO_exec_report1_lemma,
 PlatoonLeader_WARNO_exec_report1_justified_lemma] th1w

(* Main theorem *)

val PlatoonLeader_WARNO_exec_report1_justified_thm =
REWRITE_RULE
[propCommandList_def, inputList_def, extractPropCommand_def,
 extractInput_def, MAP]  
PlatoonLeader_WARNO_exec_report1_justified_lemma

val _= save_thm("PlatoonLeader_WARNO_exec_report1_justified_thm",
         PlatoonLeader_WARNO_exec_report1_justified_thm)

(* -------------------------------------------------------------------------- *)
(* Theorem: PlatoonLeader is not discarded any psgCommand.                    *)
(* Note that this is just meant to demonstrate the authenticated inputs are   *)
(* not discarded.  Instead, they should be trapped. This is because of how    *)
(* how the inputOK (authentication) was defined.  Note, this proof would also *)
(* be valid for PlatoonLeader on any plCommand.  It is not necessary to prove *)
(* this.                                                                      *)
(* -------------------------------------------------------------------------- *)
(* Should we put this GENL  in the TR_discard_cmd_rule? *)
val th1d =
GENL
[``(elementTest :('command option, 'principal, 'd, 'e) Form -> bool)``,
 ``(context :
        ('command option, 'principal, 'd, 'e) Form list ->
        ('command option, 'principal, 'd, 'e) Form list)``,
 ``(stateInterp :
        'state ->
        ('command option, 'principal, 'd, 'e) Form list ->
        ('command option, 'principal, 'd, 'e) Form list)``,
 ``(x :('command option, 'principal, 'd, 'e) Form list)``,
 ``(ins :('command option, 'principal, 'd, 'e) Form list list)``,
 ``(s :'state)``,
 ``(outs :'output list)``,
 ``(NS :'state -> 'command option list trType -> 'state)``,
 ``(Out :'state -> 'command option list trType -> 'output)``,
 ``(M :('command option, 'b, 'principal, 'd, 'e) Kripke)``,
 ``(Oi :'d po)``,``(Os :'e po)``]
TR_discard_cmd_rule

val th2d =
ISPECL
  [``inputOK:((slCommand command)option, stateRole, 'd,'e)Form -> bool``,
  ``secContextNull :((slCommand command)option, stateRole, 'd,'e)Form list ->
                    ((slCommand command)option, stateRole, 'd,'e)Form list``,
  ``secContext: (slState) ->
       ((slCommand command)option, stateRole, 'd,'e)Form list ->
       ((slCommand command)option, stateRole, 'd,'e)Form list``,
  ``[(Name PlatoonLeader) says (prop (SOME (SLc (PSG psgCommand))))
      :((slCommand command)option, stateRole, 'd,'e)Form]``,
  ``ins:((slCommand command)option, stateRole, 'd,'e)Form list list``,
  ``(s:slState)``,
  ``outs:slOutput output list trType list``] th1d

val th3d = LIST_BETA_CONV (Term `(\p q. p /\ q) F ((\p q. p/\q) T ((\p q. p /\ q) T T))`)
val th3d2 = LIST_BETA_CONV (Term `(\p q. p/\q) T T`)

val PlatoonLeader_psgCommand_notDiscard_thm = REWRITE_RULE
[authenticationTest_def, MAP, inputOK_def, FOLDR, th3d, th3d2] th2d

val _= save_thm("PlatoonLeader_psgCommand_notDiscard_thm",
                 PlatoonLeader_psgCommand_notDiscard_thm)

(* -------------------------------------------------------------------------- *)
(* Theorem: PlatoonLeader is trapped on any psgCommand.                       *)
(* -------------------------------------------------------------------------- *)
val th1t =
ISPECL
  [``inputOK:((slCommand command)option, stateRole, 'd,'e)Form -> bool``,
  ``secContextNull :((slCommand command)option, stateRole, 'd,'e)Form list ->
                    ((slCommand command)option, stateRole, 'd,'e)Form list``,
  ``secContext: (slState) ->
       ((slCommand command)option, stateRole, 'd,'e)Form list ->
       ((slCommand command)option, stateRole, 'd,'e)Form list``,
  ``[(Name PlatoonLeader) says (prop (SOME (SLc (PSG psgCommand))))
      :((slCommand command)option, stateRole, 'd,'e)Form]``,
  ``ins:((slCommand command)option, stateRole, 'd,'e)Form list list``,
  ``(s:slState)``,
  ``outs:slOutput output list trType list``]
  TR_trap_cmd_rule


val PlatoonLeader_trap_psgCommand_lemma =
TAC_PROOF(
	([],
         fst(dest_imp(concl th1t))), 
ASM_REWRITE_TAC
[CFGInterpret_def, inputOK_def, secContext_def, secContextNull_def]
THEN
ASM_REWRITE_TAC
[getRecon_def,getTenativePlan_def, getReport_def, getInitMove_def,
 getPlCom_def,satList_CONS, satList_nil, GSYM satList_conj]
THEN
ASM_REWRITE_TAC
[NOT_NONE_SOME,NOT_SOME_NONE, SOME_11, list_11,
 slCommand_one_one, slCommand_distinct_clauses,
 plCommand_distinct_clauses, psgCommand_distinct_clauses,
 GSYM slCommand_distinct_clauses,
 GSYM plCommand_distinct_clauses,
 GSYM psgCommand_distinct_clauses]
THEN
PROVE_TAC[satList_CONS, satList_nil])

val _= save_thm("PlatoonLeader_trap_psgCommand_lemma",
		 PlatoonLeader_trap_psgCommand_lemma)

val PlatoonLeader_trap_psgCommand_justified_lemma =
TAC_PROOF(
	([],
	snd(dest_imp(concl th1t))),
PROVE_TAC
[PlatoonLeader_trap_psgCommand_lemma, TR_trap_cmd_rule])
	
val _= save_thm("PlatoonLeader_trap_psgCommand_justified_lemma",
		 PlatoonLeader_trap_psgCommand_justified_lemma)


val PlatoonLeader_trap_psgCommand_justified_thm =
REWRITE_RULE
[propCommandList_def, inputList_def, extractPropCommand_def,
 extractInput_def, MAP]
 PlatoonLeader_trap_psgCommand_justified_lemma

val _= save_thm("PlatoonLeader_trap_psgCommand_justified_lemma",
		 PlatoonLeader_trap_psgCommand_justified_lemma)

(* -------------------------------------------------------------------------- *)
(* Theorem: PlatoonSergeant is trapped on any plCommand.                      *)
(* -------------------------------------------------------------------------- *)
val th1tt =
ISPECL
  [``inputOK:((slCommand command)option, stateRole, 'd,'e)Form -> bool``,
  ``secContextNull :((slCommand command)option, stateRole, 'd,'e)Form list ->
                    ((slCommand command)option, stateRole, 'd,'e)Form list``,
  ``secContext: (slState) ->
       ((slCommand command)option, stateRole, 'd,'e)Form list ->
       ((slCommand command)option, stateRole, 'd,'e)Form list``,
  ``[(Name PlatoonSergeant) says (prop (SOME (SLc (PL plCommand))))
      :((slCommand command)option, stateRole, 'd,'e)Form]``,
  ``ins:((slCommand command)option, stateRole, 'd,'e)Form list list``,
  ``(s:slState)``,
  ``outs:slOutput output list trType list``]
  TR_trap_cmd_rule


val PlatoonSergeant_trap_plCommand_lemma =
TAC_PROOF(
	([],
         fst(dest_imp(concl th1tt))), 
ASM_REWRITE_TAC
[CFGInterpret_def, inputOK_def, secContext_def, secContextNull_def]
THEN
ASM_REWRITE_TAC
[getRecon_def,getTenativePlan_def, getReport_def, getInitMove_def,
 getPlCom_def,satList_CONS, satList_nil, GSYM satList_conj]
THEN
ASM_REWRITE_TAC
[NOT_NONE_SOME,NOT_SOME_NONE, SOME_11, list_11,
 slCommand_one_one, slCommand_distinct_clauses,
 plCommand_distinct_clauses, psgCommand_distinct_clauses,
 GSYM slCommand_distinct_clauses,
 GSYM plCommand_distinct_clauses,
 GSYM psgCommand_distinct_clauses]
THEN
PROVE_TAC[satList_CONS, satList_nil])

val _= save_thm("PlatoonSergeant_trap_plCommand_lemma",
		 PlatoonSergeant_trap_plCommand_lemma)

val PlatoonSergeant_trap_plCommand_justified_lemma =
TAC_PROOF(
	([],
	snd(dest_imp(concl th1tt))),
PROVE_TAC
[PlatoonSergeant_trap_plCommand_lemma, TR_trap_cmd_rule])
	
val _= save_thm("PlatoonSergeant_trap_plCommand_justified_lemma",
		 PlatoonSergeant_trap_plCommand_justified_lemma)


val PlatoonSergeant_trap_plCommand_justified_thm =
REWRITE_RULE
[propCommandList_def, inputList_def, extractPropCommand_def,
 extractInput_def, MAP]
 PlatoonSergeant_trap_plCommand_justified_lemma

val _= save_thm("PlatoonSergeant_trap_plCommand_justified_thm",
		 PlatoonSergeant_trap_plCommand_justified_thm)

(* ==== Start testing here ====

(* -------------------------------------------------------------------------- *)
(* Theorem: if state = WARNO and not					      *)
(*      (PlatoonLeader says recon and					      *)
(*	PlatoonLeader says tentativePlan and				      *)
(* 	PlatoonSergeant says initiateMovement) then			      *)
(*      PlatoonLeader says report1 is trapped. 				      *)
(* -------------------------------------------------------------------------- *)
val th1tw =
  ISPECL
  [``inputOK:((slCommand command)option, stateRole, 'd,'e)Form -> bool``,
  ``secContextNull :((slCommand command)option, stateRole, 'd,'e)Form list ->
                    ((slCommand command)option, stateRole, 'd,'e)Form list``,
  ``secContext: (slState) ->
       ((slCommand command)option, stateRole, 'd,'e)Form list ->
       ((slCommand command)option, stateRole, 'd,'e)Form list``,
  ``[(Name PlatoonLeader) says (prop (SOME (SLc (PL report1))))
      :((slCommand command)option, stateRole, 'd,'e)Form]``,
  ``ins:((slCommand command)option, stateRole, 'd,'e)Form list list``,
  ``(s:slState)``,
  ``outs:slOutput output list trType list``] TR_exec_cmd_rule

set_goal ([],
		fst(dest_imp(concl th1tw)))
      	       
ASM_REWRITE_TAC
[CFGInterpret_def, inputOK_def, secContext_def, secContextNull_def]
THEN
ASM_REWRITE_TAC
[getRecon_def,getTenativePlan_def, getReport_def, getInitMove_def,
 getPlCom_def,satList_CONS, satList_nil, GSYM satList_conj,PL_notWARNO_Auth_def]
THEN
ASM_REWRITE_TAC
[NOT_NONE_SOME,NOT_SOME_NONE, SOME_11, list_11,
 slCommand_one_one, slCommand_distinct_clauses,
 plCommand_distinct_clauses, psgCommand_distinct_clauses,
 GSYM slCommand_distinct_clauses,
 GSYM plCommand_distinct_clauses,
 GSYM psgCommand_distinct_clauses,
 satList_CONS, satList_nil]
THEN
ASM_REWRITE_TAC
[propCommandList_def, inputList_def, MAP, extractPropCommand_def,
 extractInput_def, satList_CONS, satList_nil,GSYM satList_conj, sat_TT,
 satList_CONS, IF_EQUALS_OPTION, IF_NONE_EQUALS_OPTION,
 NOT_NONE_SOME,NOT_SOME_NONE, SOME_11, list_11]





==== End Testing Here ==== *)
val _ = export_theory();

end