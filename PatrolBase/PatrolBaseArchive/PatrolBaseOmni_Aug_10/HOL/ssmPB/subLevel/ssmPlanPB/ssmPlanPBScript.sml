(******************************************************************************)
(* ssmConductORP defines the top level state machine for the patrol base.      *)
(* Each state, save for the end states, have sub-level state machines, and    *)
(* some have sub-sub-level state machines.  These are implemented in separate *)
(* theories.                                                                  *)
(* Author: Lori Pickering in collaboration with Jesse Nathaniel Hall          *)
(* Date: 16 July 2017                                                         *)
(******************************************************************************)
structure ssmPlanPBScript = struct

(* ===== Interactive Mode ====
app load ["TypeBase", "listTheory","optionTheory",
          "acl_infRules","aclDrulesTheory","aclrulesTheory",
    	  "satListTheory","ssm11Theory","ssminfRules",
	  "OMNITypeTheory", "PlanPBTypeTheory",
	  
	  "ssmPlanPBTheory"];
open TypeBase listTheory optionTheory
     acl_infRules aclDrulesTheory aclrulesTheory
     satListTheory ssm11Theory ssminfRules
     OMNITypeTheory PlanPBTypeTheory
     ssmPlanPBTheory

 ==== end Interactive Mode ==== *)



open HolKernel Parse boolLib bossLib;
open TypeBase listTheory optionTheory
open acl_infRules aclDrulesTheory aclrulesTheory
open satListTheory ssm11Theory ssminfRules
open OMNITypeTheory PlanPBTypeTheory

val _ = new_theory "ssmPlanPB";

(* -------------------------------------------------------------------------- *)
(* Define the next state function for the state machine.                      *)
(* -------------------------------------------------------------------------- *)
val planPBNS_def =
Define
`
(* executing *)
(planPBNS RECEIVE_MISSION (exec ([PL warno]))          = WARNO)           /\
(planPBNS RECEIVE_MISSION (exec ([PL plIncomplete]))   = RECEIVE_MISSION) /\
(planPBNS WARNO (exec [PL  tentativePlan;
	  	       PSG initiateMovement;
		       PL  recon])                     = COMPLETE)        /\
(planPBNS WARNO (exec [PSG initiateMovement;
	  	       PL  tentativePlan;
		       PL  recon])                     = COMPLETE)        /\
(planPBNS WARNO (exec [PL  tentativePlan;
  	  	       PL  recon;
	  	       PSG initiateMovement])          = COMPLETE)        /\
(planPBNS WARNO (exec [PL  recon;
  	  	       PL  tentativePlan ;
	  	       PSG initiateMovement])          = COMPLETE)        /\
(planPBNS WARNO (exec [PSG initiateMovement;
  	  	       PL  recon;
	  	       PL  tentativePlan])             = COMPLETE)        /\
(planPBNS WARNO (exec [PL  recon;
  	  	       PSG initiateMovement;
	  	       PL  tentativePlan])             = COMPLETE)        /\
(planPBNS WARNO (exec [PL plIncomplete])               = WARNO)           /\
(* trapping *)
(planPBNS (s:slState)  (trap [PL  plCommand])  = s)                       /\
(planPBNS (s:slState)  (trap [PSG psgCommand]) = s)                       /\
(* discarding *)
(planPBNS (s:slState)  (discard [PL  plCommand])  = s)                    /\
(planPBNS (s:slState)  (discard [PSG psgCommand]) = s)`

(* -------------------------------------------------------------------------- *)
(* Define next-output function for ssmPlanPB                                  *)
(* -------------------------------------------------------------------------- *)
val planPBOut_def =
Define
`
(* executing *)
(planPBOut RECEIVE_MISSION (exec ([PL warno]))          = Warno)          /\
(planPBOut RECEIVE_MISSION (exec ([PL plIncomplete]))   = ReceiveMission) /\
(planPBOut WARNO (exec [PL  tentativePlan;
	  	       PSG initiateMovement;
		       PL  recon])                     = Complete)       /\
(planPBOut WARNO (exec [PSG initiateMovement;
	  	       PL  tentativePlan;
		       PL  recon])                     = Complete)       /\
(planPBOut WARNO (exec [PL  tentativePlan;
  	  	       PL  recon;
	  	       PSG initiateMovement])          = Complete)       /\
(planPBOut WARNO (exec [PL  recon;
  	  	       PL  tentativePlan ;
	  	       PSG initiateMovement])          = Complete)       /\
(planPBOut WARNO (exec [PSG initiateMovement;
  	  	       PL  recon;
	  	       PL  tentativePlan])             = Complete)       /\
(planPBOut WARNO (exec [PL  recon;
  	  	       PSG initiateMovement;
	  	       PL  tentativePlan])             = Complete)       /\
(planPBOut WARNO (exec [PL plIncomplete])               = Warno)         /\
(* trapping *)
(planPBOut (s:slState)  (trap [PL  plCommand])  = unAuthorized)          /\
(planPBOut (s:slState)  (trap [PSG psgCommand]) = unAuthorized)          /\
(* discarding *)
(planPBOut (s:slState)  (discard [PL  plCommand])  = unAuthenticated)    /\
(planPBOut (s:slState)  (discard [PSG psgCommand]) = unAuthenticated)`


(******************************************************************************)
(* Input Authentication                                                       *)
(******************************************************************************)
val authTestConductORP_def =
Define
`(authTestConductORP
 ((Name PlatoonLeader) says (prop  (cmd:(slCommand command)order))
 	:((slCommand command)order,stateRole,'d,'e)Form) = T) /\
 (authTestConductORP
 ((Name PlatoonSergeant) says (prop  (cmd:(slCommand command)order))
 	:((slCommand command)order,stateRole,'d,'e)Form) = T) /\
 (authTestConductORP _= F)`


(******************************************************************************)
(* "State Interpretation: this is the trivial assumption TT, as the machine   *)
(* state has no influence on access privileges"--Prof. Chin, SM0Script.sml    *)
(******************************************************************************)
val ssmConductORPStateInterp_def =
Define
`ssmConductORPStateInterp (slState:slState) = 
                    ( TT:((slCommand command)order,stateRole,'d,'e)Form)`


(******************************************************************************)
(* "A theorem showing commands without a principal are rejected."--Prof       *)
(*  Chin'e SM0Script.sml       	       	 	       			      *)
(******************************************************************************)
val authTestConductORP_cmd_reject_lemma =
TAC_PROOF(
 ([],
  ``!cmd. ~(authTestConductORP
      ((prop (SOME cmd)):((slCommand command)order,stateRole,'d,'e)Form))``),
PROVE_TAC[authTestConductORP_def])

val _ = save_thm("authTestConductORP_cmd_reject_lemma",
                 authTestConductORP_cmd_reject_lemma)



(* -------------------------------------------------------------------------- *)
(* securityContext definition: PlatoonLeader authorized on any slCommand      *)
(* (defined in PBTypeScript.sml)                                              *)
(* -------------------------------------------------------------------------- *)
val secContextConductORP_def =
Define
`secContextConductORP (plcmd:plCommand)(psgcmd:psgCommand)(incomplete:slCommand) =
 [((Name PlatoonLeader) controls
      (prop (SOME (SLc (PL plcmd)))) )
        :((slCommand command)order,stateRole,'d,'e)Form;
  ((Name PlatoonSergeant) controls
      (prop (SOME (SLc (PSG psgcmd)))) )
        :((slCommand command)order,stateRole,'d,'e)Form;
  ((Name PlatoonLeader) says
      (prop (SOME (SLc (PSG psgcmd)))) impf (prop NONE))
      :((slCommand command)order,stateRole,'d,'e)Form;
  ((Name PlatoonSergeant) says
      (prop (SOME (SLc (PL plcmd)))) impf (prop NONE))
      :((slCommand command)order,stateRole,'d,'e)Form]`



(******************************************************************************)
(* PlatoonLeader is authorized on any plCommand                               *)
(******************************************************************************)
val PlatoonLeader_plCommand_lemma =
TAC_PROOF(
([],
``CFGInterpret ((M:((slCommand command)order,'b,stateRole,'d,'e)Kripke),Oi,Os)
   (CFG
      authTestConductORP
      ssmConductORPStateInterp
      (secContextConductORP
         (plCommand:plCommand)(psgCommand:psgCommand)(incomplete:slCommand))
       (((Name PlatoonLeader) says (prop (SOME (SLc (PL plCommand)))))::ins)
      (s:slState)
      (outs:(slOutput output) list) ) ==>
  ((M,Oi,Os) sat (prop (SOME (SLc (PL plCommand)))))``),
REWRITE_TAC[CFGInterpret_def,secContextConductORP_def,ssmConductORPStateInterp_def,
		satList_CONS,satList_nil, sat_TT] THEN
PROVE_TAC[Controls])

val _ = save_thm("PlatoonLeader_plCommand_lemma",
		 PlatoonLeader_plCommand_lemma)


(* -------------------------------------------------------------------------- *)
(* exec plCommand occurs if and only if PlatoonLeaders's command is           *)
(* authenticated and authorized                                               *)
(* -------------------------------------------------------------------------- *)
val PlatoonLeader_exec_plCommand_justified_thm =
let
 val th1 =
 ISPECL
 [``authTestConductORP:((slCommand command)order, stateRole,'d,'e)Form -> bool``,
  ``(secContextConductORP
           (plCommand:plCommand)(psgCommand:psgCommand)(incomplete:slCommand))
           :((slCommand command)order, stateRole,'d,'e)Form list``,
  ``ssmConductORPStateInterp:(slState)->
           ((slCommand command)order, stateRole,'d,'e)Form``,
  ``Name PlatoonLeader``,``SLc (PL plCommand):(slCommand command)``,
  ``ins:((slCommand command)order,stateRole,'d,'e)Form list``,
  ``s:(slState)``,``outs:(slOutput output) list``]
 TR_exec_cmd_rule
in 
 TAC_PROOF(([],
  ``!(NS :(slState) -> (slCommand command)trType -> (slState))
     (Out :(slState) -> (slCommand command)trType -> (slOutput output))
     (M :((slCommand command)order, 'b, stateRole, 'd, 'e) Kripke)
     (Oi :'d po)
     (Os :'e po).
    TR (M,Oi,Os) (exec (SLc (PL plCommand)):((slCommand command)trType))
      (CFG
        (authTestConductORP
           :((slCommand command)order, stateRole, 'd, 'e) Form -> bool)
        (ssmConductORPStateInterp :(slState)
           -> ((slCommand command)order, stateRole, 'd, 'e) Form)
        ((secContextConductORP
           (plCommand:plCommand)(psgCommand:psgCommand)(incomplete:slCommand))
           :((slCommand command)order, stateRole,'d,'e)Form list)
        (Name PlatoonLeader says
           (prop (SOME (SLc (PL plCommand)):(slCommand command)order):
             ((slCommand command)order, stateRole, 'd, 'e)Form)::
             (ins :((slCommand command)order, stateRole,'d,'e)Form list))
        (s:(slState))
        (outs:(slOutput output) list) )
      (CFG
	(authTestConductORP
	   :((slCommand command)order, stateRole, 'd, 'e) Form -> bool)
        (ssmConductORPStateInterp :(slState)
           -> ((slCommand command)order, stateRole, 'd, 'e) Form)
        ((secContextConductORP
           (plCommand:plCommand)(psgCommand:psgCommand)(incomplete:slCommand))
           :((slCommand command)order, stateRole,'d,'e)Form list)
        ins
        (NS
	 (s:(slState))
	 (exec (SLc (PL plCommand)):((slCommand command)trType)) )
        (Out
	 (s:(slState))
	 (exec (SLc (PL plCommand)):((slCommand command)trType))::outs )  )
   <=>
   authTestConductORP
       (Name PlatoonLeader says
           (prop (SOME (SLc (PL plCommand)):(slCommand command)order):
             ((slCommand command)order, stateRole, 'd, 'e)Form))
       /\
   CFGInterpret (M,Oi,Os)
      (CFG
        (authTestConductORP
           :((slCommand command)order, stateRole, 'd, 'e) Form -> bool)
        (ssmConductORPStateInterp :(slState)
           -> ((slCommand command)order, stateRole, 'd, 'e) Form)
        ((secContextConductORP
           (plCommand:plCommand)(psgCommand:psgCommand)(incomplete:slCommand))
           :((slCommand command)order, stateRole,'d,'e)Form list)
        (Name PlatoonLeader says
           (prop (SOME (SLc (PL plCommand)):(slCommand command)order):
             ((slCommand command)order, stateRole, 'd, 'e)Form)::
             (ins :((slCommand command)order, stateRole,'d,'e)Form list))
        (s:(slState))
        (outs:(slOutput output) list) )
      /\
   (M,Oi,Os) sat
        (prop (SOME (SLc (PL plCommand)):(slCommand command)order):
           ((slCommand command)order, stateRole, 'd, 'e)Form)``),
 PROVE_TAC[th1,PlatoonLeader_plCommand_lemma])
end

val _ =
 save_thm("PlatoonLeader_exec_plCommand_justified_thm",
           PlatoonLeader_exec_plCommand_justified_thm)



(******************************************************************************)
(* PlatoonSergeant is authorized on any psgCommand                            *)
(******************************************************************************)
val PlatoonSergeant_psgCommand_lemma =
TAC_PROOF(
([],
``CFGInterpret ((M:((slCommand command)order,'b,stateRole,'d,'e)Kripke),Oi,Os)
   (CFG
      authTestConductORP
      ssmConductORPStateInterp
      (secContextConductORP (plCommand:plCommand)(psgCommand:psgCommand)(incomplete:slCommand))
       (((Name PlatoonSergeant) says (prop (SOME (SLc (PSG psgCommand)))))::ins)
      (s:slState)
      (outs:(slOutput output) list) ) ==>
  ((M,Oi,Os) sat (prop (SOME (SLc (PSG psgCommand)))))``),
REWRITE_TAC[CFGInterpret_def,secContextConductORP_def,ssmConductORPStateInterp_def,
		satList_CONS,satList_nil, sat_TT] THEN
PROVE_TAC[Controls])

val _ = save_thm("PlatoonSergeant_psgCommand_lemma",
		 PlatoonSergeant_psgCommand_lemma)


(* -------------------------------------------------------------------------- *)
(* exec psgCommand occurs if and only if PlatoonSergeant's command is           *)
(* authenticated and authorized                                               *)
(* -------------------------------------------------------------------------- *)
val PlatoonSergeant_exec_psgCommand_justified_thm =
let
 val th1 =
 ISPECL
 [``authTestConductORP:((slCommand command)order, stateRole,'d,'e)Form -> bool``,
  ``(secContextConductORP
           (plCommand:plCommand)(psgCommand:psgCommand)(incomplete:slCommand))
           :((slCommand command)order, stateRole,'d,'e)Form list``,
  ``ssmConductORPStateInterp:(slState)->
           ((slCommand command)order, stateRole,'d,'e)Form``,
  ``Name PlatoonSergeant``,``SLc (PSG psgCommand):(slCommand command)``,
  ``ins:((slCommand command)order,stateRole,'d,'e)Form list``,
  ``s:(slState)``,``outs:(slOutput output) list``]
 TR_exec_cmd_rule
in 
 TAC_PROOF(([],
  ``!(NS :(slState) -> (slCommand command)trType -> (slState))
     (Out :(slState) -> (slCommand command)trType -> (slOutput output))
     (M :((slCommand command)order, 'b, stateRole, 'd, 'e) Kripke)
     (Oi :'d po)
     (Os :'e po).
    TR (M,Oi,Os) (exec (SLc (PSG psgCommand)):((slCommand command)trType))
      (CFG
        (authTestConductORP
           :((slCommand command)order, stateRole, 'd, 'e) Form -> bool)
        (ssmConductORPStateInterp :(slState)
           -> ((slCommand command)order, stateRole, 'd, 'e) Form)
        ((secContextConductORP
           (plCommand:plCommand)(psgCommand:psgCommand)(incomplete:slCommand))
           :((slCommand command)order, stateRole,'d,'e)Form list)
        (Name PlatoonSergeant says
           (prop (SOME (SLc (PSG psgCommand)):(slCommand command)order):
             ((slCommand command)order, stateRole, 'd, 'e)Form)::
             (ins :((slCommand command)order, stateRole,'d,'e)Form list))
        (s:(slState))
        (outs:(slOutput output) list) )
      (CFG
	(authTestConductORP
	   :((slCommand command)order, stateRole, 'd, 'e) Form -> bool)
        (ssmConductORPStateInterp :(slState)
           -> ((slCommand command)order, stateRole, 'd, 'e) Form)
        ((secContextConductORP
           (plCommand:plCommand)(psgCommand:psgCommand)(incomplete:slCommand))
           :((slCommand command)order, stateRole,'d,'e)Form list)
        ins
        (NS
	 (s:(slState))
	 (exec (SLc (PSG psgCommand)):((slCommand command)trType)) )
        (Out
	 (s:(slState))
	 (exec (SLc (PSG psgCommand)):((slCommand command)trType))::outs )  )
   <=>
   authTestConductORP
       (Name PlatoonSergeant says
           (prop (SOME (SLc (PSG psgCommand)):(slCommand command)order):
             ((slCommand command)order, stateRole, 'd, 'e)Form))
       /\
   CFGInterpret (M,Oi,Os)
      (CFG
        (authTestConductORP
           :((slCommand command)order, stateRole, 'd, 'e) Form -> bool)
        (ssmConductORPStateInterp :(slState)
           -> ((slCommand command)order, stateRole, 'd, 'e) Form)
        ((secContextConductORP
           (plCommand:plCommand)(psgCommand:psgCommand)(incomplete:slCommand))
           :((slCommand command)order, stateRole,'d,'e)Form list)
        (Name PlatoonSergeant says
           (prop (SOME (SLc (PSG psgCommand)):(slCommand command)order):
             ((slCommand command)order, stateRole, 'd, 'e)Form)::
             (ins :((slCommand command)order, stateRole,'d,'e)Form list))
        (s:(slState))
        (outs:(slOutput output) list) )
      /\
   (M,Oi,Os) sat
        (prop (SOME (SLc (PSG psgCommand)):(slCommand command)order):
           ((slCommand command)order, stateRole, 'd, 'e)Form)``),
 PROVE_TAC[th1,PlatoonSergeant_psgCommand_lemma])
end

val _ =
 save_thm("PlatoonSergeant_exec_psgCommand_justified_thm",
           PlatoonSergeant_exec_psgCommand_justified_thm)

(* ==== Testing here ====
 ==== End Testing Here ==== *)
val _ = export_theory();

end