(******************************************************************************)
(* ssmConductORP defines the ConductORP sub-level state machine for the       *)
(* patrol base.                                                               *)
(* Each state, save for the end states, has a sub-level state machine, and    *)
(* some have sub-sub-level state machines.  These are implemented in separate *)
(* theories.                                                                  *)
(* Author: Lori Pickering in collaboration with Jesse Nathaniel Hall          *)
(* Date: 16 July 2017                                                         *)
(******************************************************************************)
structure ssmConductORPScript = struct

(* ===== Interactive Mode ====
app load ["TypeBase", "listTheory","optionTheory",
          "acl_infRules","aclDrulesTheory","aclrulesTheory",
    	  "satListTheory","ssm11Theory","ssminfRules",
	  "OMNITypeTheory", "ConductORPTypeTheory"];
	  
	  "ssmConductORPTheory"];
open TypeBase listTheory optionTheory
     acl_infRules aclDrulesTheory aclrulesTheory
     satListTheory ssm11Theory ssminfRules
     OMNITypeTheory ConductORPTypeTheory
     ssmConductORPTheory



 ==== end Interactive Mode ==== *)

open HolKernel Parse boolLib bossLib;
open TypeBase listTheory optionTheory
open acl_infRules aclDrulesTheory aclrulesTheory
open satListTheory ssm11Theory ssminfRules
open OMNITypeTheory ConductORPTypeTheory

val _ = new_theory "ssmConductORP";

(* -------------------------------------------------------------------------- *)
(* Define the next state function for the state machine.                      *)
(* -------------------------------------------------------------------------- *)
val conductORPNS_def =
Define
`
(* executing *)
 (conductORPNS CONDUCT_ORP (exec (PL secure))          = SECURE)      /\
 (conductORPNS CONDUCT_ORP (exec (PL plIncomplete))    = CONDUCT_ORP) /\
 (conductORPNS SECURE      (exec (PSG actionsIn))      = ACTIONS_IN)  /\
 (conductORPNS SECURE      (exec (PSG psgIncomplete))  = SECURE)      /\
 (conductORPNS ACTIONS_IN  (exec (PL withdraw))        = WITHDRAW)    /\
 (conductORPNS ACTIONS_IN  (exec (PL plIncomplete))    = ACTIONS_IN)  /\
 (conductORPNS WITHDRAW    (exec (PL complete))        = COMPLETE)    /\
 (conductORPNS WITHDRAW    (exec (PL plIncomplete))    = WITHDRAW)    /\
(* trapping *) 
 (conductORPNS (s:slState) (trap (PL (cmd:plCommand)))   = s) /\
 (conductORPNS (s:slState) (trap (PSG (cmd:psgCommand))) = s) /\
(* discarding *)
 (conductORPNS (s:slState) (discard (PL (cmd:plCommand)))   = s) /\
 (conductORPNS (s:slState) (discard (PSG (cmd:psgCommand))) = s)`

(* -------------------------------------------------------------------------- *)
(* Define next-output function for the state machine                          *)
(* -------------------------------------------------------------------------- *)
val conductORPOut_def =
Define
`
(* executing *)
 (conductORPOut CONDUCT_ORP (exec (PL secure))         = Secure)     /\
 (conductORPOut CONDUCT_ORP (exec (PL plIncomplete))   = ConductORP) /\
 (conductORPOut SECURE      (exec (PSG actionsIn))     = ActionsIn)  /\
 (conductORPOut SECURE      (exec (PSG psgIncomplete)) = Secure)     /\
 (conductORPOut ACTIONS_IN  (exec (PL withdraw))       = Withdraw)   /\
 (conductORPOut ACTIONS_IN  (exec (PL plIncomplete))   = ActionsIn)  /\
 (conductORPOut WITHDRAW    (exec (PL complete))       = Complete)   /\
 (conductORPOut WITHDRAW    (exec (PL plIncomplete))   = Withdraw)   /\
(* trapping *) 
 (conductORPOut (s:slState) (trap (PL (cmd:plCommand)))   = unAuthorized) /\
 (conductORPOut (s:slState) (trap (PSG (cmd:psgCommand))) = unAuthorized) /\
(* discarding *)
 (conductORPOut (s:slState) (discard (PL (cmd:plCommand)))   = unAuthenticated) /\
 (conductORPOut (s:slState) (discard (PSG (cmd:psgCommand))) = unAuthenticated)`


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


(* ==== This is no longer necessary...but, I worked hard to write and I am not
ready to part with it just yet. ====
val ssmConductORPStateInterp_def =
Define
`(ssmConductORPStateInterp CONDUCT_ORP =
                    (  ((Name (PlatoonLeader:stateRole)) controls
      (prop (SOME (SLc (incomplete:slCommand)))) )
        :((slCommand command)order,stateRole,'d,'e)Form)) /\
(ssmConductORPStateInterp ACTIONS_IN =
                    (  ((Name (PlatoonLeader:stateRole)) controls
      (prop (SOME (SLc (incomplete:slCommand)))) )
        :((slCommand command)order,stateRole,'d,'e)Form)) /\
(ssmConductORPStateInterp WITHDRAW =
                    (  ((Name (PlatoonLeader:stateRole)) controls
      (prop (SOME (SLc (incomplete:slCommand)))) )
        :((slCommand command)order,stateRole,'d,'e)Form)) /\
(ssmConductORPStateInterp SECURE =
                    (  ((Name (PlatoonSergeant:stateRole)) controls
      (prop (SOME (SLc (incomplete:slCommand)))) )
        :((slCommand command)order,stateRole,'d,'e)Form)) /\
(ssmConductORPStateInterp COMPLETE =
                    ( TT:((slCommand command)order,stateRole,'d,'e)Form))`
 ==== Still not parting with it yet. ==== *)
(******************************************************************************)
(* "A theorem showing commands without a principal are rejected."--Prof       *)
(*  Chin, SM0Script.sml       	       	 	       			      *)
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
(* securityContext definition:                                                *)
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
(* exec psgCommand occurs if and only if PlatoonSergeant's command is         *)
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