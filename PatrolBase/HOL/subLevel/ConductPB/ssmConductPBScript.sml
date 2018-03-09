(******************************************************************************)
(* ssmConductPB defines a sub-level state machine for the patrol base.        *)
(* Each state, save for the end states, has a sub-level state machine, and    *)
(* some have sub-sub-level state machines.  These are implemented in separate *)
(* theories.                                                                  *)
(* Contributors:                                                              *)
(*   Lori Pickering (HOL implementation),                                     *)
(*   Jesse Hall (content expert),                                             *)                       
(*   Prof. Shiu-Kai Chin (Principal Investigator).                            *)
(* Date created: 16 June 2017                                                 *)
(******************************************************************************)

structure ssmConductPBScript = struct

(* ===== Interactive Mode ====
app load ["TypeBase", "listTheory","optionTheory",
          "acl_infRules","aclDrulesTheory","aclrulesTheory",
    	  "satListTheory","ssm11Theory","ssminfRules",
	  "OMNITypeTheory", "ConductPBTypeTheory"];
	  
	  "ssmConductPBTheory"];
open TypeBase listTheory optionTheory
     acl_infRules aclDrulesTheory aclrulesTheory
     satListTheory ssm11Theory ssminfRules
     OMNITypeTheory ConductPBTypeTheory
     ssmConductPBTheory



 ==== end Interactive Mode ==== *)

open HolKernel Parse boolLib bossLib;
open TypeBase listTheory optionTheory
open acl_infRules aclDrulesTheory aclrulesTheory
open satListTheory ssm11Theory ssminfRules
open OMNITypeTheory ConductPBTypeTheory

val _ = new_theory "ssmConductPB";

(* -------------------------------------------------------------------------- *)
(* Define the next state function for the state machine.                      *)
(* -------------------------------------------------------------------------- *)
val conductPBNS_def =
Define
`
(* executing *)
 (conductPBNS CONDUCT_PB    (exec (PL securePB))         = SECURE_PB)      /\
 (conductPBNS CONDUCT_PB    (exec (PL plIncompletePB))   = CONDUCT_PB)     /\
 (conductPBNS SECURE_PB     (exec (PSG actionsInPB))     = ACTIONS_IN_PB)  /\
 (conductPBNS SECURE_PB     (exec (PSG psgIncompletePB)) = SECURE_PB)      /\
 (conductPBNS ACTIONS_IN_PB (exec (PL withdrawPB))       = WITHDRAW_PB)    /\
 (conductPBNS ACTIONS_IN_PB (exec (PL plIncompletePB))   = ACTIONS_IN_PB)  /\
 (conductPBNS WITHDRAW_PB   (exec (PL completePB))       = COMPLETE_PB)    /\
 (conductPBNS WITHDRAW_PB   (exec (PL plIncompletePB))   = WITHDRAW_PB)    /\
(* trapping *) 
 (conductPBNS (s:slState) (trap (PL (cmd:plCommandPB)))   = s)    /\
 (conductPBNS (s:slState) (trap (PSG (cmd:psgCommandPB))) = s)    /\
(* discarding *)
 (conductPBNS (s:slState) (discard (PL (cmd:plCommandPB)))   = s) /\
 (conductPBNS (s:slState) (discard (PSG (cmd:psgCommandPB))) = s)`

(* -------------------------------------------------------------------------- *)
(* Define next-output function for the state machine                          *)
(* -------------------------------------------------------------------------- *)
val conductPBOut_def =
Define
`
(* executing *)
 (conductPBOut CONDUCT_PB    (exec (PL securePB))         = ConductPB)   /\
 (conductPBOut CONDUCT_PB    (exec (PL plIncompletePB))   = ConductPB)   /\
 (conductPBOut SECURE_PB     (exec (PSG actionsInPB))     = SecurePB)    /\
 (conductPBOut SECURE_PB     (exec (PSG psgIncompletePB)) = SecurePB)    /\
 (conductPBOut ACTIONS_IN_PB (exec (PL withdrawPB))       = ActionsInPB) /\
 (conductPBOut ACTIONS_IN_PB (exec (PL plIncompletePB))   = ActionsInPB) /\
 (conductPBOut WITHDRAW_PB   (exec (PL completePB))       = WithdrawPB)  /\
 (conductPBOut WITHDRAW_PB   (exec (PL plIncompletePB))   = WithdrawPB)  /\
(* trapping *) 
 (conductPBOut (s:slState) (trap (PL (cmd:plCommandPB)))   = unAuthorized)    /\
 (conductPBOut (s:slState) (trap (PSG (cmd:psgCommandPB))) = unAuthorized)    /\
(* discarding *)
 (conductPBOut (s:slState) (discard (PL (cmd:plCommandPB)))   = unAuthenticated) /\
 (conductPBOut (s:slState) (discard (PSG (cmd:psgCommandPB))) = unAuthenticated)`


(******************************************************************************)
(* Input Authentication                                                       *)
(******************************************************************************)
val authTestConductPB_def =
Define
`(authTestConductPB
 ((Name PlatoonLeader) says (prop  (cmd:(slCommand command)order))
 	:((slCommand command)order,stateRole,'d,'e)Form) = T) /\
 (authTestConductPB
 ((Name PlatoonSergeant) says (prop  (cmd:(slCommand command)order))
 	:((slCommand command)order,stateRole,'d,'e)Form) = T) /\
 (authTestConductPB _= F)`


(******************************************************************************)
(* "State Interpretation: this is the trivial assumption TT, as the machine   *)
(* state has no influence on access privileges"--Prof. Chin, SM0Script.sml    *)
(******************************************************************************)
val ssmConductPBStateInterp_def =
Define
`ssmConductPBStateInterp (slState:slState) = 
                    ( TT:((slCommand command)order,stateRole,'d,'e)Form)`

(******************************************************************************)
(* "A theorem showing commands without a principal are rejected."--Prof       *)
(*  Chin, SM0Script.sml       	       	 	       			      *)
(******************************************************************************)
val authTestConductPB_cmd_reject_lemma =
TAC_PROOF(
 ([],
  ``!cmd. ~(authTestConductPB
      ((prop (SOME cmd)):((slCommand command)order,stateRole,'d,'e)Form))``),
PROVE_TAC[authTestConductPB_def])

val _ = save_thm("authTestConductPB_cmd_reject_lemma",
                 authTestConductPB_cmd_reject_lemma)


(* -------------------------------------------------------------------------- *)
(* securityContext definition:                                                *)
(* -------------------------------------------------------------------------- *)
val secContextConductPB_def =
Define
`secContextConductPB (plcmd:plCommandPB)(psgcmd:psgCommandPB)(incomplete:slCommand) =
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
(* PlatoonLeader is authorized on any plCommandPB                             *)
(******************************************************************************)
val PlatoonLeader_plCommandPB_lemma =
TAC_PROOF(
([],
``CFGInterpret ((M:((slCommand command)order,'b,stateRole,'d,'e)Kripke),Oi,Os)
   (CFG
      authTestConductPB
      ssmConductPBStateInterp
      (secContextConductPB
         (plCommand:plCommandPB)(psgCommand:psgCommandPB)(incomplete:slCommand))
       (((Name PlatoonLeader) says (prop (SOME (SLc (PL plCommand)))))::ins)
      (s:slState)
      (outs:(slOutput output) list) ) ==>
  ((M,Oi,Os) sat (prop (SOME (SLc (PL plCommand)))))``),
REWRITE_TAC[CFGInterpret_def,secContextConductPB_def,ssmConductPBStateInterp_def,
		satList_CONS,satList_nil, sat_TT] THEN
PROVE_TAC[Controls])

val _ = save_thm("PlatoonLeader_plCommandPB_lemma",
		 PlatoonLeader_plCommandPB_lemma)

(* -------------------------------------------------------------------------- *)
(* exec plCommandPB occurs if and only if PlatoonLeaders's command is         *)
(* authenticated and authorized                                               *)
(* -------------------------------------------------------------------------- *)
val PlatoonLeader_exec_plCommandPB_justified_thm =
let
 val th1 =
 ISPECL
 [``authTestConductPB:((slCommand command)order, stateRole,'d,'e)Form -> bool``,
  ``(secContextConductPB
           (plCommand:plCommandPB)(psgCommand:psgCommandPB)(incomplete:slCommand))
           :((slCommand command)order, stateRole,'d,'e)Form list``,
  ``ssmConductPBStateInterp:(slState)->
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
        (authTestConductPB
           :((slCommand command)order, stateRole, 'd, 'e) Form -> bool)
        (ssmConductPBStateInterp :(slState)
           -> ((slCommand command)order, stateRole, 'd, 'e) Form)
        ((secContextConductPB
           (plCommand:plCommandPB)(psgCommand:psgCommandPB)(incomplete:slCommand))
           :((slCommand command)order, stateRole,'d,'e)Form list)
        (Name PlatoonLeader says
           (prop (SOME (SLc (PL plCommand)):(slCommand command)order):
             ((slCommand command)order, stateRole, 'd, 'e)Form)::
             (ins :((slCommand command)order, stateRole,'d,'e)Form list))
        (s:(slState))
        (outs:(slOutput output) list) )
      (CFG
	(authTestConductPB
	   :((slCommand command)order, stateRole, 'd, 'e) Form -> bool)
        (ssmConductPBStateInterp :(slState)
           -> ((slCommand command)order, stateRole, 'd, 'e) Form)
        ((secContextConductPB
           (plCommand:plCommandPB)(psgCommand:psgCommandPB)(incomplete:slCommand))
           :((slCommand command)order, stateRole,'d,'e)Form list)
        ins
        (NS
	 (s:(slState))
	 (exec (SLc (PL plCommand)):((slCommand command)trType)) )
        (Out
	 (s:(slState))
	 (exec (SLc (PL plCommand)):((slCommand command)trType))::outs )  )
   <=>
   authTestConductPB
       (Name PlatoonLeader says
           (prop (SOME (SLc (PL plCommand)):(slCommand command)order):
             ((slCommand command)order, stateRole, 'd, 'e)Form))
       /\
   CFGInterpret (M,Oi,Os)
      (CFG
        (authTestConductPB
           :((slCommand command)order, stateRole, 'd, 'e) Form -> bool)
        (ssmConductPBStateInterp :(slState)
           -> ((slCommand command)order, stateRole, 'd, 'e) Form)
        ((secContextConductPB
           (plCommand:plCommandPB)(psgCommand:psgCommandPB)(incomplete:slCommand))
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
 PROVE_TAC[th1,PlatoonLeader_plCommandPB_lemma])
end

val _ =
 save_thm("PlatoonLeader_exec_plCommandPB_justified_thm",
           PlatoonLeader_exec_plCommandPB_justified_thm)

(******************************************************************************)
(* PlatoonSergeant is authorized on any psgCommandPB                          *)
(******************************************************************************)
val PlatoonSergeant_psgCommandPB_lemma =
TAC_PROOF(
([],
``CFGInterpret ((M:((slCommand command)order,'b,stateRole,'d,'e)Kripke),Oi,Os)
   (CFG
      authTestConductPB
      ssmConductPBStateInterp
      (secContextConductPB (plCommand:plCommandPB)(psgCommand:psgCommandPB)(incomplete:slCommand))
       (((Name PlatoonSergeant) says (prop (SOME (SLc (PSG psgCommand)))))::ins)
      (s:slState)
      (outs:(slOutput output) list) ) ==>
  ((M,Oi,Os) sat (prop (SOME (SLc (PSG psgCommand)))))``),
REWRITE_TAC[CFGInterpret_def,secContextConductPB_def,ssmConductPBStateInterp_def,
		satList_CONS,satList_nil, sat_TT] THEN
PROVE_TAC[Controls])

val _ = save_thm("PlatoonSergeant_psgCommandPB_lemma",
		 PlatoonSergeant_psgCommandPB_lemma)

(* -------------------------------------------------------------------------- *)
(* exec psgCommandPB occurs if and only if PlatoonSergeant's command is       *)
(* authenticated and authorized                                               *)
(* -------------------------------------------------------------------------- *)
val PlatoonSergeant_exec_psgCommandPB_justified_thm =
let
 val th1 =
 ISPECL
 [``authTestConductPB:((slCommand command)order, stateRole,'d,'e)Form -> bool``,
  ``(secContextConductPB
           (plCommand:plCommandPB)(psgCommand:psgCommandPB)(incomplete:slCommand))
           :((slCommand command)order, stateRole,'d,'e)Form list``,
  ``ssmConductPBStateInterp:(slState)->
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
        (authTestConductPB
           :((slCommand command)order, stateRole, 'd, 'e) Form -> bool)
        (ssmConductPBStateInterp :(slState)
           -> ((slCommand command)order, stateRole, 'd, 'e) Form)
        ((secContextConductPB
           (plCommand:plCommandPB)(psgCommand:psgCommandPB)(incomplete:slCommand))
           :((slCommand command)order, stateRole,'d,'e)Form list)
        (Name PlatoonSergeant says
           (prop (SOME (SLc (PSG psgCommand)):(slCommand command)order):
             ((slCommand command)order, stateRole, 'd, 'e)Form)::
             (ins :((slCommand command)order, stateRole,'d,'e)Form list))
        (s:(slState))
        (outs:(slOutput output) list) )
      (CFG
	(authTestConductPB
	   :((slCommand command)order, stateRole, 'd, 'e) Form -> bool)
        (ssmConductPBStateInterp :(slState)
           -> ((slCommand command)order, stateRole, 'd, 'e) Form)
        ((secContextConductPB
           (plCommand:plCommandPB)(psgCommand:psgCommandPB)(incomplete:slCommand))
           :((slCommand command)order, stateRole,'d,'e)Form list)
        ins
        (NS
	 (s:(slState))
	 (exec (SLc (PSG psgCommand)):((slCommand command)trType)) )
        (Out
	 (s:(slState))
	 (exec (SLc (PSG psgCommand)):((slCommand command)trType))::outs )  )
   <=>
   authTestConductPB
       (Name PlatoonSergeant says
           (prop (SOME (SLc (PSG psgCommand)):(slCommand command)order):
             ((slCommand command)order, stateRole, 'd, 'e)Form))
       /\
   CFGInterpret (M,Oi,Os)
      (CFG
        (authTestConductPB
           :((slCommand command)order, stateRole, 'd, 'e) Form -> bool)
        (ssmConductPBStateInterp :(slState)
           -> ((slCommand command)order, stateRole, 'd, 'e) Form)
        ((secContextConductPB
           (plCommand:plCommandPB)(psgCommand:psgCommandPB)(incomplete:slCommand))
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
 PROVE_TAC[th1,PlatoonSergeant_psgCommandPB_lemma])
end

val _ =
 save_thm("PlatoonSergeant_exec_psgCommandPB_justified_thm",
           PlatoonSergeant_exec_psgCommandPB_justified_thm)

(* ==== Testing here ====
==== End Testing Here ==== *)


val _ = export_theory();

end