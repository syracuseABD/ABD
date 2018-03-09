(******************************************************************************)
(* ssmPBTheory defines the top level state machine for the patrol base.       *)
(* Each state, save for the end states, have sub-level state machines, and    *)
(* some have sub-sub-level state machines.  These are implemented in separate *)
(* theories.                                                                  *)
(* Contributors:                                                              *)
(*   Lori Pickering (HOL implementation),                                     *)
(*   Jesse Hall (content expert),                                             *)                       
(*   Prof. Shiu-Kai Chin (Principal Investigator).                            *)
(* Date created: 20 June 2017                                                 *)
(******************************************************************************)
structure ssmPBScript = struct

(* ===== Interactive Mode ====
app load ["TypeBase", "listTheory","optionTheory",
          "acl_infRules","aclDrulesTheory","aclrulesTheory",
    	  "satListTheory","ssm11Theory","ssminfRules",
	  "OMNITypeTheory", "PBTypeTheory","ssmPBTheory"];
open TypeBase listTheory optionTheory
     acl_infRules aclDrulesTheory aclrulesTheory
     satListTheory ssm11Theory ssminfRules
     OMNITypeTheory PBTypeTheory ssmPBTheory
 ==== end Interactive Mode ==== *)

open HolKernel Parse boolLib bossLib;
open TypeBase listTheory optionTheory
open acl_infRules aclDrulesTheory aclrulesTheory
open satListTheory ssm11Theory ssminfRules
open OMNITypeTheory PBTypeTheory

val _ = new_theory "ssmPB";
(* -------------------------------------------------------------------------- *)
(* Define the next state function for the state machine.                      *)
(* -------------------------------------------------------------------------- *)
val PBNS_def =
Define
`
(* executing *)
 (PBNS PLAN_PB     (exec (SLc crossLD))    = MOVE_TO_ORP) /\
 (PBNS PLAN_PB     (exec (SLc incomplete)) = PLAN_PB)     /\
 (PBNS MOVE_TO_ORP (exec (SLc conductORP)) = CONDUCT_ORP) /\
 (PBNS MOVE_TO_ORP (exec (SLc incomplete)) = MOVE_TO_ORP) /\
 (PBNS CONDUCT_ORP (exec (SLc moveToPB))   = MOVE_TO_PB)  /\
 (PBNS CONDUCT_ORP (exec (SLc incomplete)) = CONDUCT_ORP) /\
 (PBNS MOVE_TO_PB  (exec (SLc conductPB))  = CONDUCT_PB)  /\
 (PBNS MOVE_TO_PB  (exec (SLc incomplete)) = MOVE_TO_PB)  /\
 (PBNS CONDUCT_PB  (exec (SLc completePB)) = COMPLETE_PB) /\
 (PBNS CONDUCT_PB  (exec (SLc incomplete)) = CONDUCT_PB)  /\
(* trapping *)
 (PBNS (s:slState) (trap (SLc (cmd:slCommand)))    = s) /\
(* discarding *)
 (PBNS (s:slState) (discard (SLc (cmd:slCommand))) = s)`

(* -------------------------------------------------------------------------- *)
(* Define next-output function for ssmPB                                      *)
(* -------------------------------------------------------------------------- *)

val PBOut_def =
Define
`
 (* executing *)
 (PBOut PLAN_PB     (exec (SLc crossLD))    = MoveToORP)  /\
 (PBOut PLAN_PB     (exec (SLc incomplete)) = PlanPB)     /\
 (PBOut MOVE_TO_ORP (exec (SLc conductORP)) = ConductORP) /\
 (PBOut MOVE_TO_ORP (exec (SLc incomplete)) = MoveToORP)  /\
 (PBOut CONDUCT_ORP (exec (SLc moveToPB))   = MoveToPB)   /\
 (PBOut CONDUCT_ORP (exec (SLc incomplete)) = ConductORP) /\
 (PBOut MOVE_TO_PB  (exec (SLc conductPB))  = ConductPB)  /\
 (PBOut MOVE_TO_PB  (exec (SLc incomplete)) = MoveToPB)   /\
 (PBOut CONDUCT_PB  (exec (SLc completePB)) = CompletePB) /\
 (PBOut CONDUCT_PB  (exec (SLc incomplete)) = ConductPB)  /\
(* trapping *) 
 (PBOut (s:slState) (trap (SLc (cmd:slCommand)))    = unAuthorized) /\
(* discarding *)
 (PBOut (s:slState) (discard (SLc (cmd:slCommand))) = unAuthenticated)`

(******************************************************************************)
(* Input Authentication                                                       *)
(******************************************************************************)
val authenticationTest_def =
Define
`(authenticationTest
 ((Name PlatoonLeader) says (prop  (cmd:(slCommand command)order))
 	:((slCommand command)order,stateRole,'d,'e)Form) = T) /\
 (authenticationTest _= F)`


(******************************************************************************)
(* "State Interpretation: this is the trivial assumption TT, as the machine   *)
(* state has no influence on access privileges"--Prof. Chin, SM0Script.sml    *)
(******************************************************************************)
val ssmPBStateInterp_def =
Define
`ssmPBStateInterp (state:slState state) =
                    (TT:((slCommand command)order,stateRole,'d,'e)Form)`


(******************************************************************************)
(* "A theorem showing commands without a principal are rejected."--Prof       *)
(*  Chin,  SM0Script.sml       	       	 	       			      *)
(******************************************************************************)
val authenticationTest_cmd_reject_lemma =
TAC_PROOF(
 ([],
  ``!cmd. ~(authenticationTest
      ((prop (SOME cmd)):((slCommand command)order,stateRole,'d,'e)Form))``),
PROVE_TAC[authenticationTest_def])

val _ = save_thm("authenticationTest_cmd_reject_lemma",
                 authenticationTest_cmd_reject_lemma)


(* -------------------------------------------------------------------------- *)
(* securityContext definition.                                                *)
(* -------------------------------------------------------------------------- *)
val secContext_def =
Define
`secContext cmd =
 [((Name PlatoonLeader) controls
      (prop (SOME (SLc cmd))) )
        :((slCommand command)order,stateRole,'d,'e)Form]`
(******************************************************************************)
(* PlatoonLeader is authorized on any slCommand                               *)
(******************************************************************************)
val PlatoonLeader_slCommand_lemma =
TAC_PROOF(
([],
``CFGInterpret ((M:((slCommand command)order,'b,stateRole,'d,'e)Kripke),Oi,Os)
   (CFG
      authenticationTest
      ssmPBStateInterp
      (secContext slCommand)
       (((Name PlatoonLeader) says (prop (SOME (SLc slCommand))))::ins)
      (s:slState state)
      (outs:(slOutput output) list) ) ==>
  ((M,Oi,Os) sat (prop (SOME (SLc slCommand))))``),
REWRITE_TAC[CFGInterpret_def,secContext_def,ssmPBStateInterp_def,satList_CONS,
	    satList_nil, sat_TT] THEN
PROVE_TAC[Controls])

val _ = save_thm("PlatoonLeader_slCommand_lemma",
		 PlatoonLeader_slCommand_lemma)
(* -------------------------------------------------------------------------- *)
(* exec slCommand occurs if and only if PlatoonLeaders's command is           *)
(* authenticated and authorized                                               *)
(* -------------------------------------------------------------------------- *)
val PlatoonLeader_exec_slCommand_justified_thm =
let
 val th1 =
 ISPECL
 [``authenticationTest:((slCommand command)order, stateRole,'d,'e)Form -> bool``,
  ``(secContext slCommand):((slCommand command)order, stateRole,'d,'e)Form list``,
  ``ssmPBStateInterp:(slState state)->
                  ((slCommand command)order, stateRole,'d,'e)Form``,
  ``Name PlatoonLeader``,``SLc slCommand:(slCommand command)``,
  ``ins:((slCommand command)order,stateRole,'d,'e)Form list``,
  ``s:(slState state)``,``outs:(slOutput output) list``]
 TR_exec_cmd_rule
in 
 TAC_PROOF(([],
  ``!(NS :(slState state) -> (slCommand command)trType -> (slState state))
     (Out :(slState state) -> (slCommand command)trType -> (slOutput output))
     (M :((slCommand command)order, 'b, stateRole, 'd, 'e) Kripke)
     (Oi :'d po)
     (Os :'e po).
    TR (M,Oi,Os) (exec (SLc slCommand):((slCommand command)trType))
      (CFG
        (authenticationTest
           :((slCommand command)order, stateRole, 'd, 'e) Form -> bool)
        (ssmPBStateInterp :(slState state)
           -> ((slCommand command)order, stateRole, 'd, 'e) Form)
        ((secContext slCommand)
	   :((slCommand command)order, stateRole,'d,'e)Form list)
        (Name PlatoonLeader says
           (prop (SOME (SLc slCommand):(slCommand command)order):
             ((slCommand command)order, stateRole, 'd, 'e)Form)::
             (ins :((slCommand command)order, stateRole,'d,'e)Form list))
        (s:(slState state))
        (outs:(slOutput output) list) )
      (CFG
	(authenticationTest
	   :((slCommand command)order, stateRole, 'd, 'e) Form -> bool)
        (ssmPBStateInterp :(slState state)
           -> ((slCommand command)order, stateRole, 'd, 'e) Form)
        ((secContext slCommand)
           :((slCommand command)order, stateRole,'d,'e)Form list)
        ins
        (NS
	 (s:(slState state))
	 (exec (SLc slCommand):((slCommand command)trType)) )
        (Out
	 (s:(slState state))
	 (exec (SLc slCommand):((slCommand command)trType))::outs )  )
   <=>
   authenticationTest
       (Name PlatoonLeader says
           (prop (SOME (SLc slCommand):(slCommand command)order):
             ((slCommand command)order, stateRole, 'd, 'e)Form))
       /\
   CFGInterpret (M,Oi,Os)
      (CFG
        (authenticationTest
           :((slCommand command)order, stateRole, 'd, 'e) Form -> bool)
        (ssmPBStateInterp :(slState state)
           -> ((slCommand command)order, stateRole, 'd, 'e) Form)
        ((secContext slCommand)
	   :((slCommand command)order, stateRole,'d,'e)Form list)
        (Name PlatoonLeader says
           (prop (SOME (SLc slCommand):(slCommand command)order):
             ((slCommand command)order, stateRole, 'd, 'e)Form)::
             (ins :((slCommand command)order, stateRole,'d,'e)Form list))
        (s:(slState state))
        (outs:(slOutput output) list) )
      /\
   (M,Oi,Os) sat
        (prop (SOME (SLc slCommand):(slCommand command)order):
           ((slCommand command)order, stateRole, 'd, 'e)Form)``),
 PROVE_TAC[th1,PlatoonLeader_slCommand_lemma])
end

val _ =
 save_thm("PlatoonLeader_exec_slCommand_justified_thm",
           PlatoonLeader_exec_slCommand_justified_thm)





val _ = export_theory();

end