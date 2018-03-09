(******************************************************************************)
(* ssmMoveToPB defines a sub-level state machine for the patrol base.         *)
(* Each state, save for the end states, has sub-level state machines, and     *)
(* some have sub-sub-level state machines.  These are implemented in separate *)
(* theories.                                                                  *)
(* Contributors:                                                              *)
(*   Lori Pickering (HOL implementation),                                     *)
(*   Jesse Hall (content expert),                                             *)                       
(*   Prof. Shiu-Kai Chin (Principal Investigator).                            *)
(* Date created: 19 June 2017                                                 *)
(******************************************************************************)

structure ssmMoveToPBScript = struct

(* ===== Interactive Mode ====
app load ["TypeBase", "listTheory","optionTheory",
          "acl_infRules","aclDrulesTheory","aclrulesTheory",
    	  "satListTheory","ssm11Theory","ssminfRules",
	  "OMNITypeTheory", "MoveToPBTypeTheory"];
open TypeBase listTheory optionTheory
     acl_infRules aclDrulesTheory aclrulesTheory
     satListTheory ssm11Theory ssminfRules
     OMNITypeTheory MoveToPBTypeTheory


ssmMoveToORPTheory
 ==== end Interactive Mode ==== *)

open HolKernel Parse boolLib bossLib;
open TypeBase listTheory optionTheory
open acl_infRules aclDrulesTheory aclrulesTheory
open satListTheory ssm11Theory ssminfRules
open OMNITypeTheory MoveToPBTypeTheory

val _ = new_theory "ssmMoveToPB";

(* -------------------------------------------------------------------------- *)
(* Define the next state function for the state machine.                      *)
(* -------------------------------------------------------------------------- *)
val moveToPBNS_def =
Define
`
(* executing *)
 (moveToPBNS MOVE_TO_PB  (exec (SLc pltForm))       = PLT_FORM) /\
 (moveToPBNS MOVE_TO_PB  (exec (SLc incomplete))    = MOVE_TO_PB)  /\
 (moveToPBNS PLT_FORM    (exec (SLc pltMove))       = PLT_MOVE) /\
 (moveToPBNS PLT_FORM    (exec (SLc incomplete))    = PLT_FORM) /\
 (moveToPBNS PLT_MOVE    (exec (SLc pltHalt))       = PLT_HALT) /\
 (moveToPBNS PLT_MOVE    (exec (SLc incomplete))    = PLT_MOVE) /\
 (moveToPBNS PLT_HALT    (exec (SLc complete))      = COMPLETE) /\
 (moveToPBNS PLT_HALT    (exec (SLc incomplete))    = PLT_HALT) /\
(* trapping *) 
 (moveToPBNS (s:slState) (trap (SLc (cmd:slCommand)))    = s) /\
(* discarding *)
 (moveToPBNS (s:slState) (discard (SLc (cmd:slCommand))) = s)`


(* -------------------------------------------------------------------------- *)
(* Define next-output function for the state machine                          *)
(* -------------------------------------------------------------------------- *)
val moveToPBOut_def =
Define
`
(* executing *)
 (moveToPBOut MOVE_TO_PB  (exec (SLc pltForm))       = PLTForm)  /\
 (moveToPBOut MOVE_TO_PB  (exec (SLc incomplete))    = MoveToPB)  /\
 (moveToPBOut PLT_FORM    (exec (SLc pltMove))       = PLTMove)  /\
 (moveToPBOut PLT_FORM    (exec (SLc incomplete))    = PLTForm)  /\
 (moveToPBOut PLT_MOVE    (exec (SLc pltHalt))       = PLTHalt)  /\
 (moveToPBOut PLT_MOVE    (exec (SLc incomplete))    = PLTMove)  /\
 (moveToPBOut PLT_HALT    (exec (SLc complete))      = Complete) /\
 (moveToPBOut PLT_HALT    (exec (SLc incomplete))    = PLTHalt)  /\
(* trapping *) 
 (moveToPBOut (s:slState) (trap (SLc (cmd:slCommand)))    = unAuthorized) /\
(* discarding *)
 (moveToPBOut (s:slState) (discard (SLc (cmd:slCommand))) = unAuthenticated)`
 


(******************************************************************************)
(* Input Authentication                                                       *)
(******************************************************************************)
val authTestMoveToPB_def =
Define
`(authTestMoveToPB
 ((Name PlatoonLeader) says (prop  (cmd:(slCommand command)order))
 	:((slCommand command)order,stateRole,'d,'e)Form) = T) /\
 (authTestMoveToPB _= F)`


(******************************************************************************)
(* "State Interpretation: this is the trivial assumption TT, as the machine   *)
(* state has no influence on access privileges"--Prof. Chin, SM0Script.sml    *)
(******************************************************************************)
val ssmMoveToPBStateInterp_def =
Define
`ssmMoveToPBStateInterp (state:slState state) =
                    (TT:((slCommand command)order,stateRole,'d,'e)Form)`


(******************************************************************************)
(* "A theorem showing commands without a principal are rejected."--Prof       *)
(*  Chin, SM0Script.sml       	       	 	       			      *)
(******************************************************************************)
val authTestMoveToPB_cmd_reject_lemma =
TAC_PROOF(
 ([],
  ``!cmd. ~(authTestMoveToPB
      ((prop (SOME cmd)):((slCommand command)order,stateRole,'d,'e)Form))``),
PROVE_TAC[authTestMoveToPB_def])

val _ = save_thm("authTestMoveToPB_cmd_reject_lemma",
                 authTestMoveToPB_cmd_reject_lemma)


(* -------------------------------------------------------------------------- *)
(* securityContext definition:                                                *)
(* -------------------------------------------------------------------------- *)
val secContextMoveToPB_def =
Define
`secContextMoveToPB cmd =
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
      authTestMoveToPB
      ssmMoveToPBStateInterp
      (secContextMoveToPB slCommand)
       (((Name PlatoonLeader) says (prop (SOME (SLc slCommand))))::ins)
      (s:slState state)
      (outs:(slOutput output) list) ) ==>
  ((M,Oi,Os) sat (prop (SOME (SLc slCommand))))``),
REWRITE_TAC[CFGInterpret_def,secContextMoveToPB_def,ssmMoveToPBStateInterp_def,
		satList_CONS,satList_nil, sat_TT] THEN
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
 [``authTestMoveToPB:((slCommand command)order, stateRole,'d,'e)Form -> bool``,
  ``(secContextMoveToPB slCommand):((slCommand command)order, stateRole,'d,'e)Form list``,
  ``ssmMoveToPBStateInterp:(slState state)->
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
        (authTestMoveToPB
           :((slCommand command)order, stateRole, 'd, 'e) Form -> bool)
        (ssmMoveToPBStateInterp :(slState state)
           -> ((slCommand command)order, stateRole, 'd, 'e) Form)
        ((secContextMoveToPB slCommand)
	   :((slCommand command)order, stateRole,'d,'e)Form list)
        (Name PlatoonLeader says
           (prop (SOME (SLc slCommand):(slCommand command)order):
             ((slCommand command)order, stateRole, 'd, 'e)Form)::
             (ins :((slCommand command)order, stateRole,'d,'e)Form list))
        (s:(slState state))
        (outs:(slOutput output) list) )
      (CFG
	(authTestMoveToPB
	   :((slCommand command)order, stateRole, 'd, 'e) Form -> bool)
        (ssmMoveToPBStateInterp :(slState state)
           -> ((slCommand command)order, stateRole, 'd, 'e) Form)
        ((secContextMoveToPB slCommand)
           :((slCommand command)order, stateRole,'d,'e)Form list)
        ins
        (NS
	 (s:(slState state))
	 (exec (SLc slCommand):((slCommand command)trType)) )
        (Out
	 (s:(slState state))
	 (exec (SLc slCommand):((slCommand command)trType))::outs )  )
   <=>
   authTestMoveToPB
       (Name PlatoonLeader says
           (prop (SOME (SLc slCommand):(slCommand command)order):
             ((slCommand command)order, stateRole, 'd, 'e)Form))
       /\
   CFGInterpret (M,Oi,Os)
      (CFG
        (authTestMoveToPB
           :((slCommand command)order, stateRole, 'd, 'e) Form -> bool)
        (ssmMoveToPBStateInterp :(slState state)
           -> ((slCommand command)order, stateRole, 'd, 'e) Form)
        ((secContextMoveToPB slCommand)
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


(* ==== Testing Here ====
==== End Testing Here ==== *)


val _ = export_theory();

end