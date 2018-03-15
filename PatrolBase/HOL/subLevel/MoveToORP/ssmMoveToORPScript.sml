(******************************************************************************)
(* ssmMoveToORP defines a sub-level state machine for the patrol base.        *)
(* Each state, save for the end states, has sub-level state machines, and     *)
(* some have sub-sub-level state machines.  These are implemented in separate *)
(* theories.                                                                  *)
(* Contributors:                                                              *)
(*   Lori Pickering (HOL implementation),                                     *)
(*   Jesse Hall (content expert),                                             *)                       
(*   Prof. Shiu-Kai Chin (Principal Investigator).                            *)
(* Date created: 19 June 2017                                                 *)
(******************************************************************************)

structure ssmMoveToORPScript = struct

(* ===== Interactive Mode ====
app load ["TypeBase", "listTheory","optionTheory",
          "acl_infRules","aclDrulesTheory","aclrulesTheory",
    	  "satListTheory","ssm11Theory","ssminfRules",
	  "OMNITypeTheory", "MoveToORPTypeTheory"];
open TypeBase listTheory optionTheory
     acl_infRules aclDrulesTheory aclrulesTheory
     satListTheory ssm11Theory ssminfRules
     OMNITypeTheory MoveToORPTypeTheory


ssmMoveToORPTheory
 ==== end Interactive Mode ==== *)

open HolKernel Parse boolLib bossLib;
open TypeBase listTheory optionTheory
open acl_infRules aclDrulesTheory aclrulesTheory
open satListTheory ssm11Theory ssminfRules
open OMNITypeTheory MoveToORPTypeTheory

val _ = new_theory "ssmMoveToORP";

(* -------------------------------------------------------------------------- *)
(* Define the next state function for the state machine.                      *)
(* -------------------------------------------------------------------------- *)
val moveToORPNS_def =
Define
`
(* executing *)
 (moveToORPNS MOVE_TO_ORP     (exec (SLc pltForm))       = PLT_FORM)        /\
 (moveToORPNS MOVE_TO_ORP     (exec (SLc incomplete))    = MOVE_TO_ORP)     /\
 (moveToORPNS PLT_FORM        (exec (SLc pltMove))       = PLT_MOVE)        /\
 (moveToORPNS PLT_FORM        (exec (SLc incomplete))    = PLT_FORM)        /\
 (moveToORPNS PLT_MOVE        (exec (SLc pltSecureHalt)) = PLT_SECURE_HALT) /\
 (moveToORPNS PLT_MOVE        (exec (SLc incomplete))    = PLT_MOVE)        /\
 (moveToORPNS PLT_SECURE_HALT (exec (SLc complete))      = COMPLETE)        /\
 (moveToORPNS PLT_SECURE_HALT (exec (SLc incomplete))    = PLT_SECURE_HALT) /\
(* trapping *) 
 (moveToORPNS (s:slState)     (trap (SLc (cmd:slCommand)))  = s)            /\
(* discarding *)
 (moveToORPNS (s:slState)     (discard (SLc (cmd:slCommand))) = s)`


(* -------------------------------------------------------------------------- *)
(* Define next-output function for the state machine                          *)
(* -------------------------------------------------------------------------- *)
val moveToORPOut_def =
Define
`
(* executing *)
 (moveToORPOut MOVE_TO_ORP     (exec (SLc pltForm))       = PLTForm)       /\
 (moveToORPOut MOVE_TO_ORP     (exec (SLc incomplete))    = MoveToORP)     /\
 (moveToORPOut PLT_FORM        (exec (SLc pltMove))       = PLTMove)       /\
 (moveToORPOut PLT_FORM        (exec (SLc incomplete))    = PLTForm)       /\
 (moveToORPOut PLT_MOVE        (exec (SLc pltSecureHalt)) = PLTSecureHalt) /\
 (moveToORPOut PLT_MOVE        (exec (SLc incomplete))    = PLTMove)       /\
 (moveToORPOut PLT_SECURE_HALT (exec (SLc complete))      = Complete)      /\
 (moveToORPOut PLT_SECURE_HALT (exec (SLc incomplete))    = PLTSecureHalt) /\
(* trapping *) 
 (moveToORPOut (s:slState)      (trap (SLc (cmd:slCommand)))  = unAuthorized) /\
(* discarding *)
 (moveToORPOut (s:slState)     (discard (SLc (cmd:slCommand))) = unAuthenticated)`


(******************************************************************************)
(* Input Authentication                                                       *)
(******************************************************************************)
val authTestMoveToORP_def =
Define
`(authTestMoveToORP
 ((Name PlatoonLeader) says (prop  (cmd:(slCommand command)order))
 	:((slCommand command)order,stateRole,'d,'e)Form) = T) /\
 (authTestMoveToORP _= F)`


(******************************************************************************)
(* "State Interpretation: this is the trivial assumption TT, as the machine   *)
(* state has no influence on access privileges"--Prof. Chin, SM0Script.sml    *)
(******************************************************************************)
val ssmMoveToORPStateInterp_def =
Define
`ssmMoveToORPStateInterp (state:slState state) =
                    (TT:((slCommand command)order,stateRole,'d,'e)Form)`


(******************************************************************************)
(* "A theorem showing commands without a principal are rejected."--Prof       *)
(*  Chin, SM0Script.sml       	       	 	       			      *)
(******************************************************************************)
val authTestMoveToORP_cmd_reject_lemma =
TAC_PROOF(
 ([],
  ``!cmd. ~(authTestMoveToORP
      ((prop (SOME cmd)):((slCommand command)order,stateRole,'d,'e)Form))``),
PROVE_TAC[authTestMoveToORP_def])

val _ = save_thm("authTestMoveToORP_cmd_reject_lemma",
                 authTestMoveToORP_cmd_reject_lemma)


(* -------------------------------------------------------------------------- *)
(* securityContext definition: PlatoonLeader authorized on any slCommand      *)
(* (defined in PBTypeScript.sml)                                              *)
(* -------------------------------------------------------------------------- *)
val secContextMoveToORP_def =
Define
`secContextMoveToORP cmd =
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
      authTestMoveToORP
      ssmMoveToORPStateInterp
      (secContextMoveToORP slCommand)
       (((Name PlatoonLeader) says (prop (SOME (SLc slCommand))))::ins)
      (s:slState state)
      (outs:(slOutput output) list) ) ==>
  ((M,Oi,Os) sat (prop (SOME (SLc slCommand))))``),
REWRITE_TAC[CFGInterpret_def,secContextMoveToORP_def,ssmMoveToORPStateInterp_def,
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
 [``authTestMoveToORP:((slCommand command)order, stateRole,'d,'e)Form -> bool``,
  ``(secContextMoveToORP slCommand):((slCommand command)order, stateRole,'d,'e)Form list``,
  ``ssmMoveToORPStateInterp:(slState state)->
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
        (authTestMoveToORP
           :((slCommand command)order, stateRole, 'd, 'e) Form -> bool)
        (ssmMoveToORPStateInterp :(slState state)
           -> ((slCommand command)order, stateRole, 'd, 'e) Form)
        ((secContextMoveToORP slCommand)
	   :((slCommand command)order, stateRole,'d,'e)Form list)
        (Name PlatoonLeader says
           (prop (SOME (SLc slCommand):(slCommand command)order):
             ((slCommand command)order, stateRole, 'd, 'e)Form)::
             (ins :((slCommand command)order, stateRole,'d,'e)Form list))
        (s:(slState state))
        (outs:(slOutput output) list) )
      (CFG
	(authTestMoveToORP
	   :((slCommand command)order, stateRole, 'd, 'e) Form -> bool)
        (ssmMoveToORPStateInterp :(slState state)
           -> ((slCommand command)order, stateRole, 'd, 'e) Form)
        ((secContextMoveToORP slCommand)
           :((slCommand command)order, stateRole,'d,'e)Form list)
        ins
        (NS
	 (s:(slState state))
	 (exec (SLc slCommand):((slCommand command)trType)) )
        (Out
	 (s:(slState state))
	 (exec (SLc slCommand):((slCommand command)trType))::outs )  )
   <=>
   authTestMoveToORP
       (Name PlatoonLeader says
           (prop (SOME (SLc slCommand):(slCommand command)order):
             ((slCommand command)order, stateRole, 'd, 'e)Form))
       /\
   CFGInterpret (M,Oi,Os)
      (CFG
        (authTestMoveToORP
           :((slCommand command)order, stateRole, 'd, 'e) Form -> bool)
        (ssmMoveToORPStateInterp :(slState state)
           -> ((slCommand command)order, stateRole, 'd, 'e) Form)
        ((secContextMoveToORP slCommand)
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