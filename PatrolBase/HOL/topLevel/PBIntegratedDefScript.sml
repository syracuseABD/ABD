(******************************************************************************)
(* PBIntegratedDefTheory                                                      *)
(* Author: Lori Pickering                                                     *)
(* Date: 7 May 2018                                                           *)
(* Definitions for ssmPBIntegratedTheory.                                     *)
(******************************************************************************)
structure PBIntegratedDefScript = struct

(* ===== Interactive Mode ====
app load  ["TypeBase", "listTheory","optionTheory",
           "uavUtilities",
	  "OMNITypeTheory",
	  "PBIntegratedDefTheory","PBTypeIntegratedTheory"];

open TypeBase listTheory optionTheory
     aclsemanticsTheory aclfoundationTheory
     uavUtilities
     OMNITypeTheory
     PBIntegratedDefTheory PBTypeIntegratedTheory
 ==== end Interactive Mode ==== *)

open HolKernel Parse boolLib bossLib;
open TypeBase listTheory optionTheory
open  uavUtilities
open OMNITypeTheory  PBTypeIntegratedTheory

val _ = new_theory "PBIntegratedDef";
(* -------------------------------------------------------------------------- *)
(* state Interpretation function                                              *)
(* -------------------------------------------------------------------------- *)
(* This function doesn't do anything but is necessary to specialize other     *)
(* theorems.                                                                  *)
(* -------------------------------------------------------------------------- *)
val secContext_def = Define `
    secContext (x:((slCommand command)option, stateRole, 'd,'e)Form list) =
        [(TT:((slCommand command)option, stateRole, 'd,'e)Form)]`

val secHelper =
Define`
  (secHelper (cmd:omniCommand) =
     [(Name Omni) controls prop (SOME (SLc (OMNI (cmd:omniCommand))))])`

val getOmniCommand_def =
Define`
  (getOmniCommand ([]:((slCommand command)option, stateRole, 'd,'e)Form list)
  		      = invalidOmniCommand:omniCommand) /\
  (getOmniCommand (((Name Omni) controls prop (SOME (SLc (OMNI cmd))))::xs)
  		      = (cmd:omniCommand)) /\
  (getOmniCommand ((x:((slCommand command)option, stateRole, 'd,'e)Form)::xs)
  		      =  (getOmniCommand xs))`

val secAuthorization_def =
Define`
  (secAuthorization (xs:((slCommand command)option, stateRole,'d,'e)Form list)
  		  = secHelper (getOmniCommand xs)) `


val secContext_def =
Define`
 (secContext (PLAN_PB) ((x:((slCommand command)option, stateRole, 'd,'e)Form)::xs) =
 	[(prop (SOME (SLc (OMNI (ssmPlanPBComplete))))
	 :((slCommand command)option, stateRole, 'd,'e)Form) impf
	 (Name PlatoonLeader) controls prop (SOME (SLc (PL crossLD)))
	  :((slCommand command)option, stateRole, 'd,'e)Form])          /\
 (secContext (MOVE_TO_ORP) ((x:((slCommand command)option, stateRole, 'd,'e)Form)::xs) =
 	[prop (SOME (SLc  (OMNI (ssmMoveToORPComplete)))) impf
	 (Name PlatoonLeader) controls prop (SOME (SLc (PL conductORP)))]) /\
 (secContext (CONDUCT_ORP) ((x:((slCommand command)option, stateRole, 'd,'e)Form)::xs) =
 	[prop (SOME (SLc (OMNI (ssmConductORPComplete)))) impf
	 (Name PlatoonLeader) controls prop (SOME (SLc (PL moveToPB)))]) /\
 (secContext (MOVE_TO_PB) ((x:((slCommand command)option, stateRole, 'd,'e)Form)::xs) =
 	[prop (SOME (SLc (OMNI (ssmMoveToPBComplete)))) impf
	 (Name PlatoonLeader) controls prop (SOME (SLc (PL conductPB)))]) /\
 (secContext (CONDUCT_PB) ((x:((slCommand command)option, stateRole, 'd,'e)Form)::xs) =
 	[prop (SOME (SLc (OMNI (ssmConductPBComplete)))) impf
	 (Name PlatoonLeader) controls prop (SOME (SLc (PL completePB)))])`

(* ===== Area 52 ====

 ==== End Area 52 ==== *)

val _= export_theory();
end