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
	  "PBTypeTheory","PBIntegratedDefTheory","PBTypeIntegratedTheory"];

open TypeBase listTheory optionTheory
     aclsemanticsTheory aclfoundationTheory
     uavUtilities
     OMNITypeTheory
     PBTypeTheory PBIntegratedDefTheory PBTypeIntegratedTheory
 ==== end Interactive Mode ==== *)

open HolKernel Parse boolLib bossLib;
open TypeBase listTheory optionTheory
open  uavUtilities
open OMNITypeTheory PBTypeTheory PBTypeIntegratedTheory

val _ = new_theory "PBIntegratedDef";
(* -------------------------------------------------------------------------- *)
(* state Interpretation function                                              *)
(* -------------------------------------------------------------------------- *)
(* This function doesn't do anything but is necessary to specialize other     *)
(* theorems.                                                                  *)
(* -------------------------------------------------------------------------- *)
val secContextNull_def = Define `
    secContextNull (x:((slCommand command)option, stateRole, 'd,'e)Form list) =
        [(TT:((slCommand command)option, stateRole, 'd,'e)Form)]`

(* ===== Area 52 ====

val secContext_def =
Define`
 (secContext (PLAN_PB) ((x:((slCommand command)option, stateRole, 'd,'e)Form)::xs) =
 	[(prop (SOME (SLc (OMNI (ssmPlanPBComplete))))
	 :((slCommand command)option, stateRole, 'd,'e)Form) impf
	 (Name PlatoonLeader) controls prop (SOME (SLc (PL crossLD)))
	  :((slCommand command)option, stateRole, 'd,'e)Form]) /\
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


val (secAuthorization_rules, secAuthorization_ind, secAuthorization_cases) =
Hol_reln
``(! (cmd:omniCommand).
  (secAuthorization (x:((slCommand command)option, stateRole, 'd,'e)Form list) =
     [(Name Omni) controls prop (SOME (SLc (OMNI cmd)))
     :((slCommand command)option, stateRole, 'd,'e)Form]))``
 

val secHelper =
Define`
  (secHelper (cmd:omniCommand) =
     [(Name Omni) controls prop (SOME (SLc (OMNI cmd)))
   :((slCommand command)option, stateRole, 'd,'e)Form])`


val secAuthorization_def =
Define`
  (secAuthorization _  = secHelper (cmd:omniCommand)) `
    





These are necessary
val getOmniCommand_def =
Define`
  (getOmniCommand ([]:((slCommand command)option, stateRole, 'd,'e)Form list)
  		      = [NONE]) /\
  (getOmniCommand ((x:((slCommand command)option, stateRole, 'd,'e)Form)::xs)
  		      = if (x = (Name Omni says prop (SOME (SLc (OMNI cmd)))))
			  then [SOME (SLc (OMNI cmd))]
			  else (getOmniCommand xs))`

val getPLCommand_def =
Define`
  (getPLCommand ([]:((slCommand command)option, stateRole, 'd,'e)Form list)
  		      = [NONE]) /\
  (getPLCommand ((x:((slCommand command)option, stateRole, 'd,'e)Form)::xs)
  		      = if (x = (Name Omni says prop (SOME (SLc (PL cmd)))))
			  then [SOME (SLc (PL cmd))]
			  else (getPLCommand xs))`

 ==== End Area 52 ==== *)




val _= export_theory();
end