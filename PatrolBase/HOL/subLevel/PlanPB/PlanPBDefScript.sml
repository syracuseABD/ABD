structure PlanPBDefScript = struct

(* ===== Interactive Mode ====
app load  ["TypeBase", "listTheory","optionTheory",
           "uavUtilities",
	  "OMNITypeTheory", "PlanPBTypeTheory"];

open TypeBase listTheory optionTheory
     aclsemanticsTheory aclfoundationTheory
     uavUtilities
     OMNITypeTheory PlanPBTypeTheory
 ==== end Interactive Mode ==== *)

open HolKernel Parse boolLib bossLib;
open TypeBase listTheory optionTheory
open  uavUtilities
open OMNITypeTheory PlanPBTypeTheory

val _ = new_theory "PlanPBDef";
(***************************************************************************)
(* Stuff                                                                   *)
(***************************************************************************)
(* -------------------------------------------------------------------------- *)
(* state Interpretation function                                              *)
(* -------------------------------------------------------------------------- *)
(* This function doesn't do anything but is necessary to specialize other     *)
(* theorems.                                                                  *)
val secContextNull_def = Define `
    secContextNull (x:((slCommand command)option, stateRole, 'd,'e)Form list) =
        [(TT:((slCommand command)option, stateRole, 'd,'e)Form)]`


(* -------------------------------------------------------------------------- *)
(* Security context                                                           *)           
(* -------------------------------------------------------------------------- *)
(* mimick Prof. Chin's C2_L1R1_RB_Auth_def *)
val PL_WARNO_Auth_def = Define `
    PL_WARNO_Auth =
    ^(impfTermList
    [``(prop (SOME (SLc (PL recon))))
         :((slCommand command)option, stateRole, 'd,'e)Form``,
     ``(prop (SOME (SLc (PL tentativePlan))))
         :((slCommand command)option, stateRole, 'd,'e)Form``,
     ``(prop (SOME (SLc (PSG initiateMovement))))
         :((slCommand command)option, stateRole, 'd,'e)Form``,
     ``(Name PlatoonLeader) controls prop (SOME (SLc (PL report1)))
         :((slCommand command)option, stateRole, 'd,'e)Form``]
     ``:((slCommand command)option, stateRole, 'd,'e)Form``)`

val PL_notWARNO_Auth_def = Define `
    PL_notWARNO_Auth (cmd:plCommand) =
    if (cmd = report1) (* report1 exits WARNO state *)
    then
      (prop NONE):((slCommand command)option, stateRole, 'd,'e)Form
    else
      ((Name PlatoonLeader) says (prop (SOME (SLc (PL cmd)))
       :((slCommand command)option, stateRole, 'd,'e)Form) impf
      (((Name PlatoonLeader) controls prop (SOME (SLc (PL cmd))))
      :((slCommand command)option, stateRole, 'd,'e)Form)) `


(* Make a function to check for elements in the list *)
val getRecon_def = Define `
    (getRecon ([]:((slCommand command)option, stateRole, 'd,'e)Form list) =
    	      [NONE]) /\
    (getRecon ((Name PlatoonLeader) says (prop (SOME (SLc (PL recon))))::xs)
    	      	        = [SOME (SLc (PL recon))]) /\
    (getRecon (_::xs) = getRecon xs)`

val getTenativePlan_def = Define `
    (getTenativePlan ([]:((slCommand command)option, stateRole, 'd,'e)Form list) =
    	      [NONE]) /\
    (getTenativePlan ((Name PlatoonLeader) says (prop (SOME (SLc (PL tentativePlan))))::xs)
    	      	        = [SOME (SLc (PL tentativePlan))]) /\
    (getTenativePlan (_::xs) =  getTenativePlan xs)`

val getReport_def = Define `
    (getReport ([]:((slCommand command)option, stateRole, 'd,'e)Form list) =
    	      [NONE]) /\
    (getReport (((Name PlatoonLeader) says (prop (SOME (SLc (PL report1)))))::xs)
    	      	       =  [SOME (SLc (PL report1))]) /\
    (getReport (_::xs) = getReport xs)`

val getInitMove_def = Define `
    (getInitMove ([]:((slCommand command)option, stateRole, 'd,'e)Form list) =
    	      [NONE]) /\
    (getInitMove ((Name PlatoonSergeant) says (prop (SOME (SLc (PSG initiateMovement))))::xs)
    	      	     = [SOME (SLc (PSG initiateMovement))]) /\
    (getInitMove (_::xs) = getInitMove xs)`

val getPlCom_def = Define `
    (getPlCom ([]:((slCommand command)option, stateRole, 'd,'e)Form list) =
    	      invalidPlCommand)
    /\
    (getPlCom (((Name PlatoonLeader) says (prop (SOME (SLc (PL cmd)))))::xs) =
    	      	      cmd)
    /\
    (getPlCom (_::xs) = getPlCom xs)`

val getPsgCom_def = Define `
    (getPsgCom ([]:((slCommand command)option, stateRole, 'd,'e)Form list) =
    	      invalidPsgCommand)
    /\
    (getPsgCom (((Name PlatoonSergeant) says (prop (SOME (SLc (PSG cmd)))))::xs) =
    	      	      cmd)
    /\
    (getPsgCom (_::xs) = getPsgCom xs)`


val secContext_def = Define `
secContext (s:slState) (x:((slCommand command)option, stateRole, 'd,'e)Form list) =
    if (s = WARNO) then
        (if (getRecon         x = [SOME (SLc (PL recon))] ) /\
	    (getTenativePlan  x = [SOME (SLc (PL tentativePlan))]) /\
            (getReport        x = [SOME (SLc (PL report1))]) /\
	    (getInitMove      x = [SOME (SLc (PSG initiateMovement))])
         then [
	       PL_WARNO_Auth
	        :((slCommand command)option, stateRole, 'd,'e)Form;
		(Name PlatoonLeader) controls prop (SOME (SLc (PL recon)));
		(Name PlatoonLeader) controls prop (SOME (SLc (PL tentativePlan)));
	       (Name PlatoonSergeant) controls prop (SOME (SLc (PSG initiateMovement)))]
	 else [(prop NONE):((slCommand command)option, stateRole, 'd,'e)Form])
    else if ((getPlCom x) = invalidPlCommand)
    	 then [(prop NONE):((slCommand command)option, stateRole, 'd,'e)Form]
	 else [PL_notWARNO_Auth (getPlCom x)]`

(* ==== Back-up copy ====

val secContext_def = Define `
secContext (s:slState) (x:((slCommand command)option, stateRole, 'd,'e)Form list) =
    if (s = WARNO) then
        (if (getRecon         x = [SOME (SLc (PL recon))] ) /\
	    (getTenativePlan  x = [SOME (SLc (PL tentativePlan))]) /\
            (getReport        x = [SOME (SLc (PL report1))]) /\
	    (getInitMove      x = [SOME (SLc (PSG initiateMovement))])
         then [
	       PL_WARNO_Auth
	        :((slCommand command)option, stateRole, 'd,'e)Form;
		(Name PlatoonLeader) controls prop (SOME (SLc (PL recon)));
		(Name PlatoonLeader) controls prop (SOME (SLc (PL tentativePlan)));
	       (Name PlatoonSergeant) controls prop (SOME (SLc (PSG initiateMovement)))]
	 else [(prop NONE):((slCommand command)option, stateRole, 'd,'e)Form])
    else if ((getPlCom x) = invalidPlCommand)
    	 then [(prop NONE):((slCommand command)option, stateRole, 'd,'e)Form]
	 else [PL_notWARNO_Auth (getPlCom x)]`

val sec_def = Define `
 sec x = ^type_of (Term(`report1`)) = ^type_of (Term(`recon`)) `


val plList =
  [``receiveMission``,
   `` warno``,
   ``tentativePlan``,
   ``recon``,
   ``report1``,
   ``completePlan``,
   ``opoid``,
   ``supervise``,
   ``report2``,
   ``complete``,
   ``plIncomplete``]
   
val isPlCom_def = Define`
  (isPlCom x []      = (1 = 2)) /\ (* How to represent false in HOL? *)
  (isPlCom x (y::ys) = (x = y) \/ (isPlCom x ys))`

val isPlCommand_def = Define`
  (isPlCommand x = FOLDR (\p q. (p = q) \/ q) x plList)`

val isPlCom_def = Define`
 (isPlCom_def ([]:((slCommand command)option, stateRole, 'd,'e)Form list) =
     false) /\
 (isPlCom ((Name PlatoonLeader) says (prop (SOME (SLc (PL plCommand))))::xs) =
      if ^type_of plCommand = ^type_of recon then true else false) /\
 (isPlCom (_::xs) = isPlCom xs)`

(* This is an older version that worked! *)


val secContext_def = Define `
secContext (s:slState) (x:((slCommand command)option, stateRole, 'd,'e)Form list) =
    if (s = WARNO) then
        (if (getRecon         x = [SOME (SLc (PL recon))] ) /\
	    (getTenativePlan  x = [SOME (SLc (PL tentativePlan))]) /\
            (getReport        x = [SOME (SLc (PL report1))]) /\
	    (getInitMove      x = [SOME (SLc (PSG initiateMovement))])
         then [
	       PL_WARNO_Auth
	        :((slCommand command)option, stateRole, 'd,'e)Form;
		(Name PlatoonLeader) controls prop (SOME (SLc (PL recon)));
		(Name PlatoonLeader) controls prop (SOME (SLc (PL tentativePlan)));
	       (Name PlatoonSergeant) controls prop (SOME (SLc (PSG initiateMovement)))]
	 else [(prop NONE):((slCommand command)option, stateRole, 'd,'e)Form])
    else [PL_notWARNO_Auth (getPlCom x)]`


 ==== End back-up copy ==== *)

val _= export_theory();
end