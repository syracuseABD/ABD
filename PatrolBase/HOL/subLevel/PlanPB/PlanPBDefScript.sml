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
    (getRecon ((Name PlatoonLeader) says (prop (SOME (SLc (PL recon))))
               :((slCommand command)option, stateRole, 'd,'e)Form::xs)
    	      	        = [SOME (SLc (PL recon)):(slCommand command)option]) /\
    (getRecon (_::xs) = getRecon xs)`

val getTenativePlan_def = Define `
    (getTenativePlan ([]:((slCommand command)option, stateRole, 'd,'e)Form list) =
    	      [NONE]) /\
    (getTenativePlan ((Name PlatoonLeader) says (prop (SOME (SLc (PL tentativePlan))))
    		       :((slCommand command)option, stateRole, 'd,'e)Form::xs)
    	      	        = [SOME (SLc (PL tentativePlan)):(slCommand command)option]) /\
    (getTenativePlan (_::xs) =  getTenativePlan xs)`

val getReport_def = Define `
    (getReport ([]:((slCommand command)option, stateRole, 'd,'e)Form list) =
    	      [NONE]) /\
    (getReport (((Name PlatoonLeader) says (prop (SOME (SLc (PL report1)))))
    	          :((slCommand command)option, stateRole, 'd,'e)Form::xs)
    	      	       =  [SOME (SLc (PL report1)):(slCommand command)option]) /\
    (getReport (_::xs) = getReport xs)`

val getInitMove_def = Define `
    (getInitMove ([]:((slCommand command)option, stateRole, 'd,'e)Form list) =
    	      [NONE]) /\
    (getInitMove (((Name PlatoonSergeant) says (prop (SOME (SLc (PSG initiateMovement)))))
    		   :((slCommand command)option, stateRole, 'd,'e)Form::xs)
    	      	     = [SOME (SLc (PSG initiateMovement)):(slCommand command)option]) /\
    (getInitMove (_::xs) = getInitMove xs)`

val getPlCom_def = Define `
    (getPlCom ([]:((slCommand command)option, stateRole, 'd,'e)Form list) =
    	      invalidPlCommand)
    /\
    (getPlCom (((Name PlatoonLeader) says (prop (SOME (SLc (PL cmd)))))
    	         :((slCommand command)option, stateRole, 'd,'e)Form::xs) =
    	      	      cmd)
    /\
    (getPlCom (_::xs) = getPlCom xs)`

val getPsgCom_def = Define `
    (getPsgCom ([]:((slCommand command)option, stateRole, 'd,'e)Form list) =
    	      invalidPsgCommand)
    /\
    (getPsgCom (((Name PlatoonSergeant) says (prop (SOME (SLc (PSG cmd)))))
    	          :((slCommand command)option, stateRole, 'd,'e)Form::xs) =
    	      	      cmd)
    /\
    (getPsgCom (_::xs) = getPsgCom xs)`


val secContext_def = Define `
secContext (s:slState) (x:((slCommand command)option, stateRole, 'd,'e)Form list) =
    if (s = WARNO) then
        (if (getRecon         x = [SOME (SLc (PL recon))
	    		           :(slCommand command)option] ) /\
	    (getTenativePlan  x = [SOME (SLc (PL tentativePlan))
	    		      	   :(slCommand command)option]) /\
            (getReport        x = [SOME (SLc (PL report1))
	    		      	   :(slCommand command)option]) /\
	    (getInitMove      x = [SOME (SLc (PSG initiateMovement))
	    		      	   :(slCommand command)option])
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

 ==== End back-up copy ==== *)

val _= export_theory();
end