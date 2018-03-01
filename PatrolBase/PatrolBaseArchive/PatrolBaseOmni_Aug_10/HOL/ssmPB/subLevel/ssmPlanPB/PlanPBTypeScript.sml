(******************************************************************************)
(* ConductORPType contains definitions for datatypes that are used in   *)
(* the conductORP state machine  machine ssmConductORP.                       *)
(* Author: Lori Pickering in collaboration with Jesse Nathaniel Hall          *)
(* Date: 13 July 2017                                                         *)
(******************************************************************************)
structure PlanPBTypeScript = struct

(* ===== Interactive Mode ====
app load ["TypeBase"];
open TypeBase 
 ==== end Interactive Mode ==== *)


open HolKernel Parse boolLib bossLib;
open TypeBase

val _ = new_theory "PlanPBType";
(******************commands *******************************************)
val _=
Datatype `plCommand = receiveMission
	 	    | warno
		    | tentativePlan
		    | recon
		    | complete
		    | plIncomplete`

val plCommand_distinct_clauses = distinct_of``:plCommand``
val _ = save_thm("plCommand_distinct_clauses",plCommand_distinct_clauses)

val _=
Datatype `psgCommand = initiateMovement
  	 	     | psgIncomplete`

val psgCommand_distinct_clauses = distinct_of``:psgCommand``
val _ = save_thm("psgCommand_distinct_clauses",psgCommand_distinct_clauses)

val _=
Datatype `slCommand = PL  plCommand
	 	    | PSG psgCommand`
		    
val slCommand_distinct_clauses = distinct_of``:slCommand``
val _ = save_thm("slCommand_distinct_clauses",slCommand_distinct_clauses)

val slCommand_one_one = one_one_of``:slCommand``
val _ = save_thm("slCommand_one_one",slCommand_one_one)

(******************states *******************************************)
val _=
Datatype `slState = RECEIVE_MISSION
	 	  | WARNO
		  | TENTATIVE_PLAN
		  | INITIATE_MOVEMENT
		  | RECON
		  | COMPLETE`

val slState_distinct_clauses = distinct_of``:slState``
val _ = save_thm("slState_distinct_clauses",slState_distinct_clauses)

(******************output *******************************************)
val _=
Datatype `slOutput = ReceiveMission
	 	   | Warno
		   | TentativePlan
		   | InitiateMovement
		   | Recon
		   | Complete
		   | unAuthenticated
		   | unAuthorized`

val slOutput_distinct_clauses = distinct_of``:slOutput``
val _ = save_thm("slOutput_distinct_clauses",slOutput_distinct_clauses)

(******************principals ****************************************)
val _=
Datatype `stateRole = PlatoonLeader
	 	    | PlatoonSergeant`

val slRole_distinct_clauses = distinct_of``:stateRole``
val _ = save_thm("slRole_distinct_clauses",slRole_distinct_clauses)

val _= export_theory();

end