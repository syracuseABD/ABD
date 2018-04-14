(******************************************************************************)
(* PlanPBType contains definitions for datatypes that are used in             *)
(* the PlanPB state machine.                                                  *)
(* Contributors:                                                              *)
(*   Lori Pickering (HOL implementation),                                     *)
(*   Jesse Hall (content expert),                                             *)                       
(*   Prof. Shiu-Kai Chin (Principal Investigator).                            *)
(* Date created: 4 March 2018                                                 *)
(******************************************************************************)

structure PlanPBTypeScript = struct

(* ===== Interactive Mode ====
app load ["TypeBase"];
open TypeBase
 ==== end Interactive Mode ==== *)


open HolKernel Parse boolLib bossLib;
open TypeBase

val _ = new_theory "PlanPBType";


val _= Datatype `plCommand = receiveMission
       			   | warno
			   | tentativePlan
			   | recon
			   | report1
			   | completePlan
			   | opoid
			   | supervise
			   | report2
			   | complete
			   | plIncomplete
			   | invalidPlCommand`

val plCommand_distinct_clauses = distinct_of``:plCommand``
val _= save_thm("plCommand_distinct_clauses",plCommand_distinct_clauses)


val _= Datatype `psgCommand = initiateMovement
       			    | psgIncomplete
			    | invalidPsgCommand`

val psgCommand_distinct_clauses = distinct_of``:psgCommand``
val _= save_thm("psgCommand_distinct_clauses", psgCommand_distinct_clauses)

val _= Datatype `slCommand = PL plCommand
       			   | PSG psgCommand`

val slCommand_distinct_clauses = distinct_of``:slCommand``
val _= save_thm("slCommand_distinct_clauses",slCommand_distinct_clauses)

val slCommand_one_one = one_one_of``:slCommand``
val _= save_thm("slCommand_one_one",slCommand_one_one)

val _= Datatype `slState = PLAN_PB
       			 | RECEIVE_MISSION
			 | WARNO
			 | TENTATIVE_PLAN
			 | INITIATE_MOVEMENT
			 | RECON
			 | REPORT1
			 | COMPLETE_PLAN
			 | OPOID
			 | SUPERVISE
			 | REPORT2
			 | COMPLETE`


val slState_distinct_clauses = distinct_of``:slState``
val _= save_thm("slState_distinct_clauses",slState_distinct_clauses)

val _= Datatype `slOutput = PlanPB
       			  | ReceiveMission
			  | Warno
			  | TentativePlan
			  | InitiateMovement
			  | Recon
			  | Report1
			  | CompletePlan
			  | Opoid
			  | Supervise
			  | Report2
			  | Complete
			  | unAuthenticated
			  | unAuthorized`

val slOutput_distinct_clauses = distinct_of``:slOutput``
val _= save_thm("slOutput_distinct_clauses",slOutput_distinct_clauses)

val _= Datatype `stateRole = PlatoonLeader
       			   | PlatoonSergeant`

val slRole_distinct_clauses = distinct_of``:stateRole``
val _= save_thm("slRole_distinct_clauses",slRole_distinct_clauses)

val _= export_theory();

end