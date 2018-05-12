(******************************************************************************)
(* PBTypeIntegrated                                                           *)
(* Author: Lori Pickering                                                     *)
(* Date 12 May 2018                                                           *)
(* This theory contains the type definitions for ssmPBIntegrated              *)
(******************************************************************************)
structure PBTypeIntegratedScript = struct


(* ===== Interactive Mode ====
app load ["TypeBase"]
open TypeBase 
 ==== end Interactive Mode ==== *)


open HolKernel Parse boolLib bossLib;
open TypeBase

val _= new_theory "PBTypeIntegrated";

(******************************************************************************)
(* Define types								      *)
(******************************************************************************)	
val _=
Datatype `plCommand = crossLD  (* Move to MOVE_TO_ORP state *)
		    | conductORP
		    | moveToPB
		    | conductPB
		    | completePB
		    | incomplete`

val plCommand_distinct_clauses = distinct_of``:plCommand``
val _= save_thm("plCommand_distinct_clauses",
		 plCommand_distinct_clauses)

val _= 
Datatype `omniCommand = ssmPlanPBComplete
	 	    | ssmMoveToORPComplete
		    | ssmConductORPComplete
		    | ssmMoveToPBComplete
		    | ssmConductPBComplete`

val omniCommand_distinct_clauses = distinct_of``:omniCommand``
val _= save_thm("omniCommand_distinct_clauses",
		 omniCommand_distinct_clauses)


val _=
Datatype `slCommand = PL plCommand
	 	    | OMNI omniCommand`


val slCommand_distinct_clauses = distinct_of``:slCommand``
val _= save_thm("slCommand_distinct_clauses",
		 slCommand_distinct_clauses)


val slCommand_one_one = one_one_of``:slCommand``
val _= save_thm("slCommand_one_one", slCommand_one_one)



val _=
Datatype `stateRole = PlatoonLeader | Omni`

val stateRole_distinct_clauses = distinct_of``:stateRole``
val _= save_thm("stateRole_distinct_clauses",
		 stateRole_distinct_clauses)


val _=
Datatype `slState = PLAN_PB
	 	  | MOVE_TO_ORP
		  | CONDUCT_ORP
		  | MOVE_TO_PB
		  | CONDUCT_PB
		  | COMPLETE_PB`

val slState_distinct_clauses = distinct_of``:slState``
val _ = save_thm("slState_distinct_clauses",slState_distinct_clauses)

val _=
Datatype `slOutput = PlanPB
	 	   | MoveToORP
		   | ConductORP
		   | MoveToPB
		   | ConductPB
		   | CompletePB
		   | unAuthenticated
		   | unAuthorized`

val slOutput_distinct_clauses = distinct_of``:slOutput``
val _ = save_thm("slOutput_distinct_clauses",slOutput_distinct_clauses)


val _= export_theory();
end
