(******************************************************************************)
(* PBType contains definitions for datatypes that are used in the PB state    *)
(* machine ssmPB.                                                             *)
(* Author: Lori Pickering in collaboration with Jesse Nathaniel Hall          *)
(* Date: 19 June 2017                                                         *)
(******************************************************************************)
structure PBTypeScript = struct

(* ===== Interactive Mode ====
app load ["TypeBase"]
open TypeBase 
 ==== end Interactive Mode ==== *)


open HolKernel Parse boolLib bossLib;
open TypeBase

val _ = new_theory "PBType";
(* -------------------------------------------------------------------------- *)
(* slcommand, slState, slOutput, and slLeader                                 *)
(* -------------------------------------------------------------------------- *)
val _=
Datatype `slCommand = crossLD  (* Move to MOVE_TO_ORP state *)
		    | conductORP
		    | moveToPB
		    | conductPB
		    | completePB
		    | incomplete`
		    
val slCommand_distinct_clauses = distinct_of``:slCommand``
val _ = save_thm("slCommand_distinct_clauses",slCommand_distinct_clauses)

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

val _=
Datatype `stateRole = PlatoonLeader`

val _ = export_theory();

end