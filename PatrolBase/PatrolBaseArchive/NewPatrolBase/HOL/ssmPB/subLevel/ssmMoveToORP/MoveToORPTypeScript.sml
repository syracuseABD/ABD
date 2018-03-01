(******************************************************************************)
(* moveToORPType contains definitions for datatypes that are used in          *)
(* the moveToORP state machine machine ssmMoveToORP.                          *)
(* Author: Lori Pickering in collaboration with Jesse Nathaniel Hall          *)
(* Date: 13 July 2017                                                         *)
(******************************************************************************)
structure MoveToORPScript = struct

(* ===== Interactive Mode ====
app load ["TypeBase"]
open TypeBase 
 ==== end Interactive Mode ==== *)


open HolKernel Parse boolLib bossLib;
open TypeBase

val _ = new_theory "MoveToORPType";
(* -------------------------------------------------------------------------- *)
(* slcommand, slState, slOutput, and slLeader                                 *)
(* -------------------------------------------------------------------------- *)
val _=
Datatype `slCommand = pltForm
		    | pltMove
		    | pltSecureHalt
		    | complete
		    | incomplete`
		    
val slCommand_distinct_clauses = distinct_of``:slCommand``
val _ = save_thm("slCommand_distinct_clauses",slCommand_distinct_clauses)

val _=
Datatype `slState = PLAN_PB
	 	  | PLT_FORM
	 	  | PLT_MOVE
		  | PLT_SECURE_HALT
		  | COMPLETE`

val slState_distinct_clauses = distinct_of``:slState``
val _ = save_thm("slState_distinct_clauses",slState_distinct_clauses)

val _=
Datatype `slOutput = PLTPlan
	 	   | PLTForm
	 	   | PLTMove
		   | PLTSecureHalt
		   | Complete
		   | unAuthorized
		   | unAuthenticated`

val slOutput_distinct_clauses = distinct_of``:slOutput``
val _ = save_thm("slOutput_distinct_clauses",slOutput_distinct_clauses)

val _=
Datatype `stateRole = PlatoonLeader`

val _ = export_theory();

end