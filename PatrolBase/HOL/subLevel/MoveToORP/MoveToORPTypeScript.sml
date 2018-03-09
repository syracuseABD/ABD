(******************************************************************************)
(* MoveToORPType contains definitions for datatypes that are used in          *)
(* the MoveToORP state machine.                                               *)
(* Contributors:                                                              *)
(*   Lori Pickering (HOL implementation),                                     *)
(*   Jesse Hall (content expert),                                             *)                       
(*   Prof. Shiu-Kai Chin (Principal Investigator).                            *)
(* Date created: 19 June 2017                                                 *)
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
(* slcommand, slState, slOutput, and stateRole                                *)
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
Datatype `slState = MOVE_TO_ORP
	 	  | PLT_FORM
	 	  | PLT_MOVE
		  | PLT_SECURE_HALT
		  | COMPLETE`

val slState_distinct_clauses = distinct_of``:slState``
val _ = save_thm("slState_distinct_clauses",slState_distinct_clauses)

val _=
Datatype `slOutput = MoveToORP
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