(******************************************************************************)
(* ConductORPType contains definitions for datatypes that are used in         *)
(* the conductORP state machine  ssmConductORP.                               *)
(* Contributors:                                                              *)
(*   Lori Pickering (HOL implementation),                                     *)
(*   Jesse Hall (content expert),                                             *)                       
(*   Prof. Shiu-Kai Chin (Principal Investigator).                            *)
(* Date created: 16 June 2017                                                 *)
(******************************************************************************)
structure ConductORPTypeScript = struct

(* ===== Interactive Mode ====
app load ["TypeBase"];
open TypeBase 
 ==== end Interactive Mode ==== *)


open HolKernel Parse boolLib bossLib;
open TypeBase

val _ = new_theory "ConductORPType";
(* -------------------------------------------------------------------------- *)
(* slcommand, slState, slOutput, and stateRole                                *)
(* -------------------------------------------------------------------------- *)
(******************commands *******************************************)
val _=
Datatype `plCommand = secure
	 	    | withdraw
		    | complete
		    | plIncomplete`

val plCommand_distinct_clauses = distinct_of``:plCommand``
val _ = save_thm("plCommand_distinct_clauses",plCommand_distinct_clauses)

val _=
Datatype `psgCommand = actionsIn
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
Datatype `slState = CONDUCT_ORP
	 	  | SECURE
		  | ACTIONS_IN
		  | WITHDRAW
		  | COMPLETE`

val slState_distinct_clauses = distinct_of``:slState``
val _ = save_thm("slState_distinct_clauses",slState_distinct_clauses)

(******************output *******************************************)

val _=
Datatype `slOutput = ConductORP
	 	   | Secure
	 	   | ActionsIn
		   | Withdraw
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

val _ = export_theory();

end