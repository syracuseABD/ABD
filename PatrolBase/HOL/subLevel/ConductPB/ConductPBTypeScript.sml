(******************************************************************************)
(* ConductPBType contains definitions for datatypes that are used in          *)
(* the conductPB state machine.                                               *)
(* Contributors:                                                              *)
(*   Lori Pickering (HOL implementation),                                     *)
(*   Jesse Hall (content expert),                                             *)                       
(*   Prof. Shiu-Kai Chin (Principal Investigator).                            *)
(* Date created: 16 June 2017                                                 *)
(******************************************************************************)
structure ConductPBTypeScript = struct

(* ===== Interactive Mode ====
app load ["TypeBase"];
open TypeBase 
 ==== end Interactive Mode ==== *)


open HolKernel Parse boolLib bossLib;
open TypeBase

val _ = new_theory "ConductPBType";
(* -------------------------------------------------------------------------- *)
(* slcommand, slState, slOutput, and stateRole                                *)
(* -------------------------------------------------------------------------- *)
(******************commands *******************************************)
val _=
Datatype `plCommandPB = securePB
	 	    | withdrawPB
		    | completePB
		    | plIncompletePB`

val plCommandPB_distinct_clauses = distinct_of``:plCommandPB``
val _ = save_thm("plCommandPB_distinct_clauses",plCommandPB_distinct_clauses)

val _=
Datatype `psgCommandPB = actionsInPB
  	 	     | psgIncompletePB`

val psgCommandPB_distinct_clauses = distinct_of``:psgCommandPB``
val _ = save_thm("psgCommandPB_distinct_clauses",psgCommandPB_distinct_clauses)

val _=
Datatype `slCommand = PL  plCommandPB
	 	    | PSG psgCommandPB`
		    
val slCommand_distinct_clauses = distinct_of``:slCommand``
val _ = save_thm("slCommand_distinct_clauses",slCommand_distinct_clauses)

val slCommand_one_one = one_one_of``:slCommand``
val _ = save_thm("slCommand_one_one",slCommand_one_one)
 
(******************states *******************************************)
val _=
Datatype `slState = CONDUCT_PB
	 	  | SECURE_PB
		  | ACTIONS_IN_PB
		  | WITHDRAW_PB
		  | COMPLETE_PB`

val slState_distinct_clauses = distinct_of``:slState``
val _ = save_thm("slState_distinct_clauses",slState_distinct_clauses)

(******************output *******************************************)

val _=
Datatype `slOutput = ConductPB
	 	   | SecurePB
	 	   | ActionsInPB
		   | WithdrawPB
		   | CompletePB
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