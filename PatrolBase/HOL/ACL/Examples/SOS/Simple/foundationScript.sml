(*************************************************************)
(* Foundations of Refinement Example: version 2              *)
(* The modification is to treat messages as labeled          *)
(* transitions and eliminate them as part of configurations. *)
(* Created 26 February 2012: Shiu-Kai Chin                   *)
(*************************************************************)

(* Interactive mode


(* Disable Pretty-Printing *)
set_trace "Unicode" 0;

app load ["acl_infRules"]
*)

structure foundationScript = struct

open HolKernel boolLib Parse bossLib
open acl_infRules;

(***********
* create a new theory
***********)
val _ = new_theory "foundation";



(*****************************)
(* Major Roles as Principals *)
(*****************************)
val _ = Hol_datatype `Roles = Owner`;

(*******************)
(* Operating Modes *)
(*******************)
val _ = Hol_datatype `modes = STBY | RDY`;

(* Commands *)
val _ = Hol_datatype `Commands = enable | disable`;

(* Statements made from modes, commands, car state, and operating limits *)
val _ = Hol_datatype `Statements = MODE of modes | CMD of Commands`;

(****************************************************************************)
(* Configurations, state, and messages are represented by lists of formulas *)
(* in the access-control logic.                                             *)
(* Previously, for a formula f in the access-control logic, we ultimately   *)
(* interpreted it within the context of a Kripke structure M and partial    *)
(* orders Oi:'Int po and Os:'Sec po. This is represented as (M,Oi,Os) sat f.*)
(* The natural extension is to interpret a list of formulas [f0;..;fn] as a *)
(* conjunction: (M,Oi,Os) sat f0 /\ ... /\ (M,Oi,Os) sat fn                 *)
(****************************************************************************)

val _ = set_fixity "satList" (Infixr 540);

val satList_def =
Define
`((M:(Statements,'world,Roles,'Int,'Sec)Kripke),(Oi:'Int po),(Os:'Sec po)) satList formList =
  FOLDR 
   (\x y. x /\ y) T 
   (MAP 
    (\ (f:(Statements,Roles,'Int,'Sec)Form). 
    ((M:(Statements,'world,Roles,'Int,'Sec)Kripke),Oi:'Int po,Os:'Sec po) sat f)formList)`;

(****************************************************************************************)
(* Configurations have 2 components: (1) Mode, and (2) operating policies.              *)
(* Policies are not expected to change. Policies are represented as lists of formulas   *)
(* in the access-control logic.                                                         *)
(****************************************************************************************)

val _ = Hol_datatype `policies = Policies of (Statements,Roles,'Int,'Sec)Form list`;

val _ = Hol_datatype `certificates = Certs of (Statements,Roles,'Int,'Sec)Form list`;

val _ = Hol_datatype `messages = Messages of (Statements,Roles,'Int,'Sec)Form list`;

val _ = Hol_datatype `configuration = CFG of modes => ('Int,'Sec) certificates => ('Int,'Sec) policies`;

val _ = Hol_datatype `block = BLK of ('Int,'Sec) messages => ('Int,'Sec) configuration`;

(************************************)
(* Interpretation of configurations *)
(************************************)

val _ = set_fixity "blocksat" (Infixr 540);

val blocksat_def =
Define
`((M:(Statements,'world,Roles,'Int,'Sec)Kripke),(Oi:'Int po),(Os:'Sec po)) 
 blocksat
 BLK
  (Messages (mlist:(Statements,Roles,'Int,'Sec)Form list))
  (CFG mode 
   (Certs (clist:(Statements,Roles,'Int,'Sec)Form list))
   (Policies (plist:(Statements,Roles,'Int,'Sec)Form list))) =
  (((M:(Statements,'world,Roles,'Int,'Sec)Kripke),(Oi:'Int po),(Os:'Sec po)) satList (mlist ++ clist ++ plist))`;


(*******************************)
(* Print and export the theory *)
(*******************************)
val _ = print_theory "-";

val _ = export_theory();

end;