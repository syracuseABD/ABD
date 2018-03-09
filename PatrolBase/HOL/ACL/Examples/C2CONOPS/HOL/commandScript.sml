(*********************************************************************)
(* Mission and weapon commands: Created by S-K Chin, 8 November 2011 *)
(*********************************************************************)

(***********
* Load necessary theories
***********)
(* Interactive mode
app load ["acl_infRules"];
*)

structure commandScript = struct

open HolKernel boolLib Parse bossLib
open acl_infRules;
(***********
* create a new theory
***********)
val _ = new_theory "command";

(******************************************************************)
(* Define the datatypes for mission commands, weapon commands and *)
(* commands in general.                                           *)
(******************************************************************)

(********************)
(* Mission Commands *)
(********************)
val _ = Hol_datatype `missionCommands = go | nogo`;

(*******************)
(* Weapon Commands *)
(*******************)
val _ = Hol_datatype `weaponCommands = launch | abort`;

(**************************************************)
(* Mission and weapon commands into a single type *)
(**************************************************)
val _ = Hol_datatype `commands = MC of missionCommands | WC of weaponCommands`;

val _ = export_theory ();
val _ = print_theory "command";

end (* structure *)