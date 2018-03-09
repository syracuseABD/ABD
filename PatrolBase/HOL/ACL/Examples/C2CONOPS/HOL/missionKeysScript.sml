(*******************************************************)
(* Mission Keys: Created by S-K Chin, 10 November 2011 *)
(*******************************************************)

(***********
* Load necessary theories
***********)
(* Interactive mode
app load ["acl_infRules","commandTheory","missionRolesTheory","missionStaffTheory"];
*)

structure missionKeysScript = struct

(* Note: in interactive mode no need to open HolKernel boolLib Parse bossLib *)
open HolKernel boolLib Parse bossLib
open acl_infRules commandTheory missionRolesTheory missionStaffTheory;

(***********
* create a new theory
***********)
val _ = new_theory "missionKeys";

(***************************)
(* Certificate Authorities *)
(***************************)
val _ = Hol_datatype `missionCA = JFCA | BFCA | GFCA`;

(********)
(* Keys *)
(********)
val _ = Hol_datatype `missionKey = Kjfca | Kbfca | Kgfca | Kalice | Kbob | Kcarol | Kdan`;

(**********************)
(* Mission Principals *)
(**********************)
val _ = 
 Hol_datatype 
 `missionPrincipals = MRole of missionRoles | MStaff of missionStaff | MCA of missionCA | MKey of missionKey`;

val _ = export_theory ();
val _ = print_theory "missionKeys";

end (* structure *)