(***************************************************************)
(* Revised Mission Keys: Created by S-K Chin, 17 November 2011 *)
(* Based on missionKeys for C2CONOPS                           *)
(***************************************************************)

(***********
* Load necessary theories
***********)
(* Interactive mode
app load ["acl_infRules","commandTheory","missionRolesTheory","missionStaffTheory","cipherTheory"];
*)

structure revisedMissionKeysScript = struct

(* Note: in interactive mode no need to open HolKernel boolLib Parse
bossLib *) 
open HolKernel boolLib Parse bossLib 
open acl_infRules commandTheory missionRolesTheory 
     missionStaffTheory cipherTheory;

(***********
* create a new theory
***********)
val _ = new_theory "revisedMissionKeys";

(***************************)
(* Certificate Authorities *)
(***************************)
val _ = Hol_datatype `missionCA = JFCA | BFCA | GFCA`;

(***********************************************)
(* Principals who are assigned asymmetric keys *)
(***********************************************)
val _ = Hol_datatype `missionStaffCA = KStaff of missionStaff | KCA of missionCA`;


(**********************)
(* Mission Principals *)
(**********************)
val _ = 
 Hol_datatype 
 `missionPrincipals = MRole of missionRoles | MStaff of missionStaff | MCA of missionCA | MKey of missionStaffCA pKey`;

val _ = export_theory ();
val _ = print_theory "-";

end (* structure *)