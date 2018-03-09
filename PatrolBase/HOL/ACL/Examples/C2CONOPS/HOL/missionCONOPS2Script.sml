(*************************************************************)
(* Staff-Level CONOPS: created by S-K Chin, 10 November 2011 *)
(*************************************************************)

(***********
* Load necessary theories
***********)
(* Interactive mode
app load ["acl_infRules","commandTheory","missionRolesTheory","missionStaffTheory","missioninf_rules"];
*)

structure missionCONOPS2Script = struct

(* Note: in interactive mode no need to open HolKernel boolLib Parse bossLib *)
open HolKernel boolLib Parse bossLib
open acl_infRules commandTheory missionRolesTheory missionStaffTheory missioninf_rules;

(***********
* create a new theory
***********)
val _ = new_theory "missionCONOPS2";

(*******************)
(* Launch theorems *)
(*******************)

val BFO_launch_thm2 =
let
 val a1 = 
  ACL_ASSUM 
  ``((Name (Role BFC)) controls (prop (MC go))):(commands,missionRoleStaff,'Int,'Sec)Form``
 val a2 = 
  ACL_ASSUM 
  ``(reps (Name (Staff Alice)) (Name (Role BFC)) 
          (prop (MC go))):(commands,missionRoleStaff,'Int,'Sec)Form``
 val a3 = 
  ACL_ASSUM 
  ``((Name (Staff Alice)) quoting (Name (Role BFC)) says 
    (prop (MC go))):(commands,missionRoleStaff,'Int,'Sec)Form``
 val a4 = 
  ACL_ASSUM 
  ``(prop(MC go) impf prop(WC launch)):(commands,missionRoleStaff,'Int,'Sec)Form``
in
 DISCH_ALL
  (ImpliedControlsDelegation 
  ``((Name (Staff Carol)) quoting (Name (Role BFO)))`` a1 a2 a3 a4)
end;

val _ = save_thm("BFO_launch_thm2",BFO_launch_thm2);

val GFO_launch_thm2 =
let
 val a1 = 
  ACL_ASSUM 
  ``((Name (Role GFC)) controls (prop (MC go))):(commands,missionRoleStaff,'Int,'Sec)Form``
 val a2 = 
  ACL_ASSUM 
  ``(reps (Name (Staff Bob)) (Name (Role GFC)) 
          (prop (MC go))):(commands,missionRoleStaff,'Int,'Sec)Form``
 val a3 = 
  ACL_ASSUM 
  ``((Name (Staff Bob)) quoting (Name (Role GFC)) says 
     (prop (MC go))):(commands,missionRoleStaff,'Int,'Sec)Form``
 val a4 = 
  ACL_ASSUM 
  ``(prop(MC go) impf prop(WC launch)):(commands,missionRoleStaff,'Int,'Sec)Form``
in
 DISCH_ALL
 (ImpliedControlsDelegation ``((Name (Staff Dan)) quoting (Name (Role GFO)))`` a1 a2 a3 a4)
end;

val _ = save_thm("GFO_launch_thm2",GFO_launch_thm2);


(******************)
(* Abort theorems *)
(******************)


val _ = export_theory ();
val _ = print_theory "missionCONOPS2";

end (* structure *)