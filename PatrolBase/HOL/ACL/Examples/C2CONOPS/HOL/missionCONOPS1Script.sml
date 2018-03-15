(***********************************************************)
(* High-Level CONOPS: created by S-K Chin, 9 November 2011 *)
(***********************************************************)

(***********
* Load necessary theories
***********)
(* Interactive mode
app load ["acl_infRules","commandTheory","missionRolesTheory","missioninf_rules"];
*)

structure missionCONOPS1Script = struct

(* Note: in interactive mode no need to open HolKernel boolLib Parse bossLib *)
open HolKernel boolLib Parse bossLib
open acl_infRules commandTheory missionRolesTheory missioninf_rules;

(***********
* create a new theory
***********)
val _ = new_theory "missionCONOPS1";

(*******************)
(* Launch theorems *)
(*******************)

val BFO_launch_thm =
let
 val a1 = ACL_ASSUM ``((Name BFC) says (prop (MC go))):(commands,missionRoles,'Int,'Sec)Form``
 val a2 = ACL_ASSUM ``((Name BFC) controls (prop (MC go))):(commands,missionRoles,'Int,'Sec)Form``
 val a3 = ACL_ASSUM ``(prop(MC go) impf prop(WC launch)):(commands,missionRoles,'Int,'Sec)Form``
in
 DISCH_ALL(ImpliedControlsSays (``Name BFO``) a1 a2 a3)
end;

val _ = save_thm("BFO_launch_thm",BFO_launch_thm);

val GFO_launch_thm =
let
 val a1 = ACL_ASSUM ``((Name GFC) says (prop (MC go))):(commands,missionRoles,'Int,'Sec)Form``
 val a2 = ACL_ASSUM ``((Name GFC) controls (prop (MC go))):(commands,missionRoles,'Int,'Sec)Form``
 val a3 = ACL_ASSUM ``(prop(MC go) impf prop(WC launch)):(commands,missionRoles,'Int,'Sec)Form``
in
 DISCH_ALL(ImpliedControlsSays (``Name GFO``) a1 a2 a3)
end;

val _ = save_thm("GFO_launch_thm",GFO_launch_thm);

val Weapons_launch_thm =
let
 val a1 = ACL_ASSUM ``((Name BFO) says (prop (WC launch))):(commands,missionRoles,'Int,'Sec)Form``
 val a2 = ACL_ASSUM ``((Name GFO) says (prop (WC launch))):(commands,missionRoles,'Int,'Sec)Form``
 val a3 = ACL_ASSUM ``((Name BFO) meet (Name GFO) controls (prop(WC launch))):(commands,missionRoles,'Int,'Sec)Form``
in
 DISCH_ALL(DualControl a1 a2 a3)
end;

val _ = save_thm("Weapons_launch_thm",Weapons_launch_thm);

(******************)
(* Abort theorems *)
(******************)

val BFO_abort_thm =
let 
 val a1 = ACL_ASSUM ``((Name BFC) says (prop (MC nogo))):(commands,missionRoles,'Int,'Sec)Form``
 val a2 = ACL_ASSUM ``((Name BFC) controls (prop (MC nogo))):(commands,missionRoles,'Int,'Sec)Form``
 val a3 = ACL_ASSUM ``(prop(MC nogo) impf prop(WC abort)):(commands,missionRoles,'Int,'Sec)Form``
in
 DISCH_ALL(ImpliedControlsSays ``Name BFO`` a1 a2 a3)
end;

val _ = save_thm("BFO_abort_thm",BFO_abort_thm);

val GFO_abort_thm =
let 
 val a1 = ACL_ASSUM ``((Name GFC) says (prop (MC nogo))):(commands,missionRoles,'Int,'Sec)Form``
 val a2 = ACL_ASSUM ``((Name GFC) controls (prop (MC nogo))):(commands,missionRoles,'Int,'Sec)Form``
 val a3 = ACL_ASSUM ``(prop(MC nogo) impf prop(WC abort)):(commands,missionRoles,'Int,'Sec)Form``
in
 DISCH_ALL(ImpliedControlsSays ``Name GFO`` a1 a2 a3)
end;

val _ = save_thm("GFO_abort_thm",GFO_abort_thm);

val BFO_weapons_abort_thm =
let
 val a1 = ACL_ASSUM ``((Name BFO) says (prop (WC abort))):(commands,missionRoles,'Int,'Sec)Form``
 val a2 = ACL_ASSUM 
 ``(((Name BFO) controls (prop (WC abort))) andf 
   ((Name GFO) controls (prop (WC abort)))):(commands,missionRoles,'Int,'Sec)Form``
in
 DISCH_ALL(AltControls1 a1 a2)
end;

val _ = save_thm("BFO_weapons_abort_thm",BFO_weapons_abort_thm);

val GFO_weapons_abort_thm =
let
 val a1 = ACL_ASSUM ``((Name GFO) says (prop (WC abort))):(commands,missionRoles,'Int,'Sec)Form``
 val a2 = ACL_ASSUM 
 ``(((Name BFO) controls (prop (WC abort))) andf ((Name GFO) controls 
   (prop (WC abort)))):(commands,missionRoles,'Int,'Sec)Form``
in
 DISCH_ALL(AltControls2 a1 a2)
end;

val _ = save_thm("GFO_weapons_abort_thm",GFO_weapons_abort_thm);

val _ = export_theory ();
val _ = print_theory "missionCONOPS1";

end (* structure *)