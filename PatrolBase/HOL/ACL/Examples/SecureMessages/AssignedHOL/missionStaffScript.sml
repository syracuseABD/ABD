(********************************************************)
(* Mission staff: Created by S-K Chin, 10 November 2011 *)
(********************************************************)

(***********
* Load necessary theories
***********)
(* Interactive mode
app load ["acl_infRules","commandTheory","missionRolesTheory"];
*)

structure missionStaffScript = struct

(* Note: in interactive mode no need to open HolKernel boolLib Parse bossLib *)
open HolKernel boolLib Parse bossLib
open acl_infRules commandTheory missionRolesTheory;

(***********
* create a new theory
***********)
val _ = new_theory "missionStaff";

(*************************************)
(* Define datatype for mission staff *)
(*************************************)
val _= Hol_datatype `missionStaff = Alice | Bob | Carol | Dan | Weapon`;

(*********************************************)
(* Define combined missionRoleStaff datatype *)
(*********************************************)
val _ = Hol_datatype `missionRoleStaff = Role of missionRoles | Staff of missionStaff`;

(************************************)
(* Implied Controls with Delegation *)
(************************************)
val ImpliedControlsDelegation_thm =
let
 val a1 = ACL_ASSUM ``(Q controls f1):('Prop,'pName,'Int,'Sec)Form``
 val a2 = ACL_ASSUM ``(reps P Q f1):('Prop,'pName,'Int,'Sec)Form``;
 val a3 = ACL_ASSUM ``(P quoting Q says f1):('Prop,'pName,'Int,'Sec)Form``
 val a4 = ACL_ASSUM ``(f1 impf f2):('Prop,'pName,'Int,'Sec)Form``
 val th5 = REPS a2 a3 a1
 val th6 = SAYS ``(R:'pName Princ)`` (ACL_MP th5 a4)
 val th7 = 
 DISCH ``((M :('Prop, β, 'pName, 'Int, 'Sec) Kripke),(Oi :'Int po),
         (Os :'Sec po)) sat
         (f1 :('Prop, 'pName, 'Int, 'Sec) Form) impf
         (f2 :('Prop, 'pName, 'Int, 'Sec) Form)`` th6
 val th8 =
 DISCH ``((M :('Prop, β, 'pName, 'Int, 'Sec) Kripke),(Oi :'Int po),
       	 (Os :'Sec po)) sat
     	 (P :'pName Princ) quoting (Q :'pName Princ) says
     	 (f1 :('Prop, 'pName, 'Int, 'Sec) Form)`` th7
 val th9 =
 DISCH ``((M :('Prop, β, 'pName, 'Int, 'Sec) Kripke),(Oi :'Int po),
         (Os :'Sec po)) sat
     	 reps (P :'pName Princ) (Q :'pName Princ)
       	 (f1 :('Prop, 'pName, 'Int, 'Sec) Form)`` th8
 val th10 =
 DISCH ``((M :('Prop, β, 'pName, 'Int, 'Sec) Kripke),(Oi :'Int po),
         (Os :'Sec po)) sat
     	 (Q :'pName Princ) controls (f1 :('Prop, 'pName, 'Int, 'Sec) Form)`` th9
in
 GEN ``(R:'pName Princ)`` th10
end;

val _ = save_thm("ImpliedControlsDelegation_thm",ImpliedControlsDelegation_thm);


val _ = export_theory ();
val _ = print_theory "missionStaff";

end (* structure *)