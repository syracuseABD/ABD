(*******************************************************)
(* Mission roles: Created by S-K Chin, 8 November 2011 *)
(*******************************************************)

(***********
* Load necessary theories
***********)
(* Interactive mode
app load ["acl_infRules","commandTheory"];
*)

structure missionRolesScript = struct

(* Note: in interactive mode no need to open HolKernel boolLib Parse bossLib *)
open HolKernel boolLib Parse bossLib
open acl_infRules commandTheory;

(***********
* create a new theory
***********)
val _ = new_theory "missionRoles";

(*************************************)
(* Define datatype for mission roles *)
(*************************************)
val _= Hol_datatype `missionRoles = BFC | GFC | BFO | GFO`;

(********************************************)
(* Prove Implied Controls with Says Theorem *)
(********************************************)
val ImpliedControlsSays_thm =
let
 val a1 = ACL_ASSUM ``(P says s1):('Prop,'pName,'Int,'Sec)Form``
 val a2 = ACL_ASSUM ``(P controls s1):('Prop,'pName,'Int,'Sec)Form``
 val a3 = ACL_ASSUM ``(s1 impf s2):('Prop,'pName,'Int,'Sec)Form``
 val th4 = CONTROLS a2 a1
 val th5 = ACL_MP th4 a3
 val th6 = SAYS ``Q:'pName Princ`` th5
 val th7 = 
 DISCH ``((M :('Prop, β, 'pName, 'Int, 'Sec) Kripke),(Oi :'Int po),
        (Os :'Sec po)) sat (s1 :('Prop, 'pName, 'Int, 'Sec) Form) impf
         (s2 :('Prop, 'pName, 'Int, 'Sec) Form)`` th6
 val th8 = 
 DISCH ``((M :('Prop, β, 'pName, 'Int, 'Sec) Kripke),(Oi :'Int po),
      (Os :'Sec po)) sat (P :'pName Princ) controls 
      (s1 :('Prop, 'pName, 'Int, 'Sec) Form)`` th7
 val th9 =
 DISCH ``((M :('Prop, β, 'pName, 'Int, 'Sec) Kripke),(Oi :'Int po),
      (Os :'Sec po)) sat (P :'pName Princ) says 
      (s1 :('Prop, 'pName, 'Int, 'Sec) Form)`` th8
in
 GEN ``Q:'pName Princ`` th9
end;

val ImpliedControlsSays_thm = 
 save_thm("ImpliedControlsSays_thm",ImpliedControlsSays_thm);

(******************************)
(* Prove Dual Control Theorem *)
(******************************)

val DualControl_thm =
let
 val a1 = ACL_ASSUM ``(P says s):('Prop,'pName,'Int,'Sec)Form``
 val a2 = ACL_ASSUM ``(Q says s):('Prop,'pName,'Int,'Sec)Form``
 val a3 = ACL_ASSUM ``(P meet Q controls s):('Prop,'pName,'Int,'Sec)Form``
 val th4 = ACL_CONJ a1 a2
 val th5 = AND_SAYS_RL th4
 val th6 = CONTROLS a3 th5
 val th7 = 
 DISCH ``((M :('Prop, 'b, 'pName, 'Int, 'Sec) Kripke),(Oi :'Int po),
      (Os :'Sec po)) sat (P :'pName Princ) meet (Q :'pName Princ) controls
      (s :('Prop, 'pName, 'Int, 'Sec) Form)`` th6
 val th8 =
 DISCH ``((M :('Prop, 'b, 'pName, 'Int, 'Sec) Kripke),(Oi :'Int po),
      (Os :'Sec po)) sat (Q :'pName Princ) says 
      (s :('Prop, 'pName, 'Int, 'Sec) Form)`` th7
in
 DISCH ``((M :('Prop, 'b, 'pName, 'Int, 'Sec) Kripke),(Oi :'Int po),
      (Os :'Sec po)) sat
     (P :'pName Princ) says (s :('Prop, 'pName, 'Int, 'Sec) Form)`` th8
end;

val DualControl_thm =
 save_thm("DualControl_thm",DualControl_thm);

(**************************)
(* Alternate Controls (1) *)
(**************************)

val AlternateControls1_thm =
let
 val a1 = ACL_ASSUM ``(P says f):('Prop,'pName,'Int,'Sec)Form``
 val a2 = ACL_ASSUM ``(P controls f andf Q controls f):('Prop,'pName,'Int,'Sec)Form``
 val th3 = ACL_SIMP1 a2
 val th4 = CONTROLS th3 a1
 val th5 = DISCH ``((M :('Prop, 'b, 'pName, 'Int, 'Sec) Kripke),(Oi :'Int po),
      (Os :'Sec po)) sat
     (P :'pName Princ) controls (f :('Prop, 'pName, 'Int, 'Sec) Form) andf
     (Q :'pName Princ) controls f`` th4
in
 DISCH ``((M :('Prop, 'b, 'pName, 'Int, 'Sec) Kripke),(Oi :'Int po),
      (Os :'Sec po)) sat
     (P :'pName Princ) says (f :('Prop, 'pName, 'Int, 'Sec) Form)`` th5
end;

val AlternateControls1_thm =
 save_thm("AlternateControls1_thm",AlternateControls1_thm);

(**************************)
(* Alternate Controls (2) *)
(**************************)

val AlternateControls2_thm =
let
 val a1 = ACL_ASSUM ``(Q says f):('Prop,'pName,'Int,'Sec)Form``
 val a2 = ACL_ASSUM ``(P controls f andf Q controls f):('Prop,'pName,'Int,'Sec)Form``
 val th3 = ACL_SIMP2 a2
 val th4 = CONTROLS th3 a1
 val th5 = DISCH ``((M :('Prop, 'b, 'pName, 'Int, 'Sec) Kripke),(Oi :'Int po),
      (Os :'Sec po)) sat
     (P :'pName Princ) controls (f :('Prop, 'pName, 'Int, 'Sec) Form) andf
     (Q :'pName Princ) controls f`` th4
in
 DISCH ``((M :('Prop, 'b, 'pName, 'Int, 'Sec) Kripke),(Oi :'Int po),
      (Os :'Sec po)) sat
     (Q :'pName Princ) says (f :('Prop, 'pName, 'Int, 'Sec) Form)`` th5
end;

val AlternateControls2_thm =
 save_thm("AlternateControls2_thm",AlternateControls2_thm);

val _ = export_theory ();
val _ = print_theory "missionRoles";

end (* structure *)