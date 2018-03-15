(******************************************************************)
(* BFO CONOPS with messages: created by S-K Chin, 4 December 2011 *)
(******************************************************************)

(***********
* Load necessary theories
***********)
(* Interactive mode
app load ["acl_infRules","cipherTheory","revisedMissionKeysTheory","messageCertificateTheory"];
*)

structure BFOConopsScript = struct

(* Note: in interactive mode no need to open HolKernel boolLib Parse bossLib *)
open HolKernel boolLib Parse bossLib
open acl_infRules cipherTheory revisedMissionKeysTheory messageCertificateTheory;

(***********
* create a new theory
***********)
val _ = new_theory "BFOConops";

val BFO_thm = 
let
 val a1 = ACL_ASSUM ``((Name (MKey (pubK (KStaff Alice)))) quoting (Name (MRole BFC)) says (prop (MC go))):(commands,missionPrincipals,'Int,'Sec)Form``
 val a2 = ACL_ASSUM ``((Name (MKey (pubK (KCA BFCA)))) says (Name (MKey (pubK (KStaff Alice)))) speaks_for (Name (MStaff Alice))):(commands,missionPrincipals,'Int,'Sec)Form``
 val a3 = ACL_ASSUM ``((Name (MKey (pubK (KCA JFCA)))) says (Name (MKey (pubK (KCA BFCA)))) speaks_for (Name (MCA BFCA))):(commands,missionPrincipals,'Int,'Sec)Form`` 
 val a4 = ACL_ASSUM ``reps (Name (MStaff Alice)) (Name (MRole BFC)) (prop (MC go)):(commands,missionPrincipals,'Int,'Sec)Form``
 val a5 = ACL_ASSUM ``((Name (MKey (pubK (KCA JFCA)))) speaks_for (Name (MCA JFCA))):(commands,missionPrincipals,'Int,'Sec)Form``
 val a6 = ACL_ASSUM ``((Name (MRole BFC)) controls (prop (MC go))):(commands,missionPrincipals,'Int,'Sec)Form``
 val a7 = ACL_ASSUM ``((Name (MCA JFCA)) controls ((Name (MKey (pubK (KCA BFCA)))) speaks_for (Name (MCA BFCA)))):(commands,missionPrincipals,'Int,'Sec)Form``
 val a8 = ACL_ASSUM ``((Name (MCA BFCA)) controls ((Name (MKey (pubK (KStaff Alice)))) speaks_for (Name (MStaff Alice)))):(commands,missionPrincipals,'Int,'Sec)Form``
 val a9 = ACL_ASSUM ``(prop (MC go)) impf (prop (WC launch)):(commands,missionPrincipals,'Int,'Sec)Form``
 val th10 = SPEAKS_FOR a5 a3
 val th11 = CONTROLS a7 th10
 val th12 = SPEAKS_FOR th11 a2
 val th13 = CONTROLS a8 th12
 val th14 = QUOTING_LR a1
 val th15 = SPEAKS_FOR th13 th14
 val th16 = QUOTING_RL th15
 val th17 = REPS a4 th16 a6
 val th18 = ACL_MP th17 a9
 val th19 = SAYS ``((Name (MKey (pubK (KStaff Carol)))) quoting (Name (MRole BFO)))`` th18
 val th20 = DISCH ``((M :(commands, β, missionPrincipals, 'Int, 'Sec) Kripke),
      (Oi :'Int po),(Os :'Sec po)) sat
     (prop (MC go) :(commands, missionPrincipals, 'Int, 'Sec) Form) impf
     (prop (WC launch) :(commands, missionPrincipals, 'Int, 'Sec) Form)`` th19
 val th21 = DISCH ``((M :(commands, β, missionPrincipals, 'Int, 'Sec) Kripke),
      (Oi :'Int po),(Os :'Sec po)) sat
     Name (MCA BFCA) controls
     ((Name (MKey (pubK (KStaff Alice))) speaks_for Name (MStaff Alice))
        :(commands, missionPrincipals, 'Int, 'Sec) Form)`` th20
 val th22 = DISCH ``((M :(commands, β, missionPrincipals, 'Int, 'Sec) Kripke),
      (Oi :'Int po),(Os :'Sec po)) sat
     Name (MCA JFCA) controls
     ((Name (MKey (pubK (KCA BFCA))) speaks_for Name (MCA BFCA))
        :(commands, missionPrincipals, 'Int, 'Sec) Form)`` th21
 val th23 = DISCH ``((M :(commands, β, missionPrincipals, 'Int, 'Sec) Kripke),
      (Oi :'Int po),(Os :'Sec po)) sat
     Name (MRole BFC) controls
     (prop (MC go) :(commands, missionPrincipals, 'Int, 'Sec) Form)`` th22
 val th24 = DISCH ``((M :(commands, β, missionPrincipals, 'Int, 'Sec) Kripke),
      (Oi :'Int po),(Os :'Sec po)) sat
     ((Name (MKey (pubK (KCA JFCA))) speaks_for Name (MCA JFCA))
        :(commands, missionPrincipals, 'Int, 'Sec) Form)`` th23
 val th25 = DISCH ``((M :(commands, β, missionPrincipals, 'Int, 'Sec) Kripke),
      (Oi :'Int po),(Os :'Sec po)) sat
     reps (Name (MStaff Alice)) (Name (MRole BFC))
       (prop (MC go) :(commands, missionPrincipals, 'Int, 'Sec) Form)`` th24
 val th26 = DISCH ``((M :(commands, β, missionPrincipals, 'Int, 'Sec) Kripke),
      (Oi :'Int po),(Os :'Sec po)) sat
     Name (MKey (pubK (KCA JFCA))) says
     ((Name (MKey (pubK (KCA BFCA))) speaks_for Name (MCA BFCA))
        :(commands, missionPrincipals, 'Int, 'Sec) Form)`` th25
 val th27 = DISCH ``((M :(commands, β, missionPrincipals, 'Int, 'Sec) Kripke),
      (Oi :'Int po),(Os :'Sec po)) sat
     Name (MKey (pubK (KCA BFCA))) says
     ((Name (MKey (pubK (KStaff Alice))) speaks_for Name (MStaff Alice))
        :(commands, missionPrincipals, 'Int, 'Sec) Form)`` th26
in
 DISCH ``((M :(commands, β, missionPrincipals, 'Int, 'Sec) Kripke),
      (Oi :'Int po),(Os :'Sec po)) sat
     Name (MKey (pubK (KStaff Alice))) quoting Name (MRole BFC) says
     (prop (MC go) :(commands, missionPrincipals, 'Int, 'Sec) Form)`` th27
end;

val BFO_thm = save_thm("BFO_thm",BFO_thm);

(* Generating the final message sent to weapon from the received message*)

(*****************************************)
(*** ADD YOUR PROOF OF blackBoxBFO_thm ***)
(*****************************************)

val _ = export_theory ();
val _ = print_theory "BFOConops";

end (* structure *)