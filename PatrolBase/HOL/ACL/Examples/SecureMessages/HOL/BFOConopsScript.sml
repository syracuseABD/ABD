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

(* Generating the final message sent to weapon from the received message *)

val blackBoxBFO_thm =
let
(* Signed Message from Alice as BFC *)
val BFCMessage =
ASSUME
``((M :(commands, 'world, missionPrincipals, 'Int, 'Sec) Kripke),Oi:'Int po,Os:'Sec po) msat
  MSG (From Alice) (As BFC) (To Carol)
      (Ea (pubK Carol) (plain (sym (dek1 :num))))
      (Es (sym dek1) (plain (CMD (From Alice)(As BFC)(To Carol)(MC go))))
      (sign Alice (hash (plain (CMD (From Alice)(As BFC)(To Carol)(MC go)))))``
(* Signed Key Certificate for Alice *)
val AliceCert =
ASSUME
``(((M :(commands, 'world, missionPrincipals, 'Int, 'Sec) Kripke),Oi:'Int po,Os:'Sec po) ksat
   KCert (CA BFCA) (Entity (KStaff Alice)) (SPubKey (pubK (KStaff Alice)))
            (KCrtSig (sign (KCA BFCA) (hash (plain (BFCA,KStaff Alice,(pubK (KStaff Alice))))))))``
(* Signed Key Certificate for BFCA *)
val BFCACert =
ASSUME
``(((M :(commands, 'world, missionPrincipals, 'Int, 'Sec) Kripke),Oi:'Int po,Os:'Sec po) ksat
   KCert (CA JFCA) (Entity (KCA BFCA)) (SPubKey (pubK (KCA BFCA)))
            (KCrtSig (sign (KCA JFCA) (hash (plain (JFCA,KCA BFCA,(pubK (KCA BFCA))))))))``
(* Trusted Root Role Certificate for Alice as BFC *)
val BFCCert =
ASSUME
``((M :(commands, 'world, missionPrincipals, 'Int, 'Sec) Kripke),Oi:'Int po,Os:'Sec po) rootrsat
  RootRCert (For Alice) (As BFC) (MC go)``
(* Trusted Root Key Certificate for JFCA *)
val JFCARootCert = 
ASSUME
 ``((M :(commands, 'world, missionPrincipals, 'Int, 'Sec) Kripke),Oi:'Int po,Os:'Sec po) rootksat 
    RootKCert (Entity (KCA JFCA)) (SPubKey (pubK (KCA JFCA)))``
(* The proof *)
(* Rewrite message with its interpretation *)
val th6 = REWRITE_RULE [GSYM msgSat_thm] BFCMessage
val th7 = MATCH_MP BFO_thm th6
(* Rewrite AliceCert with its interpretation *)
val th8 = REWRITE_RULE [GSYM kcertStaffSat_thm] AliceCert
val th9 = MATCH_MP th7 th8
(* Rewrite BFCACert with its interpretation *)
val th10 = REWRITE_RULE [GSYM kcertCASat_thm] BFCACert
val th11 = MATCH_MP th9 th10
(* Rewrite BFCCert with its interpretation *)
val th12 = REWRITE_RULE [rootrcertStaffInterp_thm] BFCCert
val th13 = MATCH_MP th11 th12
(* Rewrite JFCARootCert with its interpretation *)
val th14 = REWRITE_RULE [rootkcertCAInterp_thm] JFCARootCert
val th15 = MATCH_MP th13 th14
val th16 = DISCH ``((M :(commands, 'world, missionPrincipals, 'Int, 'Sec) Kripke),
      (Oi :'Int po),(Os :'Sec po)) rootksat
     RootKCert (Entity (KCA JFCA)) (SPubKey (pubK (KCA JFCA)))`` th15
val th17 = DISCH ``((M :(commands, 'world, missionPrincipals, 'Int, 'Sec) Kripke),
      (Oi :'Int po),(Os :'Sec po)) rootrsat
     RootRCert (For Alice) (As BFC) (MC go)`` th16
val th18 = DISCH ``((M :(commands, 'world, missionPrincipals, 'Int, 'Sec) Kripke),
      (Oi :'Int po),(Os :'Sec po)) ksat
     KCert (CA JFCA) (Entity (KCA BFCA)) (SPubKey (pubK (KCA BFCA)))
       (KCrtSig
          (sign (KCA JFCA) (hash (plain (JFCA,KCA BFCA,pubK (KCA BFCA))))))`` th17
val th19 = DISCH ``((M :(commands, 'world, missionPrincipals, 'Int, 'Sec) Kripke),
      (Oi :'Int po),(Os :'Sec po)) ksat
     KCert (CA BFCA) (Entity (KStaff Alice)) (SPubKey (pubK (KStaff Alice)))
       (KCrtSig
          (sign (KCA BFCA)
             (hash (plain (BFCA,KStaff Alice,pubK (KStaff Alice))))))`` th18
val th20 = DISCH ``((M :(commands, 'world, missionPrincipals, 'Int, 'Sec) Kripke),
      (Oi :'Int po),(Os :'Sec po)) msat
     MSG (From Alice) (As BFC) (To Carol)
       (Ea (pubK Carol) (plain (sym (dek1 :num))))
       (Es (sym dek1) (plain (CMD (From Alice) (As BFC) (To Carol) (MC go)))) (sign Alice (hash (plain (CMD (From Alice) (As BFC) (To Carol) (MC go)))))`` th19
in
REWRITE_RULE [SPECL [``Weapon``,``dek2:num``,``Carol``,``BFO``,``WC launch``] msgSat_thm] th20
end;

val _ = save_thm("blackBoxBFO_thm",blackBoxBFO_thm);

val _ = export_theory ();
val _ = print_theory "BFOConops";

end (* structure *)