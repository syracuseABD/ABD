(****************************************)
(* Message and Certificate Structures:  *)
(* Created by S-K Chin 17 November 2011 *)
(****************************************)

(***********
* Load necessary theories
***********)
(* Interactive mode
app load ["cipherTheory","revisedMissionKeysTheory"];
*)

structure messageCertificateScript = struct

open HolKernel boolLib Parse bossLib
open cipherTheory revisedMissionKeysTheory;

(***********
* create a new theory
***********)
val _ = new_theory "messageCertificate";

(************************
* THE DEFINITIONS START HERE
************************)
(* Origin *)
val _ = Hol_datatype
    `Origin = From of missionStaff`;

val staffOrigin_def =
    Define `staffOrigin(From staff) = staff`;

(* Destination *)
val _ = Hol_datatype
    `Destination = To of missionStaff`;

val staffDestination_def =
    Define `staffDestination(To staff) = staff`;

val _ = Hol_datatype
   `Role = As of missionRoles`;

val roleOrigin_def =
    Define `roleOrigin(As role) = role`;

(************************************************)
(* MESSAGE SYNTAX AND ACCESSOR FUNCTIONS        *)
(* Messages have the following components:      *)
(* 1. origin (the sender)                       *)
(* 2. role of the sender                        *)
(* 3. destination (the recipient)               *)
(* 4. symmetric data encryption key encrypted   *)
(*    by the recipient's public key             *)
(* 5. command ordered by the sender             *)
(* 6. digital signature of the order            *)
(*    prior to encryption by the data           *)
(*    encryption key                            *)
(************************************************)

val _ = Hol_datatype 
    `Message = 
     MSG of 
     Origin => 
     Role =>
     Destination => 
     (SymKey,missionStaff)asymMsg => 
     commands symMsg =>
     (commands digest, missionStaff) asymMsg`;

val msgParameters_def =
   Define
   `msgParameters
    (MSG 
     (From (sender:missionStaff))
     (As (role:missionRoles))
     (To (recipient:missionStaff))
     (enDEK:(SymKey,missionStaff)asymMsg)
     (enCMDMsg:(commands symMsg))
     (CMDMsgSig:(commands digest,missionStaff)asymMsg)) = 
    (sender,role,recipient,enDEK,enCMDMsg,CMDMsgSig)`;

val checkMSG_def =
    Define
    `checkMSG 
     (MSG 
      (From (sender:missionStaff))
      (As (role:missionRoles))
      (To (recipient:missionStaff))
      (enDEK:(SymKey,missionStaff)asymMsg)
      (enCMDMsg:(commands symMsg))
      (CMDMsgSig:(commands digest,missionStaff)asymMsg)) = 
      let dek = getMessage (deciphP (privK recipient) enDEK) in
      let msgContents = (deciphS dek enCMDMsg) in
      signVerify
       sender
       CMDMsgSig
       msgContents`;

val getCommand_def =
    Define
    `getCommand
     (MSG 
      (From (sender:missionStaff))
      (As (role:missionRoles))
      (To (recipient:missionStaff))
      (enDEK:(SymKey,missionStaff)asymMsg)
      (enCMDMsg:(commands symMsg))
      (CMDMsgSig:(commands digest,missionStaff)asymMsg)) =
     (let dek = 
        getMessage 
        (deciphP 
         (privK recipient)
         (enDEK:(SymKey,missionStaff)asymMsg))
      in
        getMessage(deciphS dek (enCMDMsg:(commands symMsg))))`;

(*************************************************************)
(* We prove that checkMSG works as expected on messages that *)
(* have the expected structure.                              *)
(*************************************************************)
(***** The form of messages/commands is as follows:
(MSG 
      (From (sender:missionStaff))
      (As (role:missionRoles))
      (To (recipient:missionStaff))
      (Ea (pubK recipient)(plain (sym dek)))
      (Es (sym dek)(plain (order:commands)))
      (sign sender (hash (plain order))))
****************************************************)

(* Show that getCommand works as anticipated *)
val getCommand_thm =
TAC_PROOF
(
([],
``getCommand
  (MSG 
   (From (sender:missionStaff))
   (As (role:missionRoles))
   (To (recipient:missionStaff))
   (Ea (pubK recipient)(plain (sym dek)))
   (Es (sym dek)(plain (order:commands)))
   (sign sender (hash (plain order)))) = order``),
 (REWRITE_TAC 
  [getCommand_def,LET_DEF,deciphP_clauses,getMessage_def] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
 REWRITE_TAC [getMessage_def, deciphS_clauses])
);
val _ = save_thm("getCommand_thm",getCommand_thm);

(* Show that checkMSG works on messages with the right form *)
val checkMSGOK =
TAC_PROOF
(
([],
``checkMSG
  (MSG 
   (From (sender:missionStaff))
   (As (role:missionRoles))
   (To (recipient:missionStaff))
   (Ea (pubK recipient)(plain (sym dek)))
   (Es (sym dek)(plain (order:commands)))
   (sign sender (hash (plain order))))``),
 (REWRITE_TAC [checkMSG_def,LET_DEF] THEN
  CONV_TAC(DEPTH_CONV(BETA_CONV)) THEN
  REWRITE_TAC [signVerifyOK,deciphP_clauses,deciphS_clauses,getMessage_def])
);

val _ = save_thm("checkMSGOK",checkMSGOK);

(****************************************************************)
(* Semantics of messages. The basic idea is when the integrity  *)
(* of a message is verified, we interpret the message as the    *)
(* sender quoting the role issuing an order.                    *)
(****************************************************************
* Define the semantic meaning function Emsg. Emsg is parameterized
* on partial orders Oi for integrity levels and Os for security levels
* and on Kripke structure
*                             KS Intrp Jfn imap smap
*
* UNIV:('w)set corresponds to W in the Kripke structure described
* in our book. UNIV is non-empty, as every type in HOL has at least
* one member.
****************************************************************)

val Emsg_def =
    Define
    `(Emsg (Oi:'Int po) (Os:'Sec po) (M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke)
     (MSG 
      (From (sender:missionStaff))
      (As (role:missionRoles))
      (To (recipient:missionStaff))
      (enDEK:(SymKey,missionStaff)asymMsg)
      (enCMDMsg:(commands symMsg))
      (CMDMsgSig:(commands digest,missionStaff)asymMsg))) =
     (let (order:commands) = 
        getCommand 
        (MSG (From sender) (As role) (To recipient) enDEK enCMDMsg CMDMsgSig)
      in
      (if (checkMSG (MSG (From sender) (As role) (To recipient) enDEK enCMDMsg CMDMsgSig))
       then 
       (Efn Oi Os M 
            (((Name (MKey (pubK (KStaff sender)))) quoting (Name (MRole role))) 
            says (prop order)))
       else {}))`;

val _ = set_fixity "msat" (Infixr 540);
val msat_def =
    Define
    `(M, Oi, Os) msat (msg:Message) = ((Emsg Oi Os M msg) = UNIV:('world) set)`;

(* Prove properties about Emsg *)

val Emsg_th1 =
TAC_PROOF
(
 ([],``(checkMSG (MSG (From sender) (As role) (To recipient) enDEK enCMDMsg CMDMsgSig)) ==> 
	((Emsg (Oi:'Int po) (Os:'Sec po) (M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke)
     (MSG 
      (From (sender:missionStaff))
      (As (role:missionRoles))
      (To (recipient:missionStaff))
      (enDEK:(SymKey,missionStaff)asymMsg)
      (enCMDMsg:(commands symMsg))
      (CMDMsgSig:(commands digest,missionStaff)asymMsg))) = 
      (let (order:commands) = 
        getCommand 
        (MSG (From sender) (As role) (To recipient) enDEK enCMDMsg CMDMsgSig)
      in
      (Efn Oi Os M 
        (((Name (MKey (pubK (KStaff sender)))) quoting (Name (MRole role))) 
            says (prop order)))))``),
(REWRITE_TAC [Emsg_def,LET_DEF] THEN
 CONV_TAC(DEPTH_CONV BETA_CONV) THEN
 DISCH_TAC THEN
 ASM_REWRITE_TAC[])
);

val Emsg_th2 =
TAC_PROOF
(
 ([],
 ``((Emsg (Oi:'Int po) (Os:'Sec po) (M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke)
      (MSG 
       (From (sender:missionStaff))
       (As (role:missionRoles))
       (To (recipient:missionStaff))
       (enDEK:(SymKey,missionStaff)asymMsg)
       (enCMDMsg:(commands symMsg))
       (CMDMsgSig:(commands digest,missionStaff)asymMsg))) = 
      (let (order:commands) = 
         getCommand 
     	    (MSG (From sender) (As role) (To recipient) enDEK enCMDMsg CMDMsgSig)
       in
        (Efn Oi Os M 
       	     (((Name (MKey (pubK (KStaff sender)))) quoting (Name (MRole role))) 
             says (prop order))))) ==>
   (let (order:commands) = 
         getCommand 
  	 (MSG (From sender) (As role) (To recipient) enDEK enCMDMsg CMDMsgSig)
    in
    (((M, Oi, Os) msat 
     (MSG 
      (From (sender:missionStaff))
      (As (role:missionRoles))
      (To (recipient:missionStaff))
      (enDEK:(SymKey,missionStaff)asymMsg)
      (enCMDMsg:(commands symMsg))
      (CMDMsgSig:(commands digest,missionStaff)asymMsg))) =  
      ((M, Oi, Os) sat 
       (((Name (MKey (pubK (KStaff sender)))) quoting (Name (MRole role))) 
       says (prop order)))))``
 ),
 (REWRITE_TAC [msat_def,LET_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN (fn th => REWRITE_TAC [th,aclrulesTheory.sat_def]))
);

val msgInterp_thm = 
save_thm
("msgInterp_thm",
 (GEN_ALL
 (CONV_RULE
  (DEPTH_CONV BETA_CONV)
   (REWRITE_RULE [LET_DEF] (IMP_TRANS Emsg_th1 Emsg_th2)))));

(* more properties of messages *)
val msgSat_thm =
save_thm("msgSat_thm",
(GENL [``recipient:missionStaff``,``dek:num``,``sender:missionStaff``,
       ``role :missionRoles``,``order :commands``,
       ``(M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke)``,
       ``Oi:'Int po``,``Os:'Sec po``](
TAC_PROOF(
([],
``((M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke),Oi:'Int po,Os:'Sec po) sat
  (((Name (MKey (pubK (KStaff sender)))) quoting (Name (MRole role))) 
       says (prop order)) =
  ((M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke),Oi:'Int po,Os:'Sec po) msat
  (MSG (From (sender:missionStaff)) (As (role:missionRoles)) (To (recipient:missionStaff))
      (Ea (pubK recipient)(plain (sym dek))) (Es (sym dek)(plain (order:commands)))
      (sign sender (hash (plain (order)))))``),
 (REWRITE_TAC [msat_def,Emsg_def,getCommand_thm,checkMSGOK,LET_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC [aclrulesTheory.sat_def])))));

(* Syntax of Certificates *)
(************************************************)
(* KEY CERTIFICATE SYNTAX AND ACCESSOR FUNCTIONS*)
(* Certificates have the following components:  *)
(* 1. Issuer: the certificate authority         *)
(* 2. Subject: the to whom key is assigned      *)
(* 3. PubKey: the publick key for Entity        *)
(* 4. digital signature of the order            *)
(*    prior to encryption by the data           *)
(*    encryption key                            *)
(************************************************)

val _ = Hol_datatype
   `Issuer = CA of missionCA`;

val _ = Hol_datatype
   `Subject = Entity of missionStaffCA`;

val _ = Hol_datatype
   `SubPubKey = SPubKey of missionStaffCA pKey`;

(****************************************************)
(**** ADD YOUR DEFINITION OF KCertSignature HERE ****)
(****************************************************)


(****************************************************)
(**** ADD YOUR DEFINITION OF KeyCertificate HERE ****)
(****************************************************)


(************************************************)
(**** ADD YOUR DEFINITION OF checkKCert HERE ****)
(************************************************)


(******************************************************************)
(* Show that checkKCert works on certificates with the right form *)
(******************************************************************)

(*******************************************)
(**** ADD YOUR PROOF OF checkKCert HERE ****)
(*******************************************)


(* Sample digests *)
(*
``hash (plain (BFCA,KStaff Alice,pubK (KStaff Alice)))``
``hash (plain (JFCA,KCA BFCA,pubK (KCA BFCA)))``
*)

(* Sample signatures *)
(*
``Ea (privK (KCA BFCA))(plain(hash (plain (BFCA,KStaff Alice,pubK (KStaff Alice)))))``

``Ea (privK (KCA JFCA))(plain(hash (plain (JFCA,KCA BFCA,pubK (KCA BFCA)))))``

``sign (KCA JFCA) (hash (plain (JFCA,KCA BFCA,pubK (KCA BFCA))))``;
*)

(* Sample certificate for BFCA key *)
(*
``KCert (CA JFCA) (Entity (KCA BFCA)) (SPubKey (pubK (KCA BFCA))) (KCrtSig(sign (KCA JFCA) (hash (plain (JFCA,KCA BFCA,pubK (KCA BFCA))))))``
*)

(**** Semantics of Key Certificates ****)

(*******************************************)
(**** ADD YOUR DEFINITION OF Ekcrt HERE ****)
(*******************************************)

(******************************************)
(**** ADD YOUR DEFINITION OF ksat HERE ****)
(******************************************)
(* Don't forget to declare ksat as infix and set its precedence *)
(* See other definitions to see how to do this                  *)


(***********************************)
(* Theorems about key certificates *)
(***********************************)

(*************************************************)
(**** ADD YOUR PROOF OF kcrtStaffInterp_thm HERE *)
(*************************************************)


(**********************************************)
(**** ADD YOUR PROOF OF kcrtCAInterp_thm HERE *)
(**********************************************)


(**************************************************)
(* ROLE CERTIFICATE SYNTAX AND ACCESSOR FUNCTIONS *)
(* Certificates have the following components:    *)
(* 1. Authority: the person in charge             *)
(* 2. Role: the role of the person in commmand    *)
(* 3. Delegate: the person being authorized       *)
(* 4. Delegate Role: the role of the delegate     *)
(* 5. digital signature of the authorization      *)
(**************************************************)

val _ = Hol_datatype
    `Authority = Auth of missionStaff`;

val _ = Hol_datatype
    `Delegate = For of missionStaff`;

val _ = Hol_datatype
    `RCertSignature = 
      RCrtSig of ((missionStaff#missionRoles#missionStaff#missionRoles#commands) digest, missionStaffCA) asymMsg`;

val _ = Hol_datatype
    `RoleCertificate = RCert of Authority => Role => Delegate => Role => commands => RCertSignature`;

(* Sample Role Certificates *)
(*** Alice as BFC authorizing Carol as BFO

``RCert (Auth Alice) (As BFC) (For Carol) (As BFO) (MC go)(RCrtSig (sign (KStaff Alice) (hash (plain (Alice,BFC,Carol,BFO,(MC go))))))``
***)

(*** Bob as GFC authorizing Dan as GFO
``RCert (Auth Bob) (As GFC) (For Dan) (As GFO) (WC launch) (RCrtSig (sign (KStaff Bob) (hash (plain (Bob,GFC,Dan,GFO,(WC launch))))))``
***)

val checkRCert_def =
    Define
    `checkRCert
     (RCert 
      (Auth commander) (As cmdRole) (For delegate) 
      (As delegateRole) (order:commands) (RCrtSig rcertSig)) =
    signVerify (KStaff commander) rcertSig (plain(commander,cmdRole,delegate,delegateRole,order))`;

(******************************************************************)
(* Show that checkRCert works on certificates with the right form *)
(******************************************************************)
val checkRCertOK =
TAC_PROOF
(
 ([],
  ``checkRCert
    (RCert (Auth commander) (As cmdRole) (For delegate) (As delegateRole) order
    (RCrtSig
     (sign (KStaff commander) (hash (plain (commander,cmdRole,delegate,delegateRole,order))))))``),
 (REWRITE_TAC [checkRCert_def,signVerifyOK])
);

val _ = save_thm("checkRCertOK",checkRCertOK);

(**** Semantics of Role Certificates ****)

val Ercrt_def =
    Define
    `(Ercrt (Oi:'Int po) (Os:'Sec po) (M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke)
      (RCert (Auth commander) (As cmdRole) (For delegate) (As delegateRole) order (RCrtSig rcertSig)))
      =
     (if 
      (checkRCert
       (RCert (Auth commander) (As cmdRole) (For delegate) (As delegateRole) order (RCrtSig rcertSig)))
       then 
       (Efn Oi Os M 
            ((Name (MKey (pubK (KStaff commander)))) says 
	     (reps (Name (MStaff delegate))(Name (MRole delegateRole))(prop (order:commands)))))
       else {})`;

val _ = set_fixity "rsat" (Infixr 540);
val rsat_def =
    Define
    `((M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke), Oi, Os) 
      rsat (rcert:RoleCertificate) = 
     ((Ercrt Oi Os M rcert = UNIV:('world) set))`;

val Ercrt_th1 =
TAC_PROOF
(
([],
``(checkRCert
   (RCert (Auth commander) (As cmdRole) (For delegate) (As delegateRole) order (RCrtSig rcertSig))) ==>
  ((Ercrt (Oi:'Int po) (Os:'Sec po) (M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke)
    (RCert (Auth commander) (As cmdRole) (For delegate) (As delegateRole) order (RCrtSig rcertSig)))
      =
    (Efn Oi Os M 
     ((Name (MKey (pubK (KStaff commander)))) says 
     (reps (Name (MStaff delegate))(Name (MRole delegateRole))(prop (order:commands))))))``),
 (REWRITE_TAC [Ercrt_def] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [])
);

val Ercrt_th2 =
TAC_PROOF
(
([],
``((Ercrt (Oi:'Int po) (Os:'Sec po) (M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke)
    (RCert (Auth commander) (As cmdRole) (For delegate) (As delegateRole) order (RCrtSig rcertSig)))
      =
    (Efn Oi Os M 
     ((Name (MKey (pubK (KStaff commander)))) says 
     (reps (Name (MStaff delegate))(Name (MRole delegateRole))(prop (order:commands)))))) ==>
  (((M, Oi, Os) rsat (RCert (Auth commander) (As cmdRole) (For delegate) (As delegateRole) order (RCrtSig rcertSig))) =
   ((M, Oi, Os) sat ((Name (MKey (pubK (KStaff commander)))) says 
     (reps (Name (MStaff delegate))(Name (MRole delegateRole))(prop (order:commands))))))``),
 (REWRITE_TAC [rsat_def] THEN
  DISCH_THEN (fn th => REWRITE_TAC [th,aclrulesTheory.sat_def]))
);

val rcrtStaffInterp_thm =
save_thm
("rcrtStaffInterp_thm",GEN_ALL(IMP_TRANS Ercrt_th1 Ercrt_th2));

(***** Root Certificates ********)
(*********************************************************)
(* These are unsigned as they are the roots of trust and *)
(* there is no higher authority to vouch for them.       *)
(* The root certificates are for keys and authorizations *)
(* of command staff to roles. Their structure is a       *)
(* subset of the fields of their signed counterparts.    *)
(*********************************************************)

(* Root Key Certificates *)

(********************************************************)
(**** ADD YOUR DEFINITION OF RootKeyCertificate HERE ****)
(********************************************************)

(**** Semantics of Root Key Certificates ****)

(***********************************************)
(**** ADD YOUR DEFINITION OF Erootkcrt HERE ****)
(***********************************************)


(**********************************************)
(**** ADD YOUR DEFINITION OF rootksat HERE ****)
(**********************************************)
(* Don't forget to declare rootksat as an infix operator *)
(* and set its precedence. See other similar relations   *)
(* as examples                                           *)



(*********************************************************)
(**** ADD YOUR PROOF OF rootkcertStaffInterp_thm HERE ****)
(*********************************************************)


(******************************************************)
(**** ADD YOUR PROOF OF rootkcertCAInterp_thm HERE ****)
(******************************************************)



(* Root Role Certificates *)
val _ = Hol_datatype
    `RootRoleCertificate = 
     RootRCert of Delegate => Role => commands`;

(**** Semantics of RootRole Certificates ****)

val Erootrcrt_def =
    Define
    `(Erootrcrt (Oi:'Int po) (Os:'Sec po) (M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke)
      (RootRCert (For delegate) (As delegateRole) order))
      =
     (Efn Oi Os M 
      (reps (Name (MStaff delegate))(Name (MRole delegateRole))(prop (order:commands))))`;

val _ = set_fixity "rootrsat" (Infixr 540);
val rootrsat_def =
    Define
    `((M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke), Oi, Os) 
      rootrsat (rootrcert:RootRoleCertificate) = 
     ((Erootrcrt Oi Os M rootrcert = UNIV:('world) set))`;

val rootrcertStaffInterp_thm =
save_thm
("rootrcertStaffInterp_thm",
GEN_ALL
(TAC_PROOF
 (
  ([],
  ``(((M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke), Oi, Os) rootrsat 
     (RootRCert (For delegate) (As delegateRole) order)) =
     ((M, Oi, Os) sat 
      (reps (Name (MStaff delegate))(Name (MRole delegateRole))(prop (order:commands))))``),
  (REWRITE_TAC [rootrsat_def,Erootrcrt_def,aclrulesTheory.sat_def])
)));

(**************************************)
(* Theorems about signed certificates *)
(**************************************)

(***********************************************)
(**** ADD YOUR PROOF OF kcertCASat_thm HERE ****)
(***********************************************)


(**************************************************)
(**** ADD YOUR PROOF OF kcertStaffSat_thm HERE ****)
(**************************************************)

val rcertStaffSat_thm =
save_thm("rcertStaffSat_thm",
GEN_ALL
(TAC_PROOF
(
([],
``((M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke),Oi:'Int po,Os:'Sec po) sat
  Name (MKey (pubK (KStaff commander))) says
  reps (Name (MStaff delegate)) (Name (MRole delegateRole))
       (prop order :(commands, missionPrincipals, 'Int, 'Sec) Form) =
  ((M,Oi,Os) rsat
  RCert (Auth commander) (As cmdRole) (For delegate)
        (As delegateRole) order 
	(RCrtSig
         (sign (KStaff commander)
               (hash
                (plain
                 (commander,cmdRole,delegate,delegateRole,order))))))``),
 (REWRITE_TAC [rsat_def,Ercrt_def,checkRCertOK,aclrulesTheory.sat_def]))));

(*************************************)
(* print and export theory           *)
(*************************************)
val _ = print_theory "-";
    
val _ = export_theory();

end;