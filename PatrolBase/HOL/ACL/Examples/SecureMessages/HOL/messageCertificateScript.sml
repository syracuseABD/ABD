(****************************************)
(* Message and Certificate Structures:  *)
(* Created by S-K Chin 17 November 2011 *)
(****************************************)

(***********
* Add the path to where aclfoundationTheory resides.
* Then, add the path to HOL's search path.
***********)
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

(* Orders issued *)
val _ = Hol_datatype
    `Orders = CMD of Origin => Role => Destination => commands`;

val ordersParameters_def =
    Define 
    `ordersParameters
     (CMD 
      (From (sender:missionStaff)) 
      (As (role:missionRoles))
      (To (recipient:missionStaff))
      (orders:commands)) = (sender,role,recipient)`;

val ordersCommand_def =
    Define 
    `ordersCommand
     (CMD 
      (From (sender:missionStaff)) 
      (As (role:missionRoles))
      (To (recipient:missionStaff))
      (orders:commands)) = orders`;

(************************************************)
(* MESSAGE SYNTAX AND ACCESSOR FUNCTIONS        *)
(* Messages have the following components:      *)
(* 1. origin (the sender)                       *)
(* 2. role of the sender                        *)
(* 3. destination (the recipient)               *)
(* 4. symmetric data encryption key encrypted   *)
(*    by the recipient's public key             *)
(* 5. orders ordered by the sender              *)
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
     Orders symMsg =>
     (Orders digest, missionStaff) asymMsg`;

val msgParameters_def =
   Define
   `msgParameters
    (MSG 
     (From (sender:missionStaff))
     (As (role:missionRoles))
     (To (recipient:missionStaff))
     (enDEK:(SymKey,missionStaff)asymMsg)
     (enCMDMsg:(Orders symMsg))
     (CMDMsgSig:(Orders digest,missionStaff)asymMsg)) = 
    (sender,role,recipient,enDEK,enCMDMsg,CMDMsgSig)`;

val checkMSG_def =
    Define
    `checkMSG 
     (MSG 
      (From (sender:missionStaff))
      (As (role:missionRoles))
      (To (recipient:missionStaff))
      (enDEK:(SymKey,missionStaff)asymMsg)
      (enCMDMsg:(Orders symMsg))
      (CMDMsgSig:(Orders digest,missionStaff)asymMsg)) = 
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
      (enCMDMsg:(Orders symMsg))
      (CMDMsgSig:(Orders digest,missionStaff)asymMsg)) =
     (let dek = 
        getMessage 
        (deciphP 
         (privK recipient)
         (enDEK:(SymKey,missionStaff)asymMsg))
      in
        getMessage(deciphS dek (enCMDMsg:(Orders symMsg))))`;

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
      (Es (sym dek)(plain (order:Orders)))
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
   (Es (sym dek)(plain (order:Orders)))
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
   (Es (sym dek)(plain (order:Orders)))
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
      (From sender) (As role) (To recipient) enDEK enCMD CMDsig)) 
     = 
     (if
       checkMSG (MSG (From sender) (As role) (To recipient) enDEK enCMD CMDsig)
      then
      (let order = 
        getCommand(MSG (From sender) (As role) (To recipient) enDEK enCMD CMDsig)
       in
        (let 
          x = (ordersParameters order)
         in
	  (if x = (sender,role,recipient) then
	  (Efn Oi Os M 
       	   (((Name (MKey (pubK (KStaff sender)))) quoting (Name (MRole role))) 
             says (prop (ordersCommand order)))) else
	   {})))
      else
       {})`;

val _ = set_fixity "msat" (Infixr 540);
val msat_def =
    Define
    `(M, Oi, Os) msat (msg:Message) = ((Emsg Oi Os M msg) = UNIV:('world) set)`;

(* Prove properties about Emsg *)

val msgSat_thm =
GENL [``recipient:missionStaff``,``dek:num``,``sender:missionStaff``,
       ``role :missionRoles``,``order :commands``,
       ``(M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke)``,
       ``Oi:'Int po``,``Os:'Sec po``]
 (TAC_PROOF(([],
``((M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke),Oi:'Int po,Os:'Sec po) sat
  (((Name (MKey (pubK (KStaff sender)))) quoting (Name (MRole role))) 
       says (prop action)) =
  ((M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke),Oi:'Int po,Os:'Sec po) msat
  (MSG 
   (From (sender:missionStaff)) 
   (As (role:missionRoles)) 
   (To (recipient:missionStaff))
   (Ea (pubK recipient)(plain (sym dek))) 
   (Es 
    (sym dek)
    (plain 
     (CMD 
      (From (sender:missionStaff)) 
      (As (role:missionRoles))
      (To (recipient:missionStaff))
      (action:commands))))
   (sign
     sender
     (hash
      (plain 
       (CMD 
        (From (sender:missionStaff)) 
   	(As (role:missionRoles))
    	(To (recipient:missionStaff))
    	(action:commands))))))``),
 (REWRITE_TAC [msat_def,Emsg_def,getCommand_thm,checkMSGOK,LET_DEF,ordersCommand_def] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[ordersParameters_def] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[GSYM aclrulesTheory.sat_def,ordersCommand_def])));

val _ = save_thm("msgSat_thm",msgSat_thm);

val msgInterp_thm = 
save_thm
("msgInterp_thm",
 (GEN_ALL
(TAC_PROOF(([],
``(checkMSG 
(MSG 
   (From (sender:missionStaff)) 
   (As (role:missionRoles)) 
   (To (recipient:missionStaff))
   (Ea (pubK recipient)(plain (sym dek))) 
   (Es 
    (sym dek)
    (plain 
     (CMD 
      (From (sender:missionStaff)) 
      (As (role:missionRoles))
      (To (recipient:missionStaff))
      (action:commands))))
   (sign
     sender
     (hash
      (plain 
       (CMD 
        (From (sender:missionStaff)) 
   	(As (role:missionRoles))
    	(To (recipient:missionStaff))
    	(action:commands))))))) ==> 
    ((M,Oi,Os) msat
         MSG (From sender) (As role) (To recipient)
           (Ea (pubK recipient) (plain (sym dek)))
           (Es (sym dek)
              (plain (CMD (From sender) (As role) (To recipient) action)))
           (sign sender
              (hash
                 (plain
                    (CMD (From sender) (As role) (To recipient) action))))) =
    ((M,Oi,Os) sat Name (MKey (pubK (KStaff sender))) quoting Name (MRole role) says
         prop action)``),
 (REWRITE_TAC[msat_def,Emsg_def] THEN
  REWRITE_TAC[LET_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[getCommand_def,LET_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC
  [cipherTheory.deciphP_clauses,cipherTheory.deciphS_clauses,cipherTheory.getMessage_def,
   ordersParameters_def,ordersCommand_def,checkMSGOK,aclrulesTheory.sat_def])))));

(* Syntax of Certificates *)
(************************************************)
(* KEY CERTIFICATE SYNTAX AND ACCESSOR FUNCTIONS*)
(* Certificates have the following components:  *)
(* 1. Issuer: the certificate authority         *)
(* 2. Subject: the to whom key is assigned      *)
(* 3. PubKey: the public key for Entity         *)
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

val _ = Hol_datatype
   `KCertSignature =
      KCrtSig of 
      ((missionCA#missionStaffCA#missionStaffCA pKey) digest, 
        missionStaffCA) asymMsg`;

val _ = Hol_datatype 
    `KeyCertificate = 
     KCert of 
     Issuer => 
     Subject =>
     SubPubKey =>
     KCertSignature`;

(****not needed
val getKCertParameters_def =
    Define
    `getKCertParameters
     (KCert (CA mca) (Entity mStaffCA) (SPubKey pubKey) (KCrtSig kcertSig)) =
     ((mca,mStaffCA,pubKey),kcertSig)`;
****)

val checkKCert_def =
    Define
    `checkKCert
     (KCert (CA mca) (Entity mStaffCA) (SPubKey pubKey)(KCrtSig kcertSig)) =
     signVerify (KCA mca) kcertSig (plain(mca,mStaffCA,pubKey))`;

(******************************************************************)
(* Show that checkKCert works on certificates with the right form *)
(******************************************************************)
val checkKCertOK =
TAC_PROOF
(
 ([],
  ``checkKCert
    (KCert (CA mca) (Entity mStaffCA) (SPubKey pubKey)
    (KCrtSig
     (sign (KCA mca) (hash (plain (mca,mStaffCA,pubKey))))))``),
 (REWRITE_TAC [checkKCert_def,signVerifyOK])
);

val _ = save_thm("checkKCertOK",checkKCertOK);

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

val Ekcrt_def =
    Define
    `((Ekcrt (Oi:'Int po) (Os:'Sec po) (M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke)
     (KCert (CA mca) (Entity (KStaff staff)) (SPubKey pubKey)(KCrtSig kcertSig))) =
     (if 
      (checkKCert
       (KCert (CA mca) (Entity (KStaff staff)) (SPubKey pubKey)(KCrtSig kcertSig)))
       then 
       (Efn Oi Os M 
            ((Name (MKey (pubK (KCA mca)))) says 
	     ((Name (MKey pubKey)) speaks_for (Name (MStaff staff)))))
       else {})) /\
     ((Ekcrt (Oi:'Int po) (Os:'Sec po) (M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke)
     (KCert (CA mca) (Entity (KCA ca2)) (SPubKey pubKey)(KCrtSig kcertSig))) =
     (if 
      (checkKCert
       (KCert (CA mca) (Entity (KCA ca2)) (SPubKey pubKey)(KCrtSig kcertSig)))
       then 
       (Efn Oi Os M 
            ((Name (MKey (pubK (KCA mca)))) says 
	     ((Name (MKey pubKey)) speaks_for (Name (MCA ca2)))))
       else {}))`;

val _ = set_fixity "ksat" (Infixr 540);
val ksat_def =
    Define
    `((M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke), Oi, Os) 
      ksat (kcert:KeyCertificate) = 
     ((Ekcrt Oi Os M kcert) = UNIV:('world) set)`;

(***********************************)
(* Theorems about key certificates *)
(***********************************)
val Ekcrt_th1 =
TAC_PROOF
(
([],
 ``(checkKCert
    (KCert (CA (mca:missionCA)) (Entity (KStaff (staff:missionStaff))) (SPubKey pubKey)(KCrtSig kcertSig))) ==>
   ((Ekcrt (Oi:'Int po) (Os:'Sec po) (M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke)
     (KCert (CA mca) (Entity (KStaff staff)) (SPubKey pubKey)(KCrtSig kcertSig))) =
    (Efn Oi Os M 
     ((Name (MKey (pubK (KCA mca)))) says 
     ((Name (MKey pubKey)) speaks_for (Name (MStaff staff))))))``),
(REWRITE_TAC [Ekcrt_def] THEN
 DISCH_TAC THEN
 ASM_REWRITE_TAC [])
);

val Ekcrt_th2 =
TAC_PROOF
(
([],
``((Ekcrt (Oi:'Int po) (Os:'Sec po) (M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke)
     (KCert (CA mca) (Entity (KStaff staff)) (SPubKey pubKey)(KCrtSig kcertSig))) =
    (Efn Oi Os M 
     ((Name (MKey (pubK (KCA mca)))) says 
     ((Name (MKey pubKey)) speaks_for (Name (MStaff staff)))))) ==>
  (((M, Oi, Os) ksat (KCert (CA mca) (Entity (KStaff staff)) (SPubKey pubKey)(KCrtSig kcertSig))) =
   ((M, Oi, Os) sat ((Name (MKey (pubK (KCA mca)))) says 
     ((Name (MKey pubKey)) speaks_for (Name (MStaff staff))))))``),
 (REWRITE_TAC [ksat_def] THEN
  DISCH_THEN (fn th => REWRITE_TAC [th,aclrulesTheory.sat_def]))
);

val kcrtStaffInterp_thm =
save_thm
("kcrtStaffInterp_thm",GEN_ALL(IMP_TRANS Ekcrt_th1 Ekcrt_th2));

val Ekcrt_th3 =
TAC_PROOF
(
([],
 ``(checkKCert
    (KCert (CA (mca:missionCA)) (Entity (KCA (ca2:missionCA))) (SPubKey pubKey)(KCrtSig kcertSig))) ==>
   ((Ekcrt (Oi:'Int po) (Os:'Sec po) (M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke)
     (KCert (CA mca) (Entity (KCA ca2)) (SPubKey pubKey)(KCrtSig kcertSig))) =
    (Efn Oi Os M 
     ((Name (MKey (pubK (KCA mca)))) says 
     ((Name (MKey pubKey)) speaks_for (Name (MCA ca2))))))``),
(REWRITE_TAC [Ekcrt_def] THEN
 DISCH_TAC THEN
 ASM_REWRITE_TAC [])
);

val Ekcrt_th4 =
TAC_PROOF
(
([],
``((Ekcrt (Oi:'Int po) (Os:'Sec po) (M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke)
     (KCert (CA mca) (Entity (KCA ca2)) (SPubKey pubKey)(KCrtSig kcertSig))) =
    (Efn Oi Os M 
     ((Name (MKey (pubK (KCA mca)))) says 
     ((Name (MKey pubKey)) speaks_for (Name (MCA ca2)))))) ==>
  (((M, Oi, Os) ksat (KCert (CA mca) (Entity (KCA ca2)) (SPubKey pubKey)(KCrtSig kcertSig))) =
   ((M, Oi, Os) sat ((Name (MKey (pubK (KCA mca)))) says 
     ((Name (MKey pubKey)) speaks_for (Name (MCA ca2))))))``),
 (REWRITE_TAC [ksat_def] THEN
  DISCH_THEN (fn th => REWRITE_TAC [th,aclrulesTheory.sat_def]))
);

val kcrtCAInterp_thm =
save_thm
("kcrtCAInterp_thm",GEN_ALL(IMP_TRANS Ekcrt_th3 Ekcrt_th4));

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
val _ = Hol_datatype 
    `RootKeyCertificate = 
     RootKCert of 
     Subject =>
     SubPubKey`;

(**** Semantics of Root Key Certificates ****)

val Erootkcrt_def =
    Define
    `((Erootkcrt (Oi:'Int po) (Os:'Sec po) (M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke)
     (RootKCert (Entity (KStaff staff)) (SPubKey pubKey))) =
     (Efn Oi Os M ((Name (MKey pubKey)) speaks_for (Name (MStaff staff)))))
      /\
     ((Erootkcrt (Oi:'Int po) (Os:'Sec po) (M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke)
     (RootKCert (Entity (KCA ca2)) (SPubKey pubKey))) =
     (Efn Oi Os M ((Name (MKey pubKey)) speaks_for (Name (MCA ca2)))))`;

val _ = set_fixity "rootksat" (Infixr 540);
val rootksat_def =
    Define
    `((M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke), Oi:'Int po, Os:'Sec po) 
      rootksat (rootkcert:RootKeyCertificate) = 
     ((Erootkcrt Oi Os M rootkcert) = UNIV:('world) set)`;

val rootkcertStaffInterp_thm =
save_thm
("rootkcertStaffInterp_thm",
GEN_ALL(
(TAC_PROOF
(
 ([],
  ``(((M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke), Oi, Os) rootksat (RootKCert (Entity (KStaff staff)) (SPubKey pubKey))) =
    ((M, Oi, Os) sat ((Name (MKey pubKey)) speaks_for (Name (MStaff staff))))``),
 (REWRITE_TAC [rootksat_def,Erootkcrt_def,aclrulesTheory.sat_def])))
));

val rootkcertCAInterp_thm =
save_thm
("rootkcertCAInterp_thm",
GEN_ALL(
TAC_PROOF
(
 ([],
  ``(((M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke), Oi:'Int po, Os:'Sec po) 
    rootksat (RootKCert (Entity (KCA ca)) (SPubKey pubKey))) =
   ((M, Oi, Os) sat ((Name (MKey pubKey)) speaks_for (Name (MCA ca))))``),
 (REWRITE_TAC [rootksat_def,Erootkcrt_def,aclrulesTheory.sat_def])
)
));

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
val kcertCASat_thm =
save_thm("kcertCASat_thm",
GEN_ALL
(TAC_PROOF
(
([],
``((M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke),Oi:'Int po,Os:'Sec po) sat
  (Name (MKey (pubK (KCA mca)))) says
  ((Name (MKey (pubK (KCA ca2))) speaks_for Name (MCA ca2)):(commands, missionPrincipals, 'Int, 'Sec) Form) =
  ((M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke),Oi:'Int po,Os:'Sec po) ksat
  KCert (CA mca) (Entity (KCA ca2)) (SPubKey (pubK (KCA ca2)))
        (KCrtSig (sign (KCA mca) (hash (plain (mca,KCA ca2,(pubK (KCA ca2)))))))``),
 (REWRITE_TAC [ksat_def,Ekcrt_def,checkKCertOK,aclrulesTheory.sat_def]))));

val kcertStaffSat_thm =
save_thm("kcertStaffSat_thm",
GEN_ALL
(TAC_PROOF
(
([],
``((M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke),Oi:'Int po,Os:'Sec po) sat
  (Name (MKey (pubK (KCA mca)))) says
  ((Name (MKey (pubK (KStaff staff))) speaks_for Name (MStaff staff)):(commands, missionPrincipals, 'Int, 'Sec) Form) =
  ((M:(commands,'world,missionPrincipals,'Int,'Sec) Kripke),Oi:'Int po,Os:'Sec po) ksat
  KCert (CA mca) (Entity (KStaff staff)) (SPubKey (pubK (KStaff staff)))
        (KCrtSig (sign (KCA mca) (hash (plain (mca,KStaff staff,(pubK (KStaff staff)))))))``),
 (REWRITE_TAC [ksat_def,Ekcrt_def,checkKCertOK,aclrulesTheory.sat_def]))));

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