(************************************************************)
(* Cipher operations                                        *)
(* Created 17 June 2011: Shiu-Kai Chin                      *)
(* Preliminary version created for AFRL IA Internship       *)
(* Summer 2011                                              *)
(************************************************************)

(* Interactive mode


(* Disable Pretty-Printing *)
set_trace "Unicode" 0;
*)

structure cipherScript = struct

open HolKernel boolLib Parse bossLib

(***********
* create a new theory
***********)
val _ = new_theory "cipher";

(************************
* THE DEFINITIONS START HERE
************************)

(************************************************)
(* Contents to be encrypted                     *)
(* Sometimes we want to return unknown if keys  *)
(* don't match in the case of public key crypto.*)
(************************************************)
val _ = Hol_datatype `contents = plain of 'message | unknown`;

val getMessage_def = Define `getMessage (plain (msg:'message)) = msg`;
val contents_11 = save_thm("contents_11", (TypeBase.one_one_of ``:'message contents``)); 
(************************************************)
(* Symmetric Encryption/Decryption              *)
(************************************************)

(************************************************)
(* Creating symmetric (secret) keys and         *)
(* encrypted messages with symmetric keys.      *)
(************************************************)

val _ = Hol_datatype `SymKey = sym of num`;
val _ = Hol_datatype `symMsg = Es of SymKey => 'message contents`;

(************************************************)
(* Deciphering with symmetric keys              *)
(* Define with pattern matching. If the key     *)
(* matches then we can retrieve the plain text. *)
(* No definition is offered for the result if   *)
(* the key in the message doesn't match the key *)
(* that is supplied.                            *)
(************************************************)

val deciphS_def =
    Define 
    `deciphS (k1:SymKey) (Es k2 (plain (text:'message))) = 
     if (k1 = k2) then (plain text) else unknown`;

(************************************************)
(* Creating asymmetric public and private keys. *)
(* As these keys are created using a common     *)
(* parameter, we will model this parameter with *)
(* the principal with whom the keys are         *)
(* associated.                                  *)
(************************************************)
val _ = Hol_datatype `pKey = pubK of 'princ | privK of 'princ`;
val _ = Hol_datatype `asymMsg = Ea of 'princ pKey => ('message)contents`;

(************************************************)
(* Deciphering with asymmetric keys             *)
(* Define with pattern matching. If the         *)
(* corresponding keys match then the text is    *)
(* recovered. No definition is offered for the  *)
(* result if the keys do not correspond to a    *)
(* public/private key pair.                     *)
(************************************************)
val deciphP_def =
    Define
    `(deciphP (key:'princ pKey) (Ea (privK (P:'princ)) (plain (text:'message))) = 
      if ((key:'princ pKey) = (pubK (P:'princ))) then (plain text) else unknown)
     /\
     (deciphP (key:'princ pKey) (Ea (pubK (P:'princ)) (plain (text:'message))) = 
      if ((key:'princ pKey) = (privK (P:'princ))) then (plain text) else unknown)`;

(************************************************)
(* Message digests are cryptographic hashes of  *)
(* messages.                                    *)
(************************************************)
val _ = Hol_datatype `digest = hash of 'message contents`;
val digest_11 = save_thm("digest_11",(TypeBase.one_one_of ``:'message digest``));

(************************************************)
(* Signatures are digests encrypted by the      *)
(* private key of the sender.                   *)
(************************************************)
val sign_def =
    Define
    `sign (P:'princ) (dgst:'message digest) = Ea (privK P) (plain dgst)`;

(************************************************)
(* Integrity checking of messages is checking   *)
(* the hash of the received message equals the  *)
(* signature decrypted with the sender's public *)
(* key.                                         *)
(************************************************)
val signVerify_def =
    Define
    `signVerify (P:'princ)(signature:('message digest,'princ)asymMsg)(msgContents:'message contents) =
    ((plain(hash msgContents)) = (deciphP (pubK P) signature))`;

(************************************************)
(* A theorem to make sure that our integrity    *)
(* checking function works with the way we      *)
(* create digital signatures.                   *)
(************************************************)

val signVerifyOK =
    save_thm
    ("signVerifyOK",
    TAC_PROOF(
    ([],``!(P:'princ)(msg:'message).signVerify P (sign P (hash (plain msg)))(plain msg)``),
    (REPEAT STRIP_TAC THEN
    REWRITE_TAC [signVerify_def, sign_def, deciphP_def])));

val signVerify_11 =
TAC_PROOF
(
 ([],``!P m1 m2.signVerify (P:'a) (Ea (privK P) (plain (hash (plain (m1 :'b)))))
      (plain (m2:'b)) = (m1 = m2)`` ),
 (REWRITE_TAC [signVerify_def,deciphP_def,contents_11,digest_11] THEN
  REPEAT STRIP_TAC THEN
  EQ_TAC THEN 
  DISCH_THEN (fn th => REWRITE_TAC[th]))
);

val signVerify_11 = save_thm("signVerify_11",signVerify_11);


val th1 =
    TAC_PROOF(
    ([], ``!P text.((deciphP (pubK P)(Ea (privK P) (plain text)) = (plain text)) /\
    (deciphP (privK P)(Ea (pubK P) (plain text)) = (plain text)))``),
    (REPEAT STRIP_TAC THEN
     REWRITE_TAC [deciphP_def]));

val contents_distinct = 
    save_thm("contents_distinct",TypeBase.distinct_of (Type `:'a contents`));

val th2 = TAC_PROOF(
 ([], ``!k P text. 
         (deciphP k (Ea (privK P) (plain text)) = (plain text)) ==> (k = pubK P)``),
  (REPEAT GEN_TAC THEN
   REWRITE_TAC [deciphP_def] THEN
   BOOL_CASES_TAC ``k = (pubK P)`` THEN
   REWRITE_TAC [GSYM contents_distinct]));

val th3 = TAC_PROOF(
 ([], ``!k P text. 
         (deciphP k (Ea (pubK P) (plain text)) = (plain text)) ==> (k = privK P)``),
  (REPEAT GEN_TAC THEN
   REWRITE_TAC [deciphP_def] THEN
   BOOL_CASES_TAC ``k = (privK P)`` THEN
   REWRITE_TAC [GSYM contents_distinct]));

val deciphP_clauses =
    save_thm("deciphP_clauses",LIST_CONJ [th1,th2,th3]);

val th1 =
    TAC_PROOF(
    ([], ``!k text.(deciphS k (Es k (plain text)) = (plain text))``),
    (REPEAT STRIP_TAC THEN
     REWRITE_TAC [deciphS_def]));

val th2 =
TAC_PROOF(
 ([], ``!(k1:SymKey) (k2:SymKey) text. 
         (deciphS k1 (Es k2 (plain text)) = (plain text)) ==> (k1 = k2)``),
  (REPEAT GEN_TAC THEN
   REWRITE_TAC [deciphS_def] THEN
   BOOL_CASES_TAC ``k1:SymKey = k2:SymKey`` THEN
   REWRITE_TAC [GSYM contents_distinct]));

val deciphS_clauses =
    save_thm("deciphS_clauses",CONJ th1 th2);


(*******************************)
(* Print and export the theory *)
(*******************************)
val _ = print_theory "-";

val _ = export_theory();

end;