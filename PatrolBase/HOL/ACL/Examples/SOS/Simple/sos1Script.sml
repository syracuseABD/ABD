(************************************************************)
(* High-Level Structural Operational Semantics: version 2   *)
(* Created by S-K Chin, 26 February 2012                    *)
(************************************************************)

(***********
* Load necessary theories
***********)
(* Interactive mode
app load ["acl_infRules","listTheory","listLib","foundationTheory","sos0Theory"];
*)

structure sos1Script = struct

(* Note: in interactive mode no need to open HolKernel boolLib Parse bossLib *)
open HolKernel boolLib Parse bossLib
open listTheory listLib acl_infRules foundationTheory sos0Theory;

(***********
* create a new theory
***********)
val _ = new_theory "sos1";

(*********************************************************************************************)
(* We justify the transition from STBY to RDY in terms of policies, messages, and conditions *)
(*********************************************************************************************)
(***********************************************************************************)
(* This theorem justifies concluding (prop (MODE RDY)) from operating policies and *)
(* statements in the access-control logic                                          *)
(***********************************************************************************)
val STBY_RDY_rule =
let
(* Policy Statements for STBY *)
val p1 = ACL_ASSUM ``(Name Owner) controls (prop (CMD enable)):(Statements,Roles,'Int,'Sec)Form``
val p2 = ACL_ASSUM ``(prop (CMD enable)) impf (prop (MODE RDY)):(Statements,Roles,'Int,'Sec)Form``
(* Messages in STBY *)
val m1 = ACL_ASSUM ``(Name Owner) says (prop (CMD enable)):(Statements,Roles,'Int,'Sec)Form``
(* Proof *)
val th1 = CONTROLS p1 m1
val th2 = ACL_MP th1 p2
val th3 = 
DISCH 
``((M :(Statements, 'b, Roles, 'Int, 'Sec) Kripke),(Oi :'Int po),
   (Os :'Sec po)) sat(prop (CMD enable)) impf (prop (MODE RDY)):(Statements,Roles,'Int,'Sec)Form``
th2
val th4 =
DISCH
``((M :(Statements, 'b, Roles, 'Int, 'Sec) Kripke),(Oi :'Int po),
   (Os :'Sec po)) sat (Name Owner) controls (prop (CMD enable)):(Statements,Roles,'Int,'Sec)Form``
th3
in
DISCH
``((M :(Statements, 'b, Roles, 'Int, 'Sec) Kripke),(Oi :'Int po),
   (Os :'Sec po)) sat (Name Owner) says (prop (CMD enable)):(Statements,Roles,'Int,'Sec)Form``
th4
end;

val _ = save_thm("STBY_RDY_rule",STBY_RDY_rule);

(*********************************************************************************************)
(* We justify the transition from RDY to STBY in terms of policies, messages, and conditions *)
(*********************************************************************************************)
(************************************************************************************)
(* This theorem justifies concluding (prop (MODE STBY)) from operating policies and *)
(* statements in the access-control logic                                           *)
(************************************************************************************)
val RDY_STBY_rule =
let
(* Policy Statements for RDY *)
val p1 = ACL_ASSUM ``(Name Owner) controls (prop (CMD disable)):(Statements,Roles,'Int,'Sec)Form``
val p2 = ACL_ASSUM ``(prop (CMD disable)) impf (prop (MODE STBY)):(Statements,Roles,'Int,'Sec)Form``
(* Messages in STBY *)
val m1 = ACL_ASSUM ``(Name Owner) says (prop (CMD disable)):(Statements,Roles,'Int,'Sec)Form``
(* Proof *)
val th1 = CONTROLS p1 m1
val th2 = ACL_MP th1 p2
val th3 = 
DISCH 
``((M :(Statements, 'b, Roles, 'Int, 'Sec) Kripke),(Oi :'Int po),
   (Os :'Sec po)) sat(prop (CMD disable)) impf (prop (MODE STBY)):(Statements,Roles,'Int,'Sec)Form``
th2
val th4 =
DISCH
``((M :(Statements, 'b, Roles, 'Int, 'Sec) Kripke),(Oi :'Int po),
   (Os :'Sec po)) sat (Name Owner) controls (prop (CMD disable)):(Statements,Roles,'Int,'Sec)Form``
th3
in
DISCH
``((M :(Statements, 'b, Roles, 'Int, 'Sec) Kripke),(Oi :'Int po),
   (Os :'Sec po)) sat (Name Owner) says (prop (CMD disable)):(Statements,Roles,'Int,'Sec)Form``
th4
end;

val _ = save_thm("RDY_STBY_rule",RDY_STBY_rule);

(**********************************************************)
(* An inference rule that takes theorems of the form      *)
(* h0 ==> ... ==> hn ==> c and  rewrites them to the form *)
(* h0 /\ ... /\ hn ==> c                                  *)
(**********************************************************)

fun Imp2ConjThm_CONV thm = 
let val term = concl thm
    fun gatherHyps (hlist,term) =
     if is_imp term then 
     (let val (h,c) = dest_imp term
      in
      gatherHyps ((h::hlist),c)
      end)
     else (hlist,term)
    fun conjList a [] = a
      | conjList a (h::hs) = conjList (mk_conj(h,a)) hs
    fun imp2conj impTerm =
     let val ((h::hs),c) = gatherHyps([],impTerm)
     in
     mk_imp ((conjList h hs),c)
     end
    fun convImp2Conj term =
     if (is_imp term) then (imp2conj term) else term
in
TAC_PROOF
(([],(mk_eq(term,(convImp2Conj term)))),
 PROVE_TAC [])
end;

(* Imp2ConjThm_CONV STBY_RDY_rule; *)
(********************)
(* TRANSITION RULES *)
(********************)
val (TR1_rules,TR1_ind,TR1_cases) =
Hol_reln
`((((M,Oi,Os) blocksat 
   BLK
    (Messages (STBYmlist:(Statements,Roles,'Int,'Sec)Form list))
    (CFG STBY 
     (Certs (STBYclist:(Statements,Roles,'Int,'Sec)Form list))
     (Policies (STBYplist:(Statements,Roles,'Int,'Sec)Form list)))) /\
  (((M:(Statements,'worlds,Roles,'Int,'Sec)Kripke),Oi:'Int po,Os:'Sec po) sat (prop (MODE RDY)))) ==>
  TR1 ((M:(Statements,'worlds,Roles,'Int,'Sec)Kripke),Oi:'Int po,Os:'Sec po)
      (Messages (STBYmlist:(Statements,Roles,'Int,'Sec)Form list))
      (CFG STBY (Certs (STBYclist:(Statements,Roles,'Int,'Sec)Form list))(Policies (STBYplist:(Statements,Roles,'Int,'Sec)Form list)))
      (CFG RDY (Certs (RDYclist:(Statements,Roles,'Int,'Sec)Form list))(Policies RDYplist))) /\
 ((((M,Oi,Os) blocksat 
   BLK
    (Messages (RDYmlist:(Statements,Roles,'Int,'Sec)Form list))
    (CFG RDY 
     (Certs (RDYclist:(Statements,Roles,'Int,'Sec)Form list))
     (Policies (RDYplist:(Statements,Roles,'Int,'Sec)Form list)))) /\
  (((M:(Statements,'worlds,Roles,'Int,'Sec)Kripke),Oi:'Int po,Os:'Sec po) sat (prop (MODE STBY)))) ==>
  TR1 ((M:(Statements,'worlds,Roles,'Int,'Sec)Kripke),Oi:'Int po,Os:'Sec po)
      (Messages (RDYmlist:(Statements,Roles,'Int,'Sec)Form list))
      (CFG RDY (Certs (RDYclist:(Statements,Roles,'Int,'Sec)Form list))(Policies RDYplist))
      (CFG STBY (Certs (STBYclist:(Statements,Roles,'Int,'Sec)Form list))(Policies (STBYplist:(Statements,Roles,'Int,'Sec)Form list))))`;

(***************************)
(* Conversion for blocksat *)
(***************************)

fun blocksat_CONV mode mlist clist plist =
let 
val th1 = 
ISPECL 
[mode,mlist,clist,plist]
(GENL 
 [``mode :modes``,``(mlist :(Statements, Roles, 'Int, 'Sec) Form list)``,
  ``(clist:(Statements, Roles, 'Int, 'Sec) Form list)``,
  ``(plist :(Statements, Roles, 'Int, 'Sec) Form list)``] blocksat_def)
val th2 = (DEPTH_CONV APPEND_CONV) ``^mlist ++ ^clist ++ ^plist``
val th3 = REWRITE_RULE [th2] th1
val th4 = REWRITE_RULE [satList_def,MAP,FOLDR] th3
val th5 = CONV_RULE(DEPTH_CONV(BETA_CONV)) th4
in
REWRITE_RULE [] th5
end;

fun blocksatTransRule mode mlist clist plist aclTransRule TransRule =
let
val th1 = TAC_PROOF(([],``(a ==> b) = (a ==> a /\ b)``),(PROVE_TAC []))
val th2 =
REWRITE_RULE
[SYM(blocksat_CONV mode mlist clist plist)]
(REWRITE_RULE [Imp2ConjThm_CONV aclTransRule] aclTransRule)
val th3 = UNDISCH(ONCE_REWRITE_RULE [th1] th2)
in
DISCH_ALL(MATCH_MP (SPEC_ALL TransRule) th3)
end;

val STBY_RDY_TRANS_rule = 
blocksatTransRule 
``STBY:modes``
``[Name Owner says (prop (CMD enable))] :(Statements, Roles, 'Int, 'Sec) Form list``
``[] :(Statements, Roles, 'Int, 'Sec) Form list``
``[Name Owner controls (prop (CMD enable));
   prop (CMD enable) impf (prop (MODE RDY))]:(Statements, Roles, 'Int, 'Sec) Form list``
STBY_RDY_rule
(CONJUNCT1 TR1_rules);

val _ = save_thm("STBY_RDY_TRANS_rule", STBY_RDY_TRANS_rule);

val RDY_STBY_TRANS_rule = 
blocksatTransRule 
``RDY:modes``
``[Name Owner says (prop (CMD disable))] :(Statements, Roles, 'Int, 'Sec) Form list``
``[] :(Statements, Roles, 'Int, 'Sec) Form list``
``[Name Owner controls (prop (CMD disable));
   prop (CMD disable) impf (prop (MODE STBY))]:(Statements, Roles, 'Int, 'Sec) Form list``
RDY_STBY_rule
(CONJUNCT2 TR1_rules);

val _ = save_thm("RDY_STBY_TRANS_rule",RDY_STBY_TRANS_rule);

(*************************)
(* SOS1 Security Theorem *)
(*************************)
val SOS1_Security_thm =
TAC_PROOF(
([],
 ``!(M:(Statements,'worlds,Roles,'Int,'Sec)Kripke)(Oi:'Int po)(Os:'Sec po)(M1:modes)(M2:modes) mlist clist1 clist2 plist1 plist2.
   (TR1 (M,Oi,Os)(Messages (mlist:(Statements,Roles,'Int,'Sec)Form list))
    (CFG M1 (Certs (clist1:(Statements,Roles,'Int,'Sec)Form list))(Policies (plist1:(Statements,Roles,'Int,'Sec)Form list)))
    (CFG M2 (Certs (clist2:(Statements,Roles,'Int,'Sec)Form list))(Policies (plist2:(Statements,Roles,'Int,'Sec)Form list)))) ==> ((M,Oi,Os) sat (prop (MODE M2)))``),
(REWRITE_TAC [TR1_cases] THEN
 REPEAT STRIP_TAC THEN
 IMP_RES_TAC (TypeBase.one_one_of ``:('Int,'Sec)configuration``) THEN
 ASM_REWRITE_TAC [])
);

val _ = save_thm("SOS1_Security_thm",SOS1_Security_thm);

(*******************************)
(* Security Simulation Theorem *)
(*******************************)

val SecuritySimulation_thm =
TAC_PROOF(
([],
 ``!(M:(Statements,'worlds,Roles,'Int,'Sec)Kripke)(Oi:'Int po)(Os:'Sec po)(M1:modes)(M2:modes) mlist clist1 clist2 plist1 plist2.
   ((TR1 (M,Oi,Os)(Messages (mlist:(Statements,Roles,'Int,'Sec)Form list))
    (CFG M1 (Certs (clist1:(Statements,Roles,'Int,'Sec)Form list))(Policies (plist1:(Statements,Roles,'Int,'Sec)Form list)))
    (CFG M2 (Certs (clist2:(Statements,Roles,'Int,'Sec)Form list))(Policies (plist2:(Statements,Roles,'Int,'Sec)Form list))))) ==>
   ((TR0 (M,Oi,Os) M1 M2) /\ ((M,Oi,Os) sat (prop (MODE M2))))``),
(REWRITE_TAC [TR1_cases] THEN
 REPEAT STRIP_TAC THEN
 IMP_RES_TAC (TypeBase.one_one_of ``:('Int,'Sec)configuration``) THEN
 IMP_RES_TAC (TR0_rules) THEN
 ASM_REWRITE_TAC []));

val _ = save_thm("SecuritySimulation_thm",SecuritySimulation_thm);


(***********************)
(* Refinement Theorems *)
(***********************)

(******************************************************)
(* Abstraction from sos1 configurations to sos0 modes *)
(* is done by projecting the mode from configurations *)
(******************************************************)
val abs1_def = 
Define
`abs1 (CFG mode (Certs clist) (Policies plist)) = mode`;

val S1ImplementsS0_thm =
TAC_PROOF(
([],
 ``!(M:(Statements,'worlds,Roles,'Int,'Sec)Kripke)(Oi:'Int po)(Os:'Sec po)(M1:modes)(M2:modes) mlist clist1 clist2 plist1 plist2.
    (TR1 ((M:(Statements,'worlds,Roles,'Int,'Sec)Kripke),(Oi:'Int po),(Os:'Sec po))(Messages (mlist:(Statements,Roles,'Int,'Sec)Form list))
    (CFG M1 (Certs (clist1:(Statements,Roles,'Int,'Sec)Form list))(Policies (plist1:(Statements,Roles,'Int,'Sec)Form list)))
    (CFG M2 (Certs (clist2:(Statements,Roles,'Int,'Sec)Form list))(Policies (plist2:(Statements,Roles,'Int,'Sec)Form list)))) ==>
   ((TR0 (M,Oi,Os) (abs1(CFG M1 (Certs clist1)(Policies plist1)))(abs1(CFG M2 (Certs clist2)(Policies plist2))) 
    /\ ((M,Oi,Os) sat (prop (MODE (abs1(CFG M2 (Certs clist2)(Policies plist2))))))))``),
(REWRITE_TAC [abs1_def,SecuritySimulation_thm]));

val _ = save_thm("S1ImplementsS0_thm",S1ImplementsS0_thm);

val _ = export_theory ();
val _ = print_theory "sos1";

end (* structure *)