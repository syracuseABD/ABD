(* Created by S-K Chin 2/20/2009. modified by L.Morris 3/13/09 *)
(* These HOL/ml functions support the forward inference rule style of *)
(* reasoning in the access-control logic (see Access Control, Security,*)
(* and Trust: A Logical Approach, Shiu-Kai Chin and Susan Older, *)
(* CRC Press.*)

(* Modified by S-K Chin 11/9/2011. Added And_Says_LR and And_Says_RL *)

(* Modified by S. Perkins 8/12/2015. Added tactics section *)

structure acl_infRules :> acl_infRules =
struct

(* Interactive mode
set_trace "Unicode" 0;
app load ["pred_setTheory", "pred_setLib", "relationTheory", "aclfoundationTheory",
          "aclsemanticsTheory", "aclrulesTheory", "aclDrulesTheory",
	  "pred_setSyntax","aclTermFuns"];
*)
(*********Load the theories on which the inference rules are based******)
open HolKernel boolLib Parse;
open bossLib pred_setLib pred_setTheory;
open aclfoundationTheory aclsemanticsTheory aclrulesTheory;
open aclDrulesTheory relationTheory;
open aclTermFuns pred_setSyntax;

(******* This tactic is from Lockwood Morris************)
(* modified by skc with the substitution of DECIDE_TAC   *)
(* for TAUT_TAC. DECIDE_TAC has superceded TAUT_TAC *)
(***********************************************************
* ACL_TAUT_TAC
* 
* ACL_TAUT_TAC : tactic
*
* SYNOPSIS
* Invoke decision procedures to prove propositional formulas
* and partial order relations in the access-control logic.
*
* DESCRIPTION
* When given a propositional formula f in the access-control logic
* using only notf, andf, orf, impf, eqf,  eqn, lte, and lt, 
* ACL_TAUT_TAC attempts to prove f true in all Kripke structures
* (M,Oi,Os).
*
*     A ?- (M,Oi,Os) sat f
*    =================== ACL_TAUT_TAC 
*     A |-  (M,Oi,Os) sat f
*
* FAILURE
* Fails if f is not a propositional tautology, e.g., p and notf p.
***********************************************************)

val ACL_TAUT_TAC =
    REWRITE_TAC 
    [sat_allworld, world_T, world_F, world_not, 
     world_and, world_or, world_imp, world_eq,
     world_eqn, world_lte, world_lt]
    THEN DECIDE_TAC;

(***********************************************************
* ACL_TAUT
*
* ACL_TAUT : term -> thm
*
* SYNOPSIS
* Attempts to prove a proposition f in the access-control logic
* is true in all Kripke models (M,Oi,Os).
*
* DESCRIPTION
* When applied to a term f, which must have type Form,
* ACL_TAUT attempts to prove (M,Oi,Os) sat f.
*
*     ----------------  ACL_TAUT f
*     |- (M,Oi,Os) sat f
*
* FAILURE
* Fails if f is not a tautology.
***********************************************************)
(*******OLD DEFINITION***********
fun ACL_TAUT f =
    TAC_PROOF(([],(Term `(M,Oi,Os) sat ^f`)),
    ACL_TAUT_TAC);
********************************)
fun ACL_TAUT f =
let
 val f_type = type_of f
 val f_type_parts = dest_type f_type
 val [prop_type, name_type, integ_type, sec_type] = snd f_type_parts
 val M_type = 
   mk_type ("Kripke",[prop_type, ``:'b``, name_type, integ_type, sec_type])
 val term = 
   Term`((M : ^(ty_antiq M_type)),(Oi : ^(ty_antiq integ_type) po),
         (Os : ^(ty_antiq sec_type) po)) sat ^f`
 in
    TAC_PROOF(([],term),ACL_TAUT_TAC)
 end;
(***********************************************************
* ACL_ASSUM
*
* ACL_ASSUM : term -> thm
*
* SYNOPSIS
* Introduces an assumption in the access-control logic
*
* DESCRIPTION
* When applied to a term f, which must have type Form,
* ACL_ASSUM introduces a theorem 
* (M,Oi,Os) sat f |- (M,Oi,Os) sat f.
*
*     -----------------------------  ACL_ASSUM f
*    (M,Oi,Os) sat f |- (M,Oi,Os) sat f
*
* FAILURE
* Fails unless f has type Form.
***********************************************************)
(*******OLD DEFINITION***********
fun ACL_ASSUM f = ASSUME
 (Term `((M:('a,'b,'c,'d,'e)Kripke),(Oi:'d po),(Os:'e po)) sat ^f`);
********************************)

fun ACL_ASSUM f = 
let
 val f_type = type_of f
 val f_type_parts = dest_type f_type
 val [prop_type, name_type, integ_type, sec_type] = snd f_type_parts
 val M_type = 
   mk_type ("Kripke",[prop_type, ``:'b``, name_type, integ_type, sec_type])
 val term = 
   Term`((M : ^(ty_antiq M_type)),(Oi : ^(ty_antiq integ_type) po),
         (Os : ^(ty_antiq sec_type) po)) sat ^f`
 in
   ASSUME term
 end;

(***********************************************************
* ACL_ASSUM2
*
* ACL_ASSUM : term -> term -> term -> thm
*
* SYNOPSIS
* Introduces an assumption in the access-control logic
* given a formula f, and partial orderings on integrity
* labels Oi and security labels Os
*
* DESCRIPTION
* When applied to a term f, which must have type Form,
* Oi of type integ_type po, and Os of type sec_type po,
* ACL_ASSUMs introduces a theorem 
* (M,Oi,Os) sat f |- (M,Oi,Os) sat f.
*
*     -----------------------------  ACL_ASSUM2 f Oi Os
*    (M,Oi,Os) sat f |- (M,Oi,Os) sat f
*
* FAILURE
* Fails unless f has type Form, and Oi and Os have types
* integ_type po and sec_type po, respectively
***********************************************************)
fun ACL_ASSUM2 f Oi Os = 
let
 val f_type = type_of f
 val f_type_parts = dest_type f_type
 val [prop_type, name_type, integ_type, sec_type] = snd f_type_parts
 val M_type = 
   mk_type ("Kripke",[prop_type, ``:'b``, name_type, integ_type, sec_type])
 val term = 
   Term`((M : ^(ty_antiq M_type)),(^Oi : ^(ty_antiq integ_type) po),
         (^Os : ^(ty_antiq sec_type) po)) sat ^f`
 in
   ASSUME term
 end;

(***********************************************************
* ACL_MP
*
* ACL_MP : thm -> thm -> thm
*
* SYNOPSIS
* Implements Modus Ponens in the access-control logic
*
* DESCRIPTION
* When applied to theorems A1 |- (M,Oi,Os) sat f1 and
* A2 |- (M,Oi,Os) sat f1 impf f2 in the access-control logic,
* ACL_MP introduces a theorem A1 u A2 |- (M,Oi,Os) sat f2.
*
*     A1 |- (M,Oi,Os) sat f1   A2 |- (M,Oi,Os) sat f1 impf f2
*     -------------------------------------------------  ACL_MP
*                         A1 u A2 |- (M,Oi,Os) sat f2
*
* FAILURE
* Fails unless f1 in the first theorem is the same as f1 in the second
* theorem.
***********************************************************)
fun ACL_MP th1 th2 = MATCH_MP (MATCH_MP (SPEC_ALL Modus_Ponens) th1) th2;

(***********************************************************
* SAYS
*
* SAYS : term -> thm -> thm
*
* SYNOPSIS
* Applies the Says inference rule to a theorem A |- (M,Oi,Os) sat f 
* in the access-control logic.
*
* DESCRIPTION
*
*             A |- (M,Oi,Os) sat f
*         ------------------------- SAYS P f
*         A |- (M,Oi,Os) sat P says f
*
* FAILURE
* Fails unless the input theorem is a double negation in the
* access-control logic
***********************************************************)
fun SAYS Q th = (SPEC Q (MATCH_MP Says th));

(******
fun SAYS princ form = 
    ISPECL [princ,form]  
    (ISPECL [``(M :('a, 'b, 'c, 'd, 'e) Kripke)``,``(Oi :'d po)``,
             ``(Os :'e po)``]Says);
*******)

(***********************************************************
* MP_SAYS
*
* MP_SAYS : term -> term -> term -> thm
*
* SYNOPSIS
* implements MP Says rule 
*
* DESCRIPTION
*
*  ----------------------------------------------------  MP_SAYS P f1 f2
*  |- (M,Oi,Os) sat (P says (f1 impf f2)) impf
*     ((P says f1) impf (P says f2))
*
* FAILURE
* Fails unless princ is a principal,f1 and f2 are terms in the
* access-control logic, and princ, f1, and f2 have consistent
* types.
***********************************************************)
(*******OLD DEFINITION***********
fun MP_SAYS princ f1 f2 = 
    ISPECL [princ, f1, f2](SPECL [``M:('a,'b,'c,'d,'e)Kripke``, ``Oi:'d po``, ``Os: 'e po``] MP_Says);
********************************)
fun MP_SAYS princ f1 f2 = 
let
 val f1_type = type_of f1
 val f1_type_parts = dest_type f1_type
 val [prop_type, name_type, integ_type, sec_type] = snd f1_type_parts
 val M_type = 
   mk_type ("Kripke",[prop_type, ``:'b``, name_type, integ_type, sec_type])
 in
   ISPECL
   [``M : ^(ty_antiq M_type)``,``Oi : ^(ty_antiq integ_type) po``,
    ``Os : ^(ty_antiq sec_type) po``, princ, f1, f2]
   MP_Says
 end;
 
(***********************************************************
* ACL_MT
*
* ACL_MT : thm -> thm -> thm
*
* SYNOPSIS
* Implements Modus Tollens in the access-control logic
*
* DESCRIPTION
* When applied to theorems A1 |- (M,Oi,Os) sat notf f2 and
* A2 |- (M,Oi,Os) sat f1 impf f2 in the access-control logic,
* ACL_MT introduces a theorem A1 u A2 |- (M,Oi,Os) sat notf f1.
*
*     A1 |- (M,Oi,Os) sat f1 impf f2    A2 |- (M,Oi,Os) sat notf f2
*     ------------------------------------------------------  ACL_MT
*                         A1 u A2 |- (M,Oi,Os) sat notf f1
*
* FAILURE
* Fails unless f2 in the first theorem is the same as f2 in the second
* theorem.
***********************************************************)
fun ACL_MT th1 th2 = MATCH_MP (MATCH_MP (SPEC_ALL Modus_Tollens) th1) th2;

(***********************************************************
* ACL_SIMP1
*
* ACL_SIMP1 : thm -> thm
*
* SYNOPSIS
* Extracts left conjunct of a theorem in the access-control logic.
*
* DESCRIPTION
*
*     A |- (M,Oi,Os) sat f1 andf f2
*     --------------------------  ACL_SIMP1
*          A |- (M,Oi,Os) sat f1
*
* FAILURE
* Fails unless the input theorem is a conjunction in the
* access-control logic.
***********************************************************)
fun ACL_SIMP1 th = MATCH_MP (SPEC_ALL Simplification1) th;

(***********************************************************
* ACL_SIMP2
*
* ACL_SIMP2 : thm -> thm
*
* SYNOPSIS
* Extracts right conjunct of a theorem in the access-control logic.
*
* DESCRIPTION
*
*     A |- (M,Oi,Os) sat f1 andf f2
*     --------------------------  ACL_SIMP2
*          A |- (M,Oi,Os) sat f2
*
* FAILURE
* Fails unless the input theorem is a conjunction in the
* access-control logic.
***********************************************************)
fun ACL_SIMP2 th = MATCH_MP (SPEC_ALL Simplification2) th;

(***********************************************************
* ACL_CONJ
*
* ACL_CONJ : thm -> thm -> thm
*
* SYNOPSIS
* Introduces a conjunction in the access-control logic
*
* DESCRIPTION
*
*     A1 |- (M,Oi,Os) sat f1   A2 |- (M,Oi,Os) sat f2
*     -------------------------------------------------  ACL_CONJ
*                         A1 u A2 |- (M,Oi,Os) sat f1 andf f2
*
* FAILURE
* Fails unless both theorems are of the form A |- (M,Oi,Os) sat f.
***********************************************************)
fun ACL_CONJ th1 th2 = MATCH_MP(MATCH_MP (SPEC_ALL Conjunction) th1) th2;

(***********************************************************
* ACL_DISJ1
*
* ACL_DISJ1 : term -> thm -> thm
*
* SYNOPSIS
* Introduces a right disjunct into the conclusion of an access-control
* logic theorem
*
* DESCRIPTION
*
*               A |- (M,Oi,Os) sat f1
*         --------------------------  ACL_DISJ1 f2
*          A |- (M,Oi,Os) sat f1 orf f2
*
* FAILURE
* Fails unless the input theorem is a disjunction in the
* access-control logic and the types of f1 and f2 are the same.
***********************************************************)
(****** old definition *****
fun ACL_DISJ1 f th = (SPEC f) (GEN ``f2`` (MATCH_MP (SPEC_ALL Disjunction1) th));
*****)
fun ACL_DISJ1 f th = 
let
 val f_type = type_of f
 val term = Term`f2:^(ty_antiq f_type)`
in
 SPEC f (GEN term (MATCH_MP (SPEC_ALL Disjunction1) th))
end;
  

(***********************************************************
* ACL_DISJ2
*
* ACL_DISJ2 : term -> thm -> thm
*
* SYNOPSIS
* Introduces a left disjunct into the conclusion of an access-control
* logic theorem
*
* DESCRIPTION
*
*               A |- (M,Oi,Os) sat f2
*         --------------------------  ACL_DISJ2 f1
*          A |- (M,Oi,Os) sat f1 orf f2
*
* FAILURE
* Fails unless the input theorem is a disjunction in the
* access-control logic and the types of f1 and f2 are the same.
***********************************************************)
(*******OLD DEFINITION**************
fun ACL_DISJ2 f1 th = (SPEC f1) (MATCH_MP (SPEC_ALL Disjunction2) th);
***********************************)
fun ACL_DISJ2 f th = 
let
 val f_type = type_of f
 val term = Term`f1:^(ty_antiq f_type)`
in
 SPEC f (GEN term (MATCH_MP (SPEC_ALL Disjunction2) th))
end;
  


(***********************************************************
* CONTROLS
*
* CONTROLS : thm->thm -> thm
*
* SYNOPSIS
* Deduces formula f if the principal who says f also controls f.
*
* DESCRIPTION
*
*     A1 |- (M,Oi,Os) sat P controls f   A2 |- (M,Oi,Os) sat P says f
*     --------------------------------------------------------  CONTROLS
*                         A1 u A2 |- (M,Oi,Os) sat f
*
* FAILURE
* Fails unless the theorems match in terms of principals and formulas
* in the access-control logic.
***********************************************************)
fun CONTROLS th1 th2 = MATCH_MP (MATCH_MP (SPEC_ALL Controls) th2) th1;

(***********************************************************
* REPS
*
* REPS : thm -> thm -> thm -> thm
*
* SYNOPSIS
* Concludes statement f given theorems on delegation, quoting, and 
* jurisdiction.
*
* DESCRIPTION
*
* A1 |- (M,Oi,Os) sat reps P Q f  A2 |- (M,Oi,Os) sat (P quoting Q) says f
*                            A3 |- (M,Oi,Os) sat Q controls f
*     --------------------------------------------------------  REPS
*                             A1 u A2 u A3 |- (M,Oi,Os) sat f
*
* FAILURE
* Fails unless M, Oi, Os, P, Q, and f match in all three theorems.
***********************************************************)
fun REPS th1 th2 th3 = 
    MATCH_MP(MATCH_MP (MATCH_MP (SPEC_ALL Reps) th1) th2) th3;

(***********************************************************
* REP_SAYS
*
* REP_SAYS : thm -> thm -> thm
*
* SYNOPSIS
* Concludes statement f given theorems on delegation, quoting, and 
* jurisdiction.
*
* DESCRIPTION
*
* A1 |- (M,Oi,Os) sat reps P Q f  A2 |- (M,Oi,Os) sat (P quoting Q) says f
*     --------------------------------------------------------  REP_SAYS
*                             A1 u A2 |- (M,Oi,Os) sat Q says f
*
* FAILURE
* Fails unless M, Oi, Os, P, Q, and f match in all three theorems.
***********************************************************)
fun REP_SAYS th1 th2 = MATCH_MP (MATCH_MP (SPEC_ALL Rep_Says) th1) th2;

(***********************************************************
* ACL_DN
*
* ACL_DN : thm -> thm
*
* SYNOPSIS
* Applies double negation to formula in the access-control logic
*
* DESCRIPTION
*
*         A |- (M,Oi,Os) sat notf(notf f)
*         ---------------------------  ACL_DN
*               A |- (M,Oi,Os) sat f
*
* FAILURE
* Fails unless the input theorem is a double negation in the
* access-control logic
***********************************************************)
fun ACL_DN th = MATCH_MP (SPEC_ALL Double_Negation) th;

(***********************************************************
* SPEAKS_FOR
*
* SPEAKS_FOR : thm -> thm -> thm
*
* SYNOPSIS
* Applies Derived Speaks For to theorems in the access-control logic
*
* DESCRIPTION
*
*  A1 |- (M,Oi,Os) sat P speaks_for Q   A2 |- (M,Oi,Os) sat P says f
*  ----------------------------------------------------------- SPEAKS_FOR
*                    A1 u A2 |- (M,Oi,Os) sat Q says f
*
* FAILURE
* Fails unless the first theorem is of the form P speaksfor Q, the
* second is P says f, and the types are the same.
***********************************************************)
fun SPEAKS_FOR th1 th2 =
             MATCH_MP (MATCH_MP (SPEC_ALL Derived_Speaks_For) th1) th2;


(***********************************************************
* HS
*
* HS : thm -> thm -> thm
*
* SYNOPSIS
* Applies hypothetical syllogism to theorems in the access-control logic
*
* DESCRIPTION
*
*  A1 |- (M,Oi,Os) sat f1 impf f2   A2 |- (M,Oi,Os) sat f2 impf f3
*  -------------------------------------------------------- HS
*               A1 u A2 |- (M,Oi,Os) sat f1 impf f3
*
* FAILURE
* Fails unless the input theorems match in their consequent and
* antecedent in access-control logic
***********************************************************)
fun HS th1 th2 = MATCH_MP(MATCH_MP (SPEC_ALL Hypothetical_Syllogism) th1) th2;


(***********************************************************
* DC
*
* DC : thm -> thm -> thm
*
* SYNOPSIS
* Applies Derived Controls rule to theorems in the access-control logic
*
* DESCRIPTION
*
*  A1 |- (M,Oi,Os) sat P speaks_for Q   A2 |- (M,Oi,Os) sat Q controls f
*  -------------------------------------------------------------- DC
*               A1 u A2 |- (M,Oi,Os) sat P controls f
*
* FAILURE
* Fails unless the input theorems match in their corresponding principal
* names
***********************************************************)
fun DC th1 th2 = MATCH_MP(MATCH_MP (SPEC_ALL Derived_Controls) th1) th2;

(***********************************************************
* SAYS_SIMP1
*
* SAYS_SIMP1 : thm -> thm
*
* SYNOPSIS
* Applies the Says_Simplification1 rule to conjunctive statements within
* says statements in theorems in the access-control logic
*
* DESCRIPTION
*
*   A |- (M,Oi,Os) sat P says (f1 andf f2)
*  ---------------------------------- SAYS_SIMP1
*          A |- (M,Oi,Os) sat P says f1
*
* FAILURE
* Fails unless the input theorem is a conjunction within a
* says statement in the access-control logic
***********************************************************)
fun SAYS_SIMP1 th = MATCH_MP (SPEC_ALL Says_Simplification1) th;

(***********************************************************
* SAYS_SIMP2
*
* SAYS_SIMP2 : thm -> thm
*
* SYNOPSIS
* Applies the Says_Simplification2 rule to conjunctive statements within
* says statements in theorems in the access-control logic
*
* DESCRIPTION
*
*   A |- (M,Oi,Os) sat P says (f1 andf f2)
*  ---------------------------------- SAYS_SIMP2
*          A |- (M,Oi,Os) sat P says f2
*
* FAILURE
* Fails unless the input theorem is a conjunction within a
* says statement in the access-control logic
***********************************************************)
fun SAYS_SIMP2 th = MATCH_MP (SPEC_ALL Says_Simplification2) th;

(***********************************************************
* DOMS_TRANS
*
* DOMS_TRANS : thm -> thm -> thm
*
* SYNOPSIS
* Applies transitivity of doms to theorems in the access-control logic
*
* DESCRIPTION
*
*  A1 |- (M,Oi,Os) sat l1 doms l2   A2 |- (M,Oi,Os) sat l2 doms l3
*  -------------------------------------------------------- DOMS_TRANS
*               A1 u A2 |- (M,Oi,Os) sat l1 doms l3
*
* FAILURE
* Fails unless l1, l2, and l3 match appropriately and have the
* same type.
***********************************************************)
fun DOMS_TRANS th1 th2 =
                MATCH_MP(MATCH_MP (SPEC_ALL doms_transitive) th1) th2;

(***********************************************************
* DOMI_TRANS
*
* DOMI_TRANS : thm -> thm -> thm
*
* SYNOPSIS
* Applies transitivity of domi to theorems in the access-control logic
*
* DESCRIPTION
*
*  A1 |- (M,Oi,Os) sat l1 domi l2   A2 |- (M,Oi,Os) sat l2 domi l3
*  -------------------------------------------------------- DOMI_TRANS
*               A1 u A2 |- (M,Oi,Os) sat l1 domi l3
*
* FAILURE
* Fails unless the input theorems match in their corresponding terms
***********************************************************)
fun DOMI_TRANS th1 th2 =
             MATCH_MP(MATCH_MP (SPEC_ALL domi_transitive) th1) th2;

(***********************************************************
* SL_DOMS
*
* SL_DOMS : thm -> thm -> thm -> thm
*
* SYNOPSIS
* Applies sl_doms to theorems in the access-control logic
*
* DESCRIPTION
*
*  A1 |- (M,Oi,Os) sat sl P eqs l1
*  A2 |- (M,Oi,Os) sat sl Q eqs l2  
*  A3 |- (M,Oi,Os) sat l2 doms l1
*  --------------------------------------------------------------- SL_DOMS
*  A1 u A2 u A3 |- (M,Oi,Os) sat sl Q doms sl P
*
* FAILURE
* Fails unless the types are consistent across the three
* input theorems
***********************************************************)
fun SL_DOMS th1 th2 th3 =
   MATCH_MP (MATCH_MP (MATCH_MP sl_doms th1) th2) th3;

(***********************************************************
* IL_DOMI
*
* IL_DOMI : thm -> thm -> thm -> thm
*
* SYNOPSIS
* Applies il_doms to theorems in the access-control logic
*
* DESCRIPTION
*
*         A1 |- (M,Oi,Os) sat il P eqi l1
*         A2 |- (M,Oi,Os) sat il Q eqi l2  
*         A3 |- (M,Oi,Os) sat l2 domi l1
*  -------------------------------------------- IL_DOMI
*  A1 u A2 u A3 |- (M,Oi,Os) sat il Q domi il P
*
* FAILURE
* Fails unless the types are consistent among the three
* theorems.
***********************************************************)
fun IL_DOMI th1 th2 th3 =
   MATCH_MP (MATCH_MP (MATCH_MP il_domi th1) th2) th3;

(***********************************************************
* QUOTING_RL
*
* QUOTING_RL : thm -> thm
*
* SYNOPSIS
* Applies quoting rule to theorems in the access-control logic
*
* DESCRIPTION
*    th [P says Q says f/A]
*  ------------------------- QUOTING_RL
*  th [P quoting Q says f/A]
*
* FAILURE
* Fails unless the input theorem is of the form P says Q
* says f.
***********************************************************)
fun QUOTING_RL th = REWRITE_RULE [GSYM(SPEC_ALL Quoting_Eq)] th;

(***********************************************************
* QUOTING_LR
*
* QUOTING_LR : thm -> thm
*
* SYNOPSIS
* Applies quoting rule to theorems in the access-control logic
*
* DESCRIPTION
*               th [P quoting Q says f/A]
*  -----------------------------QUOTING_LR
*               th [P says Q says f/A]
*
* FAILURE
* Fails unless the input theorem is of the form P quoting Q
* says f.
***********************************************************)
fun QUOTING_LR th = REWRITE_RULE [SPEC_ALL Quoting_Eq] th;

(***********************************************************
* EQN_LTE
*
* EQN_LTE : thm -> thm -> thm -> thm
*
* SYNOPSIS
* Applies eqn_lte to theorems in the access-control logic
*
* DESCRIPTION
*
*         A1 |- (M,Oi,Os) sat c1 eqn n1
*         A2 |- (M,Oi,Os) sat c2 eqn n2  
*         A3 |- (M,Oi,Os) sat n1 lte n2
*  -------------------------------------------- EQN_LTE
*  A1 u A2 u A3 |- (M,Oi,Os) sat c1 lte c2
*
* FAILURE
* Fails unless the types are consistent among the three
* theorems.
***********************************************************)
fun EQN_LTE th1 th2 th3 =
   MATCH_MP (MATCH_MP (MATCH_MP eqn_lte th1) th2) th3;

(***********************************************************
* EQN_LT
*
* EQN_LT : thm -> thm -> thm -> thm
*
* SYNOPSIS
* Applies eqn_lt to theorems in the access-control logic
*
* DESCRIPTION
*
*         A1 |- (M,Oi,Os) sat c1 eqn n1
*         A2 |- (M,Oi,Os) sat c2 eqn n2  
*         A3 |- (M,Oi,Os) sat n1 lt n2
*  -------------------------------------------- EQN_LT
*  A1 u A2 u A3 |- (M,Oi,Os) sat c1 lt c2
*
* FAILURE
* Fails unless the types are consistent among the three
* theorems.
***********************************************************)
fun EQN_LT th1 th2 th3 =
   MATCH_MP (MATCH_MP (MATCH_MP eqn_lt th1) th2) th3;

(***********************************************************
* EQN_EQN
*
* EQN_EQN : thm -> thm -> thm -> thm
*
* SYNOPSIS
* Applies eqn_eqn to theorems in the access-control logic
*
* DESCRIPTION
*
*         A1 |- (M,Oi,Os) sat c1 eqn n1
*         A2 |- (M,Oi,Os) sat c2 eqn n2  
*         A3 |- (M,Oi,Os) sat n1 eqn n2
*  -------------------------------------------- EQN_EQN
*  A1 u A2 u A3 |- (M,Oi,Os) sat c1 eqn c2
*
* FAILURE
* Fails unless the types are consistent among the three
* theorems.
***********************************************************)
fun EQN_EQN th1 th2 th3 =
   MATCH_MP (MATCH_MP (MATCH_MP eqn_eqn th1) th2) th3;


(***********************************************************
* AND_SAYS_RL
*
* AND_SAYS_RL : thm -> thm
*
* SYNOPSIS
* Applies quoting rule to theorems in the access-control logic
*
* DESCRIPTION
*    th [(P says f) andf (Q says f)/A]
*  ------------------------- AND_SAYS_RL
*  th [P meet Q says f/A]
*
* FAILURE
* Fails unless the input theorem is of the form 
* P says f  andf Q says f.
***********************************************************)
fun AND_SAYS_RL th = REWRITE_RULE [GSYM(SPEC_ALL And_Says_Eq)] th;

(***********************************************************
* AND_SAYS_LR
*
* AND_SAYS_LR : thm -> thm
*
* SYNOPSIS
* Applies And_Says rule to theorems in the access-control logic
*
* DESCRIPTION
*   th [P meet Q says f/A]
*  ------------------------------ AND_SAYS_LR
*   th [P says f andf Q says f/A]
*
* FAILURE
* Fails unless the input theorem is of the form P quoting Q
* says f.
***********************************************************)
fun AND_SAYS_LR th = REWRITE_RULE [SPEC_ALL And_Says_Eq] th;

(***********************************************************
* IDEMP_SPEAKS_FOR
*
* IDEMP_SPEAKS_FOR : term -> thm
*
* SYNOPSIS
* Specializes Idemp_Speaks_For to principal P
*
* DESCRIPTION
*  
*  ------------------- IDEMP_SPEAKS_FOR P
*   |- P speaks_for P
*
* FAILURE
* Fails unless the term is a principal
***********************************************************)
fun IDEMP_SPEAKS_FOR term = ISPEC term (GEN ``P:'c Princ``(SPEC_ALL Idemp_Speaks_For));

(***********************************************************
* MONO_SPEAKS_FOR
*
* MONO_SPEAKS_FOR : thm -> thm -> thm
*
* SYNOPSIS
* Applies Mono_speaks_for to theorems in the access-control logic
*
* DESCRIPTION
*
*         A1 |- (M,Oi,Os) sat P speaks_for P'
*         A2 |- (M,Oi,Os) sat Q speaks_for Q'
*  ----------------------------------------------------------------- MONO_SPEAKS_FOR
*  A1 u A2 |- (M,Oi,Os) sat (P quoting Q) speaks_for (P' quoting Q')
*
* FAILURE
* Fails unless the types are consistent among the two
* theorems.
***********************************************************)
fun MONO_SPEAKS_FOR th1 th2 =
   (MATCH_MP (MATCH_MP Mono_speaks_for th1) th2);

(***********************************************************
* TRANS_SPEAKS_FOR
*
* TRANS_SPEAKS_FOR : thm -> thm -> thm
*
* SYNOPSIS
* Applies Trans_Speaks_For to theorems in the access-control logic
*
* DESCRIPTION
*
*    A1 |- (M,Oi,Os) sat P speaks_for Q
*    A2 |- (M,Oi,Os) sat Q speaks_for R
*  --------------------------------------- TRANS_SPEAKS_FOR
*  A1 u A2 |- (M,Oi,Os) sat P speaks_for R
*
* FAILURE
* Fails unless the types are consistent among the two
* theorems.
***********************************************************)
fun TRANS_SPEAKS_FOR th1 th2 =
   (MATCH_MP (MATCH_MP Trans_Speaks_For th1) th2);

(* -------------------------------------------------------------------------- *)
(* EQF_ANDF1                                                                  *)
(*                                                                            *)
(* EQF_ANDF1 : thm -> thm -> thm                                              *)
(*                                                                            *)
(* SYNOPSIS                                                                   *)
(* Applies eqf_andf1 to substitute an equivalent term for another in the left *)
(* conjunct.                                                                  *)
(*                                                                            *)
(* DESCRIPTION                                                                *)
(*                                                                            *)
(*    A1 |- (M,Oi,Os) sat f eqf f'                                            *)
(*    A2 |- (M,Oi,Os) sat f andf g                                            *)
(* ---------------------------------- EQF_ANDF1                               *)
(* A1 u A2 |- (M,Oi,Os) sat f' andf g                                         *)
(*                                                                            *)
(* FAILURE                                                                    *)
(* Fails unless the first theorem is an equivance and the second theorem is   *)
(* a conjunction.  Fails unless all the types are consistent.                 *)
(* -------------------------------------------------------------------------- *)
fun EQF_ANDF1 th1 th2 =
let
 val th3 = MATCH_MP eqf_andf1 th1
in
 MATCH_MP th3 th2
end

(* -------------------------------------------------------------------------- *)
(* EQF_ANDF2                                                                  *)
(*                                                                            *)
(* EQF_ANDF2 : thm -> thm -> thm                                              *)
(*                                                                            *)
(* SYNOPSIS                                                                   *)
(* Applies eqf_andf2 to substitute an equivalent term for another in the left *)
(* conjunct.                                                                  *)
(*                                                                            *)
(* DESCRIPTION                                                                *)
(*                                                                            *)
(*    A1 |- (M,Oi,Os) sat f eqf f'                                            *)
(*    A2 |- (M,Oi,Os) sat g andf f                                            *)
(* ---------------------------------- EQF_ANDF2                               *)
(* A1 u A2 |- (M,Oi,Os) sat g andf f'                                         *)
(*                                                                            *)
(* FAILURE                                                                    *)
(* Fails unless the first theorem is an equivance and the second theorem is   *)
(* a conjunction.  Fails unless all the types are consistent.                 *)
(* -------------------------------------------------------------------------- *)
fun EQF_ANDF2 th1 th2 =
let
 val th3 = MATCH_MP eqf_andf2 th1
in
 MATCH_MP th3 th2
end

(* -------------------------------------------------------------------------- *)
(* EQF_CONTROLS                                                               *)
(*                                                                            *)
(* EQF_CONTROLS : thm -> thm -> thm                                           *)
(*                                                                            *)
(* SYNOPSIS                                                                   *)
(* Applies eqf_controls to substitute an equivalent formula f' for f in       *)
(* P controls f                                                               *)
(*                                                                            *)
(* DESCRIPTION                                                                *)
(*                                                                            *)
(*    A1 |- (M,Oi,Os) sat f eqf f'                                            *)
(*    A2 |- (M,Oi,Os) sat P controls f                                        *)
(* ---------------------------------- EQF_CONTROLS                            *)
(* A1 u A2 |- (M,Oi,Os) sat P controls f'                                     *)
(*                                                                            *)
(* FAILURE                                                                    *)
(* Fails unless the first theorem is an equivance and the second theorem is   *)
(* a conjunction.  Fails unless all the types are consistent.                 *)
(* -------------------------------------------------------------------------- *)
fun EQF_CONTROLS th1 th2 =
let
 val th3 = MATCH_MP eqf_controls th1
in
 MATCH_MP th3 th2
end

(* -------------------------------------------------------------------------- *)
(* EQF_EQF1                                                                   *)
(*                                                                            *)
(* EQF_EQF1 : thm -> thm -> thm                                               *)
(*                                                                            *)
(* SYNOPSIS                                                                   *)
(* Applies eqf_eqf1 to substitute an equivalent term for another in the left  *)
(* side of the equivalence                                                    *)
(*                                                                            *)
(* DESCRIPTION                                                                *)
(*                                                                            *)
(*    A1 |- (M,Oi,Os) sat f eqf f'                                            *)
(*    A2 |- (M,Oi,Os) sat f eqf g                                             *)
(* ---------------------------------- EQF_EQF1                                *)
(* A1 u A2 |- (M,Oi,Os) sat f' eqf g                                          *)
(*                                                                            *)
(* FAILURE                                                                    *)
(* Fails unless the first theorem is an equivance and the second theorem is   *)
(* a equivalence.  Fails unless all the types are consistent.                 *)
(* -------------------------------------------------------------------------- *)
fun EQF_EQF1 th1 th2 =
let
 val th3 = MATCH_MP eqf_eqf1 th1
in
 MATCH_MP th3 th2
end

(* -------------------------------------------------------------------------- *)
(* EQF_EQF2                                                                   *)
(*                                                                            *)
(* EQF_EQF2 : thm -> thm -> thm                                               *)
(*                                                                            *)
(* SYNOPSIS                                                                   *)
(* Applies eqf_eqf2 to substitute an equivalent term for another in the right *)
(* side of an equivalence.                                                    *)
(*                                                                            *)
(* DESCRIPTION                                                                *)
(*                                                                            *)
(*    A1 |- (M,Oi,Os) sat f eqf f'                                            *)
(*    A2 |- (M,Oi,Os) sat g eqf f                                             *)
(* ---------------------------------- EQF_EQF2                                *)
(* A1 u A2 |- (M,Oi,Os) sat g eqf f'                                          *)
(*                                                                            *)
(* FAILURE                                                                    *)
(* Fails unless the first theorem is an equivance and the second theorem is   *)
(* an equivalence.  Fails unless all the types are consistent.                *)
(* -------------------------------------------------------------------------- *)
fun EQF_EQF2 th1 th2 =
let
 val th3 = MATCH_MP eqf_eqf2 th1
in
 MATCH_MP th3 th2
end

(* -------------------------------------------------------------------------- *)
(* EQF_IMPF1                                                                  *)
(*                                                                            *)
(* EQF_IMPF1 : thm -> thm -> thm                                              *)
(*                                                                            *)
(* SYNOPSIS                                                                   *)
(* Applies eqf_impf1 to substitute an equivalent term for another in the left *)
(* side of an implication                                                     *)
(*                                                                            *)
(* DESCRIPTION                                                                *)
(*                                                                            *)
(*    A1 |- (M,Oi,Os) sat f eqf f'                                            *)
(*    A2 |- (M,Oi,Os) sat f impf g                                            *)
(* ---------------------------------- EQF_IMPF1                               *)
(* A1 u A2 |- (M,Oi,Os) sat f' impf g                                         *)
(*                                                                            *)
(* FAILURE                                                                    *)
(* Fails unless the first theorem is an equivance and the second theorem is   *)
(* an implication.  Fails unless all the types are consistent.                *)
(* -------------------------------------------------------------------------- *)
fun EQF_IMPF1 th1 th2 =
let
 val th3 = MATCH_MP eqf_impf1 th1
in
 MATCH_MP th3 th2
end

(* -------------------------------------------------------------------------- *)
(* EQF_IMPF2                                                                  *)
(*                                                                            *)
(* EQF_IMPF2 : thm -> thm -> thm                                              *)
(*                                                                            *)
(* SYNOPSIS                                                                   *)
(* Applies eqf_impf2 to substitute an equivalent term for another in the right*)
(* side of an implication.                                                    *)
(*                                                                            *)
(* DESCRIPTION                                                                *)
(*                                                                            *)
(*    A1 |- (M,Oi,Os) sat f eqf f'                                            *)
(*    A2 |- (M,Oi,Os) sat g impf f                                            *)
(* ---------------------------------- EQF_IMPF2                               *)
(* A1 u A2 |- (M,Oi,Os) sat g impf f'                                         *)
(*                                                                            *)
(* FAILURE                                                                    *)
(* Fails unless the first theorem is an equivance and the second theorem is   *)
(* an implication.  Fails unless all the types are consistent.                *)
(* -------------------------------------------------------------------------- *)
fun EQF_IMPF2 th1 th2 =
let
 val th3 = MATCH_MP eqf_impf2 th1
in
 MATCH_MP th3 th2
end

(* -------------------------------------------------------------------------- *)
(* EQF_NOTF                                                                   *)
(*                                                                            *)
(* EQF_NOTF : thm -> thm -> thm                                               *)
(*                                                                            *)
(* SYNOPSIS                                                                   *)
(* Applies eqf_notf to substitute an equivalent term for another in a         *)
(* negation.                                                                  *)
(*                                                                            *)
(* DESCRIPTION                                                                *)
(*                                                                            *)
(*    A1 |- (M,Oi,Os) sat f eqf f'                                            *)
(*    A2 |- (M,Oi,Os) sat notf f                                              *)
(* ---------------------------------- EQF_NOTF                                *)
(* A1 u A2 |- (M,Oi,Os) sat notf f'                                           *)
(*                                                                            *)
(* FAILURE                                                                    *)
(* Fails unless the first theorem is an equivance and the second theorem is   *)
(* a negation.  Fails unless all the types are consistent.                    *)
(* -------------------------------------------------------------------------- *)
fun EQF_NOTF th1 th2 =
let
 val th3 = MATCH_MP eqf_notf th1
in
 MATCH_MP th3 th2
end

(* -------------------------------------------------------------------------- *)
(* EQF_ORF1                                                                   *)
(*                                                                            *)
(* EQF_ORF1 : thm -> thm -> thm                                               *)
(*                                                                            *)
(* SYNOPSIS                                                                   *)
(* Applies eqf_orf1 to substitute an equivalent term for another in the left  *)
(* side of a disjunction.                                                     *)
(*                                                                            *)
(* DESCRIPTION                                                                *)
(*                                                                            *)
(*    A1 |- (M,Oi,Os) sat f eqf f'                                            *)
(*    A2 |- (M,Oi,Os) sat f orf g                                             *)
(* ---------------------------------- EQF_ORF1                                *)
(* A1 u A2 |- (M,Oi,Os) sat f' orf g                                          *)
(*                                                                            *)
(* FAILURE                                                                    *)
(* Fails unless the first theorem is an equivance and the second theorem is   *)
(* a disjunction. Fails unless all the types are consistent.                  *)
(* -------------------------------------------------------------------------- *)
fun EQF_ORF1 th1 th2 =
let
 val th3 = MATCH_MP eqf_orf1 th1
in
 MATCH_MP th3 th2
end

(* -------------------------------------------------------------------------- *)
(* EQF_ORF2                                                                   *)
(*                                                                            *)
(* EQF_ORF2 : thm -> thm -> thm                                               *)
(*                                                                            *)
(* SYNOPSIS                                                                   *)
(* Applies eqf_orf2 to substitute an equivalent term for another in the right *)
(* side of a disjunction.                                                     *)
(*                                                                            *)
(* DESCRIPTION                                                                *)
(*                                                                            *)
(*    A1 |- (M,Oi,Os) sat f eqf f'                                            *)
(*    A2 |- (M,Oi,Os) sat g orf f                                             *)
(* ---------------------------------- EQF_ORF2                                *)
(* A1 u A2 |- (M,Oi,Os) sat g orf f'                                          *)
(*                                                                            *)
(* FAILURE                                                                    *)
(* Fails unless the first theorem is an equivance and the second theorem is   *)
(* a disjunction. Fails unless all the types are consistent.                  *)
(* -------------------------------------------------------------------------- *)
fun EQF_ORF2 th1 th2 =
let
 val th3 = MATCH_MP eqf_orf2 th1
in
 MATCH_MP th3 th2
end

(* -------------------------------------------------------------------------- *)
(* EQF_REPS                                                                   *)
(*                                                                            *)
(* EQF_REPS : thm -> thm -> thm                                               *)
(*                                                                            *)
(* SYNOPSIS                                                                   *)
(* Applies eqf_reps to substitute an equivalent formula for another in a      *)
(* a delegation formula.                                                      *)
(*                                                                            *)
(* DESCRIPTION                                                                *)
(*                                                                            *)
(*    A1 |- (M,Oi,Os) sat f eqf f'                                            *)
(*    A2 |- (M,Oi,Os) sat reps P Q f                                          *)
(* ---------------------------------- EQF_REPS                                *)
(* A1 u A2 |- (M,Oi,Os) sat reps P Q f'                                       *)
(*                                                                            *)
(* FAILURE                                                                    *)
(* Fails unless the first theorem is an equivance and the second theorem is   *)
(* a delegation. Fails unless all the types are consistent.                   *)
(* -------------------------------------------------------------------------- *)
fun EQF_REPS th1 th2 =
let
 val th3 = MATCH_MP eqf_reps th1
in
 MATCH_MP th3 th2
end

(* -------------------------------------------------------------------------- *)
(* EQF_SAYS                                                                   *)
(*                                                                            *)
(* EQF_SAYS : thm -> thm -> thm                                               *)
(*                                                                            *)
(* SYNOPSIS                                                                   *)
(* Applies eqf_says to substitute an equivalent formula for another in a      *)
(* a says formula.                                                            *)
(*                                                                            *)
(* DESCRIPTION                                                                *)
(*                                                                            *)
(*    A1 |- (M,Oi,Os) sat f eqf f'                                            *)
(*    A2 |- (M,Oi,Os) sat P says f                                            *)
(* ---------------------------------- EQF_SAYS                                *)
(* A1 u A2 |- (M,Oi,Os) sat P says f'                                         *)
(*                                                                            *)
(* FAILURE                                                                    *)
(* Fails unless the first theorem is an equivance and the second theorem is   *)
(* a says formula. Fails unless all the types are consistent.                 *)
(* -------------------------------------------------------------------------- *)
fun EQF_SAYS th1 th2 =
let
 val th3 = MATCH_MP eqf_says th1
in
 MATCH_MP th3 th2
end


(*****************)
(**** Tactics ****)
(*****************)

(******************************************************************************
ACL_CONJ_TAC

ACL_CONJ_TAC : (’a*term)−>(’a*term)list*(thm list−>thm))

SYNOPSIS
Reduces an ACL conjunctive goal to two separate subgoals.

DESCRIPTION
When applied to a goal A ?- (M,Oi,Os) sat t1 andf t2, reduces it to the two sub-
goals corresponding to each conjunct separately.

        A ?- (M,Oi,Os) sat t1 andf t2
 ============================================= ACL_CONJ_TAC
           A ?- (M,Oi,Os) sat t1
           A ?- (M,Oi,Os) sat t2


FAILURE
Fails unless the conclusion of the goal is an ACL conjunction.
*******************************************************************************)

fun ACL_CONJ_TAC (asl,term) =
let
  val (tuple,conj) = dest_sat term
  val (conj1,conj2) = dest_andf conj
  val conjTerm1 = mk_sat (tuple,conj1)
  val conjTerm2 = mk_sat (tuple,conj2)
in
 ([(asl,conjTerm1),(asl,conjTerm2)], fn [th1,th2] => ACL_CONJ th1 th2)
end


(******************************************************************************
ACL_DISJ1_TAC 

ACL_DISJ1_TAC : (’a*term)−>((’a*term)list*(thm list−>thm))

SYNOPSIS
Selects the left disjunct of an ACL disjunctive goal.

DESCRIPTION
When applied to a goal A ?- (M,Oi,Os) sat t1 orf t2, the tactic ACL_DISJ1_-
TAC reduces it to the subgoal corresponding to the left disjunct.

    A ?- (M,Oi,Os) sat t1 orf t2
  ================================ ACL_DISJ1_TAC
      A ?- (M,Oi,Os) sat t1


FAILURE
Fails unless the goal is an ACL disjunction.
******************************************************************************)

fun ACL_DISJ1_TAC (asl,term) =
let
  val (tuple,disj) = dest_sat term
  val (disj1,disj2) = dest_orf disj
  val disjTerm1 = mk_sat (tuple,disj1)
in
  ([(asl,disjTerm1)], fn [th] => ACL_DISJ1 disj2 th)
end

(***************************************************************************** 
ACL_DISJ2_TAC 
ACL_DISJ2_TAC : (’a*term)−>((’a*term)list*(thm list−>thm))

SYNOPSIS
Selects the right disjunct of an ACL disjunctive goal.

DESCRIPTION
When applied to a goal A ?- (M,Oi,Os) sat t1 orf t2, the tactic ACL_DISJ2_-
TAC reduces it to the subgoal corresponding to the right disjunct.

  A ?- (M,Oi,Os) sat t1 orf t2
 ================================= ACL_DISJ2_TAC
  A ?- (M,Oi,Os) sat t2

FAILURE
Fails unless the goal is an ACL disjunction.

*****************************************************************************)
fun ACL_DISJ2_TAC (asl,term) =
let
  val (tuple,disj) = dest_sat term
  val (disj1,disj2) = dest_orf disj
  val disjTerm2 = mk_sat (tuple,disj2)
in
  ([(asl,disjTerm2)], fn [th] => ACL_DISJ2 disj1 th)
end

(****************************************************************************** 
ACL_MP_TAC 

ACL_MP_TAC : thm−>(’a*term)−>((’a*term)list*(thm list−>thm))

SYNOPSIS
Reduces a goal to an ACL implication from a known theorem.

DESCRIPTION
When applied to the theorem A’ |- (M,Oi,Os) sat s and the goal A ?- (M,Oi,Os)
sat t, the tactic ACL_MP_TAC reduces the goal to A ?- (M,Oi,Os) sat s impf t.
Unless A’ is a subset of A, this is an invalid tactic.

  A ?- (M,Oi,Os) sat t
 ================================= ACL_MP_TAC (A’ |- s)
  A ?- (M,Oi,Os) sat s impf t

FAILURE
Fails unless A’ is a subset of A.
******************************************************************************)

fun ACL_MP_TAC thb (asl,term) =
let
  val (tuple,form) = dest_sat term
  val (ntuple,nform) = dest_sat (concl thb)
  val newForm = mk_impf (nform,form)
  val newTerm = mk_sat (tuple,newForm)
  val predTerm = mk_sat (tuple,nform)
  val tupleType = type_of tuple
  val (_,[kripketype,_]) = dest_type tupleType
  val (_,[_,btype,_,_,_]) = dest_type kripketype
  val th2 = INST_TYPE [``:'b`` |-> btype] thb
in
    ([(asl,newTerm)], fn [th] => ACL_MP th2 th)
end

(***************************************************************************** 
ACL_AND_SAYS_RL_TAC 

ACL_AND_SAYS_RL_TAC : (’a*term)−>((’a*term)list*(thm list−>thm))

SYNOPSIS
Rewrites a goal with meet to two says statements.

DESCRIPTION
When applied to a goal A ?- (M,Oi,Os) sat p meet q says f, returns a new sub-
goal in the form A ?- (M,Oi,Os) sat (p says f) andf (q says f).

  A ?- (M,Oi,Os) sat p meet q says f
 ======================================= ACL_AND_SAYS_RL_TAC
  A ?- (M,Oi,Os) sat (p says f)
                        andf (q says f)

FAILURE
Fails unless the goal is in the form p meet q says f.
*****************************************************************************)

fun ACL_AND_SAYS_RL_TAC (asl,term) =
let
 val (tuple,form) = dest_sat term
 val (princs,prop) = dest_says form
 val (princ1,princ2) = dest_meet princs
 val conj1 = mk_says (princ1,prop)
 val conj2 = mk_says (princ2,prop)
 val conj = mk_andf (conj1,conj2)
 val newTerm = mk_sat (tuple,conj)
in
 ([(asl,newTerm)], fn [th] => AND_SAYS_RL th)
end

(****************************************************************************** 
ACL_AND_SAYS_LR_TAC 

ACL_AND_SAYS_LR_TAC : (’a*term)−>((’a*term)list*(thm list−>thm))

SYNOPSIS
Rewrites a goal with conjunctive says statements into a meet statement.

DESCRIPTION
When applied to a goal A ?- (M,Oi,Os) sat (p says f) andf (q says f), re-
turns a new subgoal in the form A ?- (M,Oi,Os) sat p meet q says f.

  A ?- (M,Oi,Os) sat (p says f)
                andf (q says f)
 ======================================== ACL_AND_SAYS_LR_TAC
    A ?- (M,Oi,Os) sat p meet q says f

FAILURE
Fails unless the goal is in the form (p says f) andf (q says f).
******************************************************************************)

fun ACL_AND_SAYS_LR_TAC (asl,term) =
let
 val (tuple,form) = dest_sat term
 val (conj1,conj2) = dest_andf form
 val (princ1,prop) = dest_says conj1
 val (princ2,_) = dest_says conj2
 val princs = mk_meet (princ1,princ2)
 val newForm = mk_says (princs,prop)
 val newTerm = mk_sat (tuple,newForm)
in
 ([(asl,newTerm)], fn [th] => AND_SAYS_LR th)
end

(***************************************************************************** 
ACL_CONTROLS_TAC 

ACL_CONTROLS_TAC : term−>(’a*term)−>((’a*term)list*(thm list−>thm))

SYNOPSIS
Reduces a goal to corresponding controls and says subgoals.

DESCRIPTION
When applied to a princ p and a goal A ?- (M,Oi,Os) sat f, returns a two new subgoals in the form A ?- (M,Oi,Os) sat p controls f and A ?- (M,Oi,Os) sat p
says f.

  A ?- (M,Oi,Os) sat f
 ======================================= ACL_CONTROLS_TAC p
  A ?- (M,Oi,Os) sat p controls f
  A ?- (M,Oi,Os) sat p says f

FAILURE
Fails unless the goal is a form type and p is a principle.
******************************************************************************)

fun ACL_CONTROLS_TAC princ (asl,term) = 
let
 val (tuple,form) = dest_sat term
 val newControls = mk_controls (princ,form)
 val newTerm1 = mk_sat (tuple,newControls)
 val newSays = mk_says (princ,form)
 val newTerm2 = mk_sat (tuple,newSays)
in
 ([(asl,newTerm1),(asl,newTerm2)], fn [th1,th2] => CONTROLS th1 th2)
end

(***************************************************************************** 
ACL_DC_TAC 

ACL_DC_TAC : term−>(’a*term)−>((’a*term)list*(thm list−>thm))

SYNOPSIS
Reduces a goal to corresponding controls and speaks f or subgoals.

DESCRIPTION
When applied to a principal q and a goal A ?- (M,Oi,Os) sat p controls f, returns a two new subgoals in the form A ?- (M,Oi,Os) sat p speaks_for q and A ?- (M,Oi,Os) sat q controls f.

  A ?- (M,Oi,Os) sat p controls f
 ======================================= ACL_DC_TAC q
  A ?- (M,Oi,Os) sat p speaks_for q
  A ?- (M,Oi,Os) sat q controls f

FAILURE
Fails unless the goal is an ACL controls statement and q is a principle.
******************************************************************************)

fun ACL_DC_TAC princ2 (asl,term) =
let
 val (tuple,form) = dest_sat term
 val (princ1,prop) = dest_controls form
 val formType = type_of form
 val speaksFor = ``(^princ1 speaks_for ^princ2):^(ty_antiq formType)``
 val newTerm1 = mk_sat (tuple,speaksFor)
 val newControls = mk_controls (princ2,prop)
 val newTerm2 = mk_sat (tuple,newControls)
in
 ([(asl,newTerm1),(asl,newTerm2)], fn [th1,th2] => DC th1 th2)
end

(***************************************************************************** 
ACL_DOMI_TRANS_TAC 

ACL_DOMI_TRANS_TAC : term−>(’a*term)−>((’a*term)list*(thm list−>thm))

SYNOPSIS
Reduces a goal to two subgoals using the transitive property of integrity levels.

DESCRIPTION
When applied to an integrity level l2 and a goal A ?- (M,Oi,Os) sat l1 domi l3, returns a two new subgoals in the form A ?- (M,Oi,Os) sat l1 domi l2 and A ?- (M,Oi,Os) sat l2 domi l3.

  A ?- (M,Oi,Os) sat l1 domi l3
 ====================================== ACL_DOMI_TRANS_TAC l2
  A ?- (M,Oi,Os) sat l1 domi l2
  A ?- (M,Oi,Os) sat l2 domi l3

FAILURE
Fails unless the goal is an ACL domi statement and l2 is an integrity level.
******************************************************************************)

fun ACL_DOMI_TRANS_TAC iLev2 (asl,term) =
let
 val (tuple,form) = dest_sat term
 val (iLev1,iLev3) = dest_domi form
 val formType = type_of form
 val newDomi1 = ``(^iLev1 domi ^iLev2):^(ty_antiq formType)``
 val newTerm1 = mk_sat (tuple,newDomi1)
 val newDomi2 = ``(^iLev2 domi ^iLev3):^(ty_antiq formType)``
 val newTerm2 = mk_sat (tuple,newDomi2)
in
 ([(asl,newTerm1),(asl,newTerm2)], fn [th1,th2] => DOMI_TRANS th1 th2)
end

(***************************************************************************** 
ACL_DOMS_TRANS_TAC 

ACL_DOMS_TRANS_TAC : term−>(’a*term)−>((’a*term)list*(thm list−>thm))

SYNOPSIS
Reduces a goal to two subgoals using the transitive property of security levels.

DESCRIPTION
When applied to a security level l2 and a goal A ?- (M,Oi,Os) sat l1 doms l3,
returns a two new subgoals in the form A ?- (M,Oi,Os) sat l1 doms l2 and A ?-
(M,Oi,Os) sat l2 doms l3.

  A ?- (M,Oi,Os) sat l1 doms l3
 ====================================== ACL_DOMS_TRANS_TAC l2
  A ?- (M,Oi,Os) sat l1 doms l2
  A ?- (M,Oi,Os) sat l2 doms l3

FAILURE
Fails unless the goal is an ACL doms statement and l2 is a security level.
*****************************************************************************)

fun ACL_DOMS_TRANS_TAC sLev2 (asl,term) =
let
 val (tuple,form) = dest_sat term
 val (sLev1,sLev3) = dest_doms form
 val formType = type_of form
 val newDoms1 = ``(^sLev1 doms ^sLev2):^(ty_antiq formType)``
 val newTerm1 = mk_sat (tuple,newDoms1)
 val newDoms2 = ``(^sLev2 doms ^sLev3):^(ty_antiq formType)``
 val newTerm2 = mk_sat (tuple,newDoms2)
in
 ([(asl,newTerm1),(asl,newTerm2)], fn [th1,th2] => DOMS_TRANS th1 th2)
end

(***************************************************************************** 
ACL_HS_TAC 

ACL_HS_TAC : term−>(’a*term)−>((’a*term)list*(thm list−>thm))

SYNOPSIS
Reduces a goal to two subgoals using the transitive property of ACL implications.

DESCRIPTION
When applied to an ACL formula f2 and a goal A ?- (M,Oi,Os) sat f1 impf f3,
returns a two new subgoals in the form A ?- (M,Oi,Os) sat f1 impf f2 and A ?-
(M,Oi,Os) sat f2 impf f3.

  A ?- (M,Oi,Os) sat f1 impf f3
 ======================================= ACL_HS_TAC f2
  A ?- (M,Oi,Os) sat f1 impf f2
  A ?- (M,Oi,Os) sat f2 impf f3

FAILURE
Fails unless the goal is an ACL implication and f2 is an ACL formula.
*****************************************************************************)

fun ACL_HS_TAC f2 (asl,term) =
let
 val (tuple,form) = dest_sat term
 val (f1,f3) = dest_impf form
 val newImpf1 = mk_impf (f1,f2)
 val newTerm1 = mk_sat (tuple,newImpf1)
 val newImpf2 = mk_impf (f2,f3)
 val newTerm2 = mk_sat (tuple,newImpf2)
in
 ([(asl,newTerm1),(asl,newTerm2)], fn [th1,th2] => HS th1 th2)
end

(***************************************************************************** 
ACL_IDEMP_SPEAKS_FOR_TAC 

ACL_IDEMP_SPEAKS_FOR_TAC : (’a*term)−>((’a*term)list*(thm list−>thm))

SYNOPSIS
Proves a goal of the form p speaks for p.

DESCRIPTION
When applied to a goal A ?- (M,Oi,Os) sat p speaks_for p, it will prove the goal.

  A ?- (M,Oi,Os) sat p speaks_for p
 =================================== ACL_IDEMP_SPEAKS_FOR_TAC

FAILURE
Fails unless the goal is an ACL formula of the form p speaks for p.
******************************************************************************)
fun ACL_IDEMP_SPEAKS_FOR_TAC (asl,term) = 
let
 val (tuple,form) = dest_sat term
 val (princ1,princ2) = dest_speaks_for form
 val th1 = IDEMP_SPEAKS_FOR princ1
 val tupleType = type_of tuple
 val (_,[kripketype,_]) = dest_type tupleType
 val (_,[_,btype,_,_,_]) = dest_type kripketype
 val formType = type_of form
 val (_,[proptype,princtype,inttype,sectype]) = dest_type formType
 val th2 = INST_TYPE [``:'a`` |-> proptype, ``:'b`` |-> btype, ``:'d`` |-> inttype, ``:'e`` |-> sectype] th1
in
 ([], fn xs => th2)
end

(***************************************************************************** 
ACL_IL_DOMI_TAC 

ACL_IL_DOMI_TAC : term−>term−>(’a*term)−>((’a*term)list*(thm list−>thm))

SYNOPSIS
Reduces a goal comparing integrity levels of two principals to three subgoals.

DESCRIPTION
When applied to a goal A ?- (M,Oi,Os) sat il q domi il p, integrity levels l2
and l1 it will return 3 subgoals.

  A ?- (M,Oi,Os) sat il q domi il p
 ======================================= ACL_IL_DOMI_TAC l2 l1
  A ?- (M,Oi,Os) sat l2 domi l1
  A ?- (M,Oi,Os) sat il q eqi l2
  A ?- (M,Oi,Os) sat il p eqi l1

FAILURE
Fails unless the goal is an ACL formula of the form il q domi il p.
*****************************************************************************)
fun ACL_IL_DOMI_TAC ilev1 ilev2 (asl,term) =
let
 val (tuple,form) = dest_sat term 
 val formtype = type_of form
 val (ilevprinc1,ilevprinc2) = dest_domi form
 val princ1eq = ``(^ilevprinc1 eqi ^ilev1):^(ty_antiq formtype)``
 val subgoal1 = mk_sat (tuple,princ1eq)
 val princ2eq = ``(^ilevprinc2 eqi ^ilev2):^(ty_antiq formtype)``
 val subgoal2 = mk_sat (tuple,princ2eq)
 val ilevdomi = ``(^ilev1 domi ^ilev2):^(ty_antiq formtype)``
 val subgoal3 = mk_sat (tuple,ilevdomi)
in
 ([(asl,subgoal1),(asl,subgoal2),(asl,subgoal3)], fn [th1,th2,th3] => IL_DOMI th2 th1 th3)
end

(***************************************************************************** 
ACL_MONO_SPEAKS_FOR_TAC 

ACL_MONO_SPEAKS_FOR_TAC : (’a*term)−>((’a*term)list*(thm list−>thm))

SYNOPSIS
Reduces a goal to corresponding speaks f or subgoals.

DESCRIPTION
When applied to a goal A ?- (M,Oi,Os) sat (p quoting q) speaks_for (p’
quoting q’), it will return 2 subgoals.

  A ?- (M,Oi,Os) sat (p quoting q)
           speaks_for (p’ quoting q’)
 ==================================== ACL_MONO_SPEAKS_FOR_TAC
  A ?- (M,Oi,Os) sat p speaks_for p’
  A ?- (M,Oi,Os) sat q speaks_for q’

FAILURE
Fails unless the goal is an ACL formula of the form (p quoting q) speaks for (p’ quoting q’).
*****************************************************************************)
fun ACL_MONO_SPEAKS_FOR_TAC (asl,term) =
let
 val (tuple,form) = dest_sat term
 val formtype = type_of form
 val (quote1,quote2) = dest_speaks_for form
 val (princ1,princ2) = dest_quoting quote1
 val (princ1',princ2') = dest_quoting quote2
 val speaksfor1 = ``(^princ1 speaks_for ^princ1'):^(ty_antiq formtype)``
 val subgoal1 = mk_sat (tuple,speaksfor1)
 val speaksfor2 = ``(^princ2 speaks_for ^princ2'):^(ty_antiq formtype)``
 val subgoal2 = mk_sat (tuple,speaksfor2)
in
 ([(asl,subgoal1),(asl,subgoal2)], fn [th1,th2] => MONO_SPEAKS_FOR th1 th2)
end

(***************************************************************************** 
ACL_MP_SAYS_TAC 

ACL_MP_SAYS_TAC : (’a*term)−>((’a*term)list*(thm list−>thm))

SYNOPSIS
Proves a goal of the form A ?- (M,Oi,Os) sat (p says (f1 impf f2)) impf
((p says f1) impf (p says f2))

DESCRIPTION
It will prove a goal of the following form: A ?- (M,Oi,Os) sat (p says (f1 impf f2)) impf ((p says f1) impf (p says f2)).

  A ?- (M,Oi,Os) sat
      (p says (f1 impf f2)) impf
       ((p says f1) impf (p says f2))
 ======================================= ACL_MP_SAYS_TAC

FAILURE
Fails unless the goal is an ACL formula of the form (p says (f1 impf f2)) impf ((p says f1) impf (p says f2)).
*****************************************************************************)
fun ACL_MP_SAYS_TAC (asl,term) =
let
 val (tuple,form) = dest_sat term
 val (saysterm,_) = dest_impf form
 val (princ,impterm) = dest_says saysterm
 val (f1,f2) = dest_impf impterm
  val tupleType = type_of tuple
 val (_,[kripketype,_]) = dest_type tupleType
 val (_,[_,btype,_,_,_]) = dest_type kripketype
 val th1 = MP_SAYS princ f1 f2
 val th2 = INST_TYPE [``:'b`` |-> btype] th1
in
 ([], fn xs => th2)
end

(***************************************************************************** 
ACL_QUOTING_LR_TAC 

ACL_QUOTING_LR_TAC : (’a*term)−>((’a*term)list*(thm list−>thm))

SYNOPSIS
Reduces a says goal to corresponding quoting subgoal.

DESCRIPTION
When applied to a goal A ?- (M,Oi,Os) sat p says q says f, it will return one
subgoal.

  A ?- (M,Oi,Os) sat p says q says f
 ======================================= ACL_QUOTING_LR_TAC
  A ?- (M,Oi,Os) sat p quoting q says f

FAILURE
Fails unless the goal is an ACL formula of the form p says q says f.
*****************************************************************************)
fun ACL_QUOTING_LR_TAC (asl,term) =
let
 val (tuple,form) = dest_sat term
 val (princ1,saysterm) = dest_says form
 val (princ2,f) = dest_says saysterm
 val quotingterm = mk_quoting (princ1,princ2)
 val newform = mk_says (quotingterm,f)
 val subgoal = mk_sat (tuple,newform)
in
 ([(asl,subgoal)], fn [th] => QUOTING_LR th)
end

(***************************************************************************** 
ACL_QUOTING_RL_TAC 

ACL_QUOTING_RL_TAC : (’a*term)−>((’a*term)list*(thm list−>thm))

SYNOPSIS
Reduces a quoting goal to corresponding says subgoal.

DESCRIPTION
When applied to a goal A ?- (M,Oi,Os) sat p quoting q says f, it will return 1
subgoal.

  A ?- (M,Oi,Os) sat p quoting q says f
 ======================================= ACL_QUOTING_RL_TAC
  A ?- (M,Oi,Os) sat p says q says f

FAILURE
Fails unless the goal is an ACL formula of the form p quoting q says f.
*****************************************************************************)
fun ACL_QUOTING_RL_TAC (asl,term) =
let
 val (tuple,form) = dest_sat term
 val (quotingterm,f) = dest_says form
 val (princ1,princ2) = dest_quoting quotingterm
 val saysterm = mk_says (princ2,f)
 val newform = mk_says (princ1,saysterm)
 val subgoal = mk_sat (tuple,newform)
in
 ([(asl,subgoal)], fn [th] => QUOTING_RL th)
end

(**************************************************************************** 
ACL_REPS_TAC 

ACL_REPS_TAC : term−>term−>(’a*term)−>((’a*term)list*(thm list−>thm))

SYNOPSIS
Reduces a goal to the corresponding reps subgoals.

DESCRIPTION
When applied to principals p, q and a goal A ?- (M,Oi,Os) sat f, it will return 3 subgoals.

  A ?- (M,Oi,Os) sat f
 ======================================== ACL_REPS_TAC p q
  A ?- (M,Oi,Os) sat q controls f
  A ?- (M,Oi,Os) sat p quoting q says f
  A ?- (M,Oi,Os) sat reps p q f

FAILURE
Fails unless the goal is an ACL formula.
****************************************************************************)
fun ACL_REPS_TAC princ1 princ2 (asl,term) =
let
 val (tuple,form) = dest_sat term
 val repterm = mk_reps (princ1,princ2,form)
 val subgoal1 = mk_sat (tuple,repterm)
 val quotingterm = mk_quoting (princ1,princ2)
 val saysterm = mk_says (quotingterm,form)
 val subgoal2 = mk_sat (tuple,saysterm)
 val controlsterm = mk_controls (princ2,form)
 val subgoal3 = mk_sat (tuple,controlsterm)
in
 ([(asl,subgoal1),(asl,subgoal2),(asl,subgoal3)], fn [th1,th2,th3] => REPS th1 th2 th3)
end

(***************************************************************************** 
ACL_REP_SAYS_TAC 

ACL_REP_SAYS_TAC : term−>(’a*term)−>((’a*term)list*(thm list−>thm))

SYNOPSIS
Reduces a says goal to the corresponding reps subgoals.

DESCRIPTION
When applied to principal p and a goal A ?- (M,Oi,Os) sat q says f, it will return two subgoals.

  A ?- (M,Oi,Os) sat q says f
 ======================================== ACL_REP_SAYS_TAC p
  A ?- (M,Oi,Os) sat p quoting q says f
  A ?- (M,Oi,Os) sat reps p q f

FAILURE
Fails unless the goal is an ACL formula in the form of q says f.
*****************************************************************************)
fun ACL_REP_SAYS_TAC princ1 (asl,term) =
let
 val (tuple,form) = dest_sat term
 val (princ2,f) = dest_says form
 val repsterm = mk_reps (princ1,princ2,f)
 val subgoal1 = mk_sat (tuple,repsterm)
 val quotingterm = mk_quoting (princ1,princ2)
 val saysterm = mk_says (quotingterm,f)
 val subgoal2 = mk_sat (tuple,saysterm)
in
 ([(asl,subgoal1),(asl,subgoal2)], fn [th1,th2] => REP_SAYS th1 th2)
end

(***************************************************************************** 
ACL_SAYS_TAC 

ACL_SAYS_TAC : (’a*term)−>((’a*term)list*(thm list−>thm))

SYNOPSIS
Reduces a says goal to the corresponding subgoal.

DESCRIPTION
When applied to a goal A ?- (M,Oi,Os) sat p says f, it will return one subgoal.

  A ?- (M,Oi,Os) sat p says f
 =============================== ACL_SAYS_TAC
  A ?- (M,Oi,Os) sat f

FAILURE
Fails unless the goal is an ACL formula in the form of p says f.
*****************************************************************************)
fun ACL_SAYS_TAC (asl,term) =
let
 val (tuple,form) = dest_sat term
 val (princ,f) = dest_says form
 val subgoal = mk_sat (tuple,f)
in
 ([(asl,subgoal)], fn [th] => SAYS princ th)
end

(***************************************************************************** 
ACL_SPEAKS_FOR_TAC 

ACL_SPEAKS_FOR_TAC : term−>(’a*term)−>((’a*term)list*(thm list−>thm))

SYNOPSIS
Reduces a says goal to the corresponding says and speaks_for subgoals.

DESCRIPTION
When applied to a principal p and a goal A ?- (M,Oi,Os) sat q says f, it will return two subgoals.

  A ?- (M,Oi,Os) sat q says f
 =================================== ACL_SPEAKS_FOR_TAC p
  A ?- (M,Oi,Os) sat p says f
  A ?- (M,Oi,Os) sat p speaks_for q

FAILURE
Fails unless the goal is an ACL formula in the form of p says f.
******************************************************************************)
fun ACL_SPEAKS_FOR_TAC princ2 (asl,term) =
let
 val (tuple,form) = dest_sat term
 val formtype = type_of form
 val (princ1,f) = dest_says form
 val newSpeaksfor = ``(^princ2 speaks_for ^princ1):^(ty_antiq formtype)``
 val newTerm1 = mk_sat (tuple,newSpeaksfor)
  val newSays = mk_says (princ2,f)
 val newTerm2 = mk_sat (tuple,newSays)
in
 ([(asl,newTerm1),(asl,newTerm2)],fn [th1,th2] => SPEAKS_FOR th1 th2)
end

(***************************************************************************** 
ACL_TRANS_SPEAKS_FOR_TAC 

ACL_TRANS_SPEAKS_FOR_TAC : term−>(’a*term)−>((’a*term)list*(thm list−>thm))

SYNOPSIS
Reduces a speaks_for goal to two corresponding speaks_for subgoals, using the transitive property of speaks_for.

DESCRIPTION
When applied to a principal q and a goal A ?- (M,Oi,Os) sat p speaks_for r, it
will return two subgoals.

  A ?- (M,Oi,Os) sat p speaks_for r
 =================================== ACL_TRANS_SPEAKS_FOR_TAC q
  A ?- (M,Oi,Os) sat q speaks_for r
  A ?- (M,Oi,Os) sat p speaks_for q

FAILURE
Fails unless the goal is an ACL formula in the form of p speaks for r.
*****************************************************************************)
fun ACL_TRANS_SPEAKS_FOR_TAC princ2 (asl,term) =
let
 val (tuple,form) = dest_sat term
 val formtype = type_of form
 val (princ1,princ3) = dest_speaks_for form
 val newSpeaksFor1 = ``(^princ1 speaks_for ^princ2):^(ty_antiq formtype)``
 val newTerm1 = mk_sat (tuple,newSpeaksFor1)
 val newSpeaksFor2 = ``(^princ2 speaks_for ^princ3):^(ty_antiq formtype)``
 val newTerm2 = mk_sat (tuple,newSpeaksFor2)
in
 ([(asl,newTerm1),(asl,newTerm2)],fn [th1,th2] => TRANS_SPEAKS_FOR th1 th2)
end


end; (* structure *)
