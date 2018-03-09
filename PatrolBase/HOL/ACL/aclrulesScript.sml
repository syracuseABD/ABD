(* modified by SKC, 11/9/2011
   - added AndSays_Eq
   modified by SKC, 2/19/2009
   - proved all core rules and many derived ones. *)
(* mutilated by lm, 1/24/09  *)
(*=========================================================*)
(* We build the semantic definitions of the access-control logic *)
(*=========================================================*)
(*
load "aclsemanticsTheory";
*)
structure aclrulesScript =
struct

open HolKernel boolLib Parse bossLib;
open pred_setLib pred_setTheory;
open aclfoundationTheory aclsemanticsTheory relationTheory;

val _ = new_theory "aclrules";

(**********
* The definition of M |= f, pronounced "M satisfies f", where M is
* a Kripke structure and f is a formula in the access-control logic.
* We say, M satisfies f, whenever f is true in all worlds of M. This
* relation is denoted by ``M sat f``, as defined below.
**********)
val _ = set_fixity "sat" (Infixr 540);
val sat_def =
    Define
    `(M, Oi, Os) sat f = ((Efn Oi Os M f) = UNIV:('world) set)`;

(*********
* A property of Images
*********)
val world_says =
    store_thm
    ("world_says",
     Term`!M Oi Os P f w.
     w IN Efn Oi Os M (P says f) =
        !v. v IN Jext (jKS M) P w ==> v IN Efn Oi Os M f`,
     REPEAT GEN_TAC THEN REWRITE_TAC [says_def] THEN
     CONV_TAC (LAND_CONV SET_SPEC_CONV) THEN
     REWRITE_TAC [SUBSET_DEF]);

val cond_lemma =
TAC_PROOF(
        ([],``! b t1 t2.(~ (t2:'a= t1:'a))==>
                        ((if b then t1 else t2) = t1) ==> b``),
        REPEAT GEN_TAC THEN
        BOOL_CASES_TAC ``b:bool`` THEN
        REWRITE_TAC []);

val [repPO_iPO_reflexive, repPO_iPO_antisymmetric, repPO_iPO_transitive] =
    CONJUNCTS repPO_iPO_partial_order;

(******
* Properties of sat
******)

val sat_allworld =
store_thm(
        "sat_allworld",
        ``!M f. (M, Oi, Os) sat f = !w. w IN Efn Oi Os M f``,
        REWRITE_TAC [sat_def, UNIV_DEF, IN_DEF] THEN
        CONV_TAC
        (DEPTH_CONV FUN_EQ_CONV THENC DEPTH_CONV BETA_CONV) THEN
        REWRITE_TAC [TT_def, IN_UNIV]);

(******
* Properties of propositions:
******)

val world_T =
    store_thm
    ("world_T",
    ``!M Oi Os w. w IN Efn Oi Os M TT``,
    REWRITE_TAC [TT_def, IN_UNIV]);

val world_F =
    store_thm
    ("world_F",
    ``!M Oi Os w.~ (w IN Efn Oi Os M FF)``,
    REWRITE_TAC [FF_def, NOT_IN_EMPTY]);

val world_not =
    store_thm
    ("world_not",
    ``!M Oi Os f w.w IN Efn Oi Os M (notf f) = ~ (w IN Efn Oi Os M f)``,
    REWRITE_TAC [notf_def, IN_DIFF, IN_UNIV]);

val world_not =
    store_thm
    ("world_not",
    ``!M Oi Os f w.w IN Efn Oi Os M (notf f) = ~ (w IN Efn Oi Os M f)``,
    REWRITE_TAC [notf_def, IN_DIFF, IN_UNIV]);

val world_not =
    store_thm
    ("world_not",
    ``!M Oi Os f w.w IN Efn Oi Os M (notf f) = ~ (w IN Efn Oi Os M f)``,
    REWRITE_TAC [notf_def, IN_DIFF, IN_UNIV]);

val world_and =
    store_thm
    ("world_and",
    ``!M Oi Os f1 f2 w.
    w IN Efn Oi Os M (f1 andf f2) = w IN Efn Oi Os M f1 /\
    w IN Efn Oi Os M f2``,
    REWRITE_TAC [andf_def, IN_INTER]);

val world_or =
    store_thm
    ("world_or",
    ``!M f1 f2 w.
    w IN Efn Oi Os M (f1 orf f2) = w IN Efn Oi Os M f1 \/
    w IN Efn Oi Os M f2``,
    REWRITE_TAC [orf_def, IN_UNION]);

val world_imp =
    store_thm
    ("world_imp",
    ``!M Oi Os f1 f2 w.
    w IN Efn Oi Os M (f1 impf f2) = w IN Efn Oi Os M f1 ==>
    w IN Efn Oi Os M f2``,
    REWRITE_TAC [impf_def, IN_DIFF, IN_UNION, IN_UNIV, IMP_DISJ_THM]);

val world_eq =
    store_thm
    ("world_eq",
    ``!M Oi Os f1 f2 w.
    w IN Efn Oi Os M (f1 eqf f2) = (w IN Efn Oi Os M f1 =
    w IN Efn Oi Os M f2)``,
    REPEAT GEN_TAC
    THEN REWRITE_TAC [eqf_def, IN_DIFF, IN_UNION, IN_INTER, IN_UNIV]
    THEN CONV_TAC (RAND_CONV (REWRITE_CONV [EQ_IMP_THM, IMP_DISJ_THM]))
    THEN REFL_TAC);

val world_eqn =
    store_thm
    ("world_eqn",
     ``!M Oi Os n1 n2 w.
      w IN Efn Oi Os m (n1 eqn n2) = (n1 = n2)``,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [eqn_def] THEN
   COND_CASES_TAC THEN
   REWRITE_TAC [IN_UNIV, NOT_IN_EMPTY]);

val world_lte =
    store_thm
    ("world_lte",
     ``!M Oi Os n1 n2 w.
      w IN Efn Oi Os m (n1 lte n2) = (n1 <= n2)``,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [lte_def] THEN
   COND_CASES_TAC THEN
   REWRITE_TAC [IN_UNIV, NOT_IN_EMPTY]);

val world_lt =
    store_thm
    ("world_lt",
     ``!M Oi Os n1 n2 w.
      w IN Efn Oi Os m (n1 lt n2) = (n1 < n2)``,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [lt_def] THEN
   COND_CASES_TAC THEN
   REWRITE_TAC [IN_UNIV, NOT_IN_EMPTY]);

(**********************************
* INFERENCE RULES
* Our inference rules in the textbook are written as
*
*    H1 ... Hn
*    ------- Rule Name
*        C
*
* Inference rules are theorems:
* !(M:('a IntLabel, 'b SecLabel, 'world) Kripke)
*    (H1:('a IntLabel, 'b SecLabel) Form) .. Hn.
*   M sat H1 ==> M sat H2 ==> ... ==> M sat Hn ==> M sat C
***********************************)



(********************************************************************
* A tactic to prove goals of the form M sat <instance of tautology> *
********************************************************************)
val ACL_TAUT_TAC =
    REWRITE_TAC
    [sat_allworld, world_T, world_F, world_not,
     world_and, world_or, world_imp, world_eq]
    THEN DECIDE_TAC;

(*******************
* reflexivity of domi
*
*    -------------- Reflexivity of domi
*     intL domi intL
*******************)
val domi_reflexive =
store_thm(
        "domi_reflexive",
        ``!M Oi Os l. (M, Oi, Os) sat (l domi l)``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC [sat_def, domi_def, repPO_iPO_partial_order]);

(*******************
* transitivity of domi
*
* intL1 domi intL2    intL2 domi intL3
* -------------------------------- Transitivity of domi
*               intL1 domi intL3
*******************)
val domi_transitive =
store_thm(
        "domi_transitive",
        ``!M Oi Os l1 l2 l3.
            ((M,Oi,Os) sat (l1 domi l2)) ==>
            ((M,Oi,Os) sat (l2 domi l3)) ==>
            ((M,Oi,Os) sat (l1 domi l3))``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC [sat_def, domi_def, repPO_iPO_partial_order] THEN
        REPEAT DISCH_TAC THEN
        IMP_RES_TAC (MATCH_MP cond_lemma EMPTY_NOT_UNIV) THEN
        IMP_RES_TAC repPO_iPO_transitive THEN
        ASM_REWRITE_TAC []);


(**********
* antisymmetry of domi
*
* intL1 domi intL2    intL2 domi intL1
* -------------------------------- Antisymmetry of domi
*               intL1 eqi intL2
**********)
val domi_antisymmetric =
store_thm(
        "domi_antisymmetric",
        ``!M Oi Os l1 l2.
            ((M,Oi,Os) sat (l1 domi l2)) ==>
            ((M,Oi,Os) sat (l2 domi l1)) ==>
            ((M,Oi,Os) sat (l1 eqi l2))``,
            REPEAT GEN_TAC THEN
            REWRITE_TAC [sat_def, domi_def, eqi_def,
                         repPO_iPO_partial_order] THEN
            REPEAT DISCH_TAC THEN
            ASM_REWRITE_TAC [INTER_UNIV]);

(*****************
* eqi_Eq
* (l1 eqi l2) = (l2 domi l1 andf l1 domi l2)
*****************)
val eqi_Eq =
store_thm
   ("eqi_Eq",
    ``!M Oi Os l1 l2.((M,Oi,Os) sat l1 eqi l2) =
                     ((M,Oi,Os) sat (l2 domi l1) andf (l1 domi l2))``,
    REPEAT GEN_TAC THEN
    REWRITE_TAC [sat_def,eqi_domi]);

(*******************
* reflexivity of doms
*
*    -------------- Reflexivity of doms
*     secL doms secL
*******************)
val doms_reflexive =
store_thm(
        "doms_reflexive",
        ``!M Oi Os l. (M,Oi,Os) sat (l doms l)``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC [sat_def, doms_def, repPO_iPO_reflexive]);


(*******************
* transitivity of doms
*
* secL1 doms secL2    secL2 doms secL3
* -------------------------------- Transitivity of doms
*               secL1 doms secL3
*******************)
val doms_transitive =
store_thm(
        "doms_transitive",
        ``!M Oi Os l1 l2 l3.
            ((M,Oi,Os) sat (l1 doms l2)) ==>
            ((M,Oi,Os) sat (l2 doms l3)) ==>
            ((M,Oi,Os) sat (l1 doms l3))``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC [sat_def, doms_def, repPO_iPO_partial_order] THEN
        REPEAT DISCH_TAC THEN
        IMP_RES_TAC (MATCH_MP cond_lemma EMPTY_NOT_UNIV) THEN
        IMP_RES_TAC repPO_iPO_transitive THEN
        ASM_REWRITE_TAC []);

(**********
* antisymmetry of doms
*
* secL1 domi secL2    secL2 domi secL1
* -------------------------------- Antisymmetry of doms
*               secL1 eqs secL2
**********)
val doms_antisymmetric =
store_thm(
        "doms_antisymmetric",
        ``!M Oi Os l1 l2.
            ((M,Oi,Os) sat (l1 doms l2)) ==>
            ((M,Oi,Os) sat (l2 doms l1)) ==>
            ((M,Oi,Os) sat (l1 eqs l2))``,
            REPEAT GEN_TAC THEN
            REWRITE_TAC [sat_def, doms_def, eqs_def,
                         repPO_iPO_partial_order] THEN
            REPEAT DISCH_TAC THEN
            ASM_REWRITE_TAC [INTER_UNIV]);

(*****************
* eqs_Eq
*
* (l1 eqs l2) = (l2 doms l1 andf l1 doms l2)
*****************)
val eqs_Eq =
store_thm
   ("eqs_Eq",
    ``!M Oi Os l1 l2.((M,Oi,Os) sat l1 eqs l2) =
                     ((M,Oi,Os) sat (l2 doms l1) andf (l1 doms l2))``,
    REPEAT GEN_TAC THEN
    REWRITE_TAC [sat_def,eqs_doms]);

(****************************
* Modus Ponens
*
* f1  f1 impf f2
* ------------ Modus Ponens
*        f2
****************************)
val Modus_Ponens =
store_thm(
        "Modus_Ponens",
        ``!M Oi Os f1 f2.
            ((M,Oi,Os) sat f1) ==>
            ((M,Oi,Os) sat (f1 impf f2)) ==>
            ((M,Oi,Os) sat f2)``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC [sat_def, impf_def] THEN
        DISCH_TAC THEN
        ASM_REWRITE_TAC [DIFF_UNIV, UNION_EMPTY]);

(****************************
* Says
*
*         f
* ------------ Says
*    P says f
****************************)
val Says =
store_thm(
        "Says",
        ``!M Oi Os P f.
            ((M,Oi,Os) sat f) ==>
            ((M,Oi,Os) sat (P says f))``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC [sat_def, says_def] THEN
        DISCH_TAC THEN
        ASM_REWRITE_TAC [SUBSET_UNIV, GSPEC_T]);

(***************************
* MP Says
*
*  -------------------------------------------------------
*  P says (f1 impf f2) impf ((P says f1) impf (P says f2))
***************************)
val MP_Says =
    store_thm
    ("MP_Says",
    Term`!M Oi Os P f1 f2.
    (M,Oi,Os) sat ((P says (f1 impf f2)) impf
                            ((P says f1) impf (P says f2)))`,
    REPEAT GEN_TAC THEN
    REWRITE_TAC [sat_allworld, world_says, world_imp] THEN
    REPEAT STRIP_TAC THEN
    RES_TAC);

(***************************
* Speaks For
*
* --------------------------------------------------
* (P speaks_for Q) impf ((P says f) impf (Q says f))
***************************)

(**properties of sets and images **)
val UNIV_DIFF_SUBSET =
store_thm
  ("UNIV_DIFF_SUBSET",
  ``!R1 R2. (R1 SUBSET R2) ==> (((UNIV DIFF R1) UNION R2) = UNIV)``,
  REWRITE_TAC
  [SUBSET_DEF, DIFF_DEF, IN_UNIV, UNION_DEF] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [SPECL [``x IN R1``, ``x IN R2``] IMP_DISJ_THM] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC [GSPEC_T]);

val Image_SUBSET =
store_thm
  ("Image_SUBSET",
   ``!R1 R2.(R2 RSUBSET R1) ==> !w.((R2 w) SUBSET (R1 w))``,
   REWRITE_TAC [RSUBSET, SUBSET_DEF, IN_DEF] THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   PROVE_TAC []);

val SUBSET_Image_SUBSET =
store_thm
  ("SUBSET_Image_SUBSET",
   ``!R1 R2 R3.
   (!w1.((R2 w1) SUBSET (R1 w1))) ==>
   (!w.({w | (R1 w) SUBSET R3} SUBSET {w | (R2 w) SUBSET R3}))``,
   REWRITE_TAC [SUBSET_DEF] THEN
   CONV_TAC(DEPTH_CONV SET_SPEC_CONV) THEN
   PROVE_TAC []);

val speaks_for_SUBSET =
store_thm
  ("speaks_for_SUBSET",
  ``!R3 R2 R1.(R2 RSUBSET R1) ==>
  (!w.({w | (R1 w) SUBSET R3} SUBSET {w | (R2 w) SUBSET R3}))``,
  REPEAT STRIP_TAC THEN
  IMP_RES_TAC Image_SUBSET THEN
  IMP_RES_TAC SUBSET_Image_SUBSET THEN
  ASM_REWRITE_TAC []);

val UNIV_DIFF_SUBSET_lemma =
TAC_PROOF(
   ([],
     ``!M Oi Os P Q f. (Jext (jKS (M :('a, 'b, 'c, 'd, 'e) Kripke))
                       (Q :'c Princ) RSUBSET
        Jext (jKS M) (P :'c Princ)) ==> ((UNIV :'b -> bool) DIFF
       {(w :'b) |
        Jext (jKS (M :('a, 'b, 'c, 'd, 'e) Kripke)) (P :'c Princ) w SUBSET
        Efn (Oi :'d po) (Os :'e po) M (f :('a, 'c, 'd, 'e) Form)} UNION
       {w | Jext (jKS M) (Q :'c Princ) w SUBSET Efn Oi Os M f} =
       (UNIV :'b -> bool))``),
  REPEAT GEN_TAC THEN
  DISCH_THEN
  (fn th =>
    ASSUME_TAC
    (SPEC_ALL
    (MP
     (ISPEC
    ``Jext (jKS (M :('a, 'b, 'c, 'd, 'e) Kripke)) P``
    (ISPEC ``(Jext (jKS (M :('a, 'b, 'c, 'd, 'e) Kripke)) Q)``
    (ISPEC ``Efn (Oi :'d po) (Os :'e po) M (f :('a, 'c, 'd, 'e) Form)``
            speaks_for_SUBSET)))
    th))) THEN
   IMP_RES_TAC
    (ISPEC
    ``{(w:'b) | Jext (jKS M) (Q :'c Princ) w SUBSET Efn Oi Os M f}``
      (ISPEC ``{(w :'b) |
        Jext (jKS (M :('a, 'b, 'c, 'd, 'e) Kripke)) (P :'c Princ) w SUBSET
        Efn (Oi :'d po) (Os :'e po) M (f :('a, 'c, 'd, 'e) Form)}``
      UNIV_DIFF_SUBSET)));

val Speaks_For =
store_thm
   ("Speaks_For",
   ``!M Oi Os P Q f.
   (M,Oi,Os) sat (P speaks_for Q) impf ((P says f) impf (Q says f))``,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [sat_def,says_def, impf_def, speaks_for_def] THEN
   COND_CASES_TAC THEN
   REWRITE_TAC [DIFF_EMPTY,UNION_UNIV, DIFF_UNIV, UNION_EMPTY] THEN
   IMP_RES_TAC UNIV_DIFF_SUBSET_lemma THEN
   ASM_REWRITE_TAC []);

(***************************
* Trans_Speaks_For
*
* P speaks_for Q    Q speaks_for R
* --------------------------------
*          P speaks_for R
***************************)
val RSUBSET_TRANS =
(hd o tl o tl)(CONJUNCTS(REWRITE_RULE
               [WeakOrder, transitive_def] RSUBSET_WeakOrder));

val Trans_Speaks_For =
store_thm
  ("Trans_Speaks_For",
  ``!M Oi Os P Q R.
      ((M,Oi,Os) sat P speaks_for Q) ==>
      ((M,Oi,Os) sat Q speaks_for R) ==>
      ((M,Oi,Os) sat P speaks_for R)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [sat_def, speaks_for_def] THEN
  REPEAT
  (COND_CASES_TAC THEN
   REWRITE_TAC [EMPTY_NOT_UNIV]) THEN
  IMP_RES_TAC RSUBSET_TRANS);

(***************************
* Idemp_Speaks_For
*
* --------------
* P speaks_for P
***************************)

val RSUBSET_REFL =
hd(CONJUNCTS (REWRITE_RULE [WeakOrder, transitive_def,
                            reflexive_def] RSUBSET_WeakOrder));

val Idemp_Speaks_For =
store_thm
  ("Idemp_Speaks_For",
   ``!M Oi Os P. (M,Oi,Os) sat (P speaks_for P)``,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [sat_def, speaks_for_def] THEN
   COND_CASES_TAC THEN
   REWRITE_TAC [EMPTY_NOT_UNIV] THEN
   UNDISCH_TAC
   ``~(Jext (jKS (M :('a, 'b, 'c, 'd, 'e) Kripke)) (P :'c Princ) RSUBSET
     Jext (jKS M) P)``  THEN
   REWRITE_TAC [RSUBSET_REFL]);

(**************************
* Mono_speaks_for
*
*  P speaks_for P'       Q speaks_for Q'
* ---------------------------------------
*(P quoting Q) speaks_for (P' quoting Q')
**************************)

val Mono_speaks_for =
store_thm
  ("Mono_speaks_for",
    ``!M Oi Os P P' Q Q'.
      ((M,Oi,Os) sat (P speaks_for P')) ==>
       ((M,Oi,Os) sat (Q speaks_for Q')) ==>
      ((M,Oi,Os) sat ((P quoting Q) speaks_for (P' quoting Q')))``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
  [sat_def, quoting_def, speaks_for_def, RSUBSET, O_DEF] THEN
  PROVE_TAC []);


(*************************
* And_Says
*
* -----------------------------------------------------
* ((P meet Q) says f) impf ((P says f) andf (Q says f))
**************************)
val Image_UNION =
store_thm
  ("Image_UNION",
   ``!R1 R2 w. (R1 RUNION R2) w = (R1 w) UNION (R2 w) ``,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [RUNION, UNION_DEF, IN_DEF] THEN
   CONV_TAC (DEPTH_CONV (BETA_CONV)) THEN
   REWRITE_TAC [SYM (SPEC_ALL RUNION)] THEN
   REWRITE_TAC[SYM(ISPECL [``(R1 RUNION R2) w``,``x:'b``]
               SPECIFICATION), GSPEC_ID]);

val and_says_lemma =
store_thm
  ("and_says_lemma",
  ``!M Oi Os P Q f. (M,Oi,Os) sat ((P meet Q) says f) impf
                    ((P says f) andf (Q says f))``,
 REPEAT GEN_TAC THEN
 REWRITE_TAC
 [sat_def, meet_def, says_def, impf_def, andf_def,
  Image_UNION, UNION_SUBSET, INTER_DEF] THEN
 CONV_TAC(DEPTH_CONV SET_SPEC_CONV) THEN
 REWRITE_TAC [(SYM (SPEC_ALL COMPL_DEF)),COMPL_CLAUSES]);

val says_and_lemma =
store_thm
  ("says_and_lemma",
  ``!M Oi Os P Q f. (M,Oi,Os) sat ((P says f) andf (Q says f)) impf
                          ((P meet Q) says f)``,
 REPEAT GEN_TAC THEN
 REWRITE_TAC
 [sat_def, meet_def, says_def, impf_def, andf_def,
  Image_UNION, UNION_SUBSET, INTER_DEF] THEN
 CONV_TAC(DEPTH_CONV SET_SPEC_CONV) THEN
 REWRITE_TAC [(SYM (SPEC_ALL COMPL_DEF)),COMPL_CLAUSES]);

val And_Says =
store_thm
  ("And_Says",
   ``!M Oi Os P Q f. (M,Oi,Os) sat ((P meet Q) says f) eqf
                    ((P says f) andf (Q says f))``,
   REPEAT GEN_TAC THEN
   REWRITE_TAC
   [sat_def,eqf_impf,andf_def,
    (REWRITE_RULE[sat_def] and_says_lemma),
    (REWRITE_RULE[sat_def] says_and_lemma),
    INTER_UNIV]);

(******************************
* Quoting
*
* ----------------------------------------------
* ((P meet Q) says f) eqf ((P says f) andf (Q says f))
*
******************************)
(*********************
* Relating eqf and impf
*********************)
val eqf_and_impf =
store_thm
  ("eqf_and_impf",
   ``!M Oi Os f1 f2.
     ((M,Oi,Os) sat (f1 eqf f2)) =
     ((M,Oi,Os) sat ((f1 impf f2) andf (f2 impf f1)))``,
   REWRITE_TAC [sat_def, eqf_impf]);

(*******************
* Relating eqf and (M,Oi,Os) sat
*******************)
val eqf_sat =
store_thm(
   "eqf_sat",
   ``!M Oi Os f1 f2.(M,Oi,Os) sat f1 eqf f2 ==>
                       ((M,Oi,Os) sat f1 = (M,Oi,Os) sat f2)``,
   PROVE_TAC [sat_allworld,world_eq]);

(* -------------------------------------------------------------------------- *)
(* Theorems dealing with equivalence and substitution of terms in             *)
(* the access-control logic                                                   *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* When the intersection of two sets is the universe, then each set is        *)
(* also the universe                                                          *)
(* -------------------------------------------------------------------------- *)

val INTER_EQ_UNIV =
TAC_PROOF(([],``((s:'a set) INTER t = univ(:'a)) = ((s = univ(:'a)) /\ (t = univ(:'a)))``),
PROVE_TAC[(GSYM EQ_UNIV),IN_INTER])

val _ = save_thm("INTER_EQ_UNIV",INTER_EQ_UNIV)

(* -------------------------------------------------------------------------- *)
(* conjunction in ACL related to conjunction in HOL                           *)
(* (M,Oi,Os) sat (f1 andf f2) = (M,Oi,Os) sat f1 /\ (M,Oi,Os) sat f2          *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)

val sat_andf_eq_and_sat =
TAC_PROOF(([],``((M:('a,'b,'c,'d,'e)Kripke),Oi:'d po,Os:'e po) sat (f1 andf f2) = 
 (((M,Oi,Os) sat f1) /\ ((M,Oi,Os) sat f2))``),
REWRITE_TAC[sat_def,world_and,andf_def,INTER_EQ_UNIV])

val _ = save_thm("sat_andf_eq_and_sat",sat_andf_eq_and_sat)

val DIFF_UNIV_SUBSET =
TAC_PROOF(([],``((univ(:'a) DIFF s) UNION t = univ(:'a)) = s SUBSET t``),
REWRITE_TAC[SET_EQ_SUBSET] THEN
REWRITE_TAC[SUBSET_DEF, DIFF_DEF, IN_UNIV, UNION_DEF] THEN
CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
REWRITE_TAC[SPECL [``x IN s``, ``x IN t``] IMP_DISJ_THM])

val _ = save_thm("DIFF_UNIV_SUBSET",DIFF_UNIV_SUBSET)



(* -------------------------------------------------------------------------- *)
(* The key theorem: Efn Oi Os (f1 eqf f2) = univ(:'b) =                       *)
(*                  (Efn Oi Os f1 = Efn Oi Os f2)                             *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)

val eqf_eq_lemma1 =
TAC_PROOF(([],
``((Efn (Oi:'d po) (Os:'e po) (M:('a,'b,'c,'d,'e)Kripke) f1) = 
   (Efn (Oi:'d po) (Os:'e po) (M:('a,'b,'c,'d,'e)Kripke) f2)) ==>
  ((Efn Oi Os M (f1 eqf f2)) = univ(:'b))``),
REWRITE_TAC[eqf_def] THEN
DISCH_THEN (fn th => REWRITE_TAC[th,INTER_IDEMPOT,(MATCH_MP UNION_DIFF (SPEC_ALL SUBSET_UNIV))]))

val eqf_eq_lemma2 =
TAC_PROOF(
([],
``((Efn Oi Os M (f1 eqf f2)) = univ(:'b)) ==>
  ((Efn (Oi:'d po) (Os:'e po) (M:('a,'b,'c,'d,'e)Kripke) f1) = 
   (Efn (Oi:'d po) (Os:'e po) (M:('a,'b,'c,'d,'e)Kripke) f2))``),
REWRITE_TAC[eqf_def,INTER_EQ_UNIV,DIFF_UNIV_SUBSET,GSYM SET_EQ_SUBSET])

val eqf_eq = save_thm("eqf_eq",IMP_ANTISYM_RULE eqf_eq_lemma2 eqf_eq_lemma1)



(* -------------------------------------------------------------------------- *)
(* Equivalence and substitution over negation                                 *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
val eqf_notf =
TAC_PROOF
(([],
``!M Oi Os f f'.
  ((M:('a,'b,'c,'d,'e)Kripke),Oi:'d po,Os:'e po) sat (f eqf f') ==> (M,Oi,Os) sat (notf f) ==>
  (M,Oi,Os) sat (notf f')``),
REPEAT GEN_TAC THEN
REWRITE_TAC[sat_def,notf_def,eqf_eq] THEN
DISCH_THEN (fn th => REWRITE_TAC[th]))

val _ = save_thm("eqf_notf",eqf_notf)



(* -------------------------------------------------------------------------- *)
(* Equivalence and substitution over conjunction                              *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
val eqf_andf1 =
TAC_PROOF
(([],
``!M Oi Os f f' g.
  ((M:('a,'b,'c,'d,'e)Kripke),Oi:'d po,Os:'e po) sat (f eqf f') ==> (M,Oi,Os) sat (f andf g) ==>
  (M,Oi,Os) sat (f' andf g)``),
REPEAT GEN_TAC THEN
REWRITE_TAC[sat_def,andf_def,eqf_eq] THEN
DISCH_THEN (fn th => REWRITE_TAC[th]))

val _ = save_thm("eqf_andf1",eqf_andf1)

val eqf_andf2 =
TAC_PROOF
(([],
``!M Oi Os f f' g.
  ((M:('a,'b,'c,'d,'e)Kripke),Oi:'d po,Os:'e po) sat (f eqf f') ==> (M,Oi,Os) sat (g andf f) ==>
  (M,Oi,Os) sat (g andf f')``),
REPEAT GEN_TAC THEN
REWRITE_TAC[sat_def,andf_def,eqf_eq] THEN
DISCH_THEN (fn th => REWRITE_TAC[th]))

val _ = save_thm("eqf_andf2",eqf_andf2)



(* -------------------------------------------------------------------------- *)
(* Equivalence and substitution over disjunction                              *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
val eqf_orf1 =
TAC_PROOF
(([],
``!M Oi Os f f' g.
  ((M:('a,'b,'c,'d,'e)Kripke),Oi:'d po,Os:'e po) sat (f eqf f') ==> (M,Oi,Os) sat (f orf g) ==>
  (M,Oi,Os) sat (f' orf g)``),
REPEAT GEN_TAC THEN
REWRITE_TAC[sat_def,orf_def,eqf_eq] THEN
DISCH_THEN (fn th => REWRITE_TAC[th]))

val _ = save_thm("eqf_orf1",eqf_orf1)

val eqf_orf2 =
TAC_PROOF
(([],
``!M Oi Os f f' g.
  ((M:('a,'b,'c,'d,'e)Kripke),Oi:'d po,Os:'e po) sat (f eqf f') ==> (M,Oi,Os) sat (g orf f) ==>
  (M,Oi,Os) sat (g orf f')``),
REPEAT GEN_TAC THEN
REWRITE_TAC[sat_def,orf_def,eqf_eq] THEN
DISCH_THEN (fn th => REWRITE_TAC[th]))

val _ = save_thm("eqf_orf2",eqf_orf2)

(* -------------------------------------------------------------------------- *)
(* Equivalence and substitution over implication                              *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
val eqf_impf1 =
TAC_PROOF
(([],
``!M Oi Os f f' g.
  ((M:('a,'b,'c,'d,'e)Kripke),Oi:'d po,Os:'e po) sat (f eqf f') ==> (M,Oi,Os) sat (f impf g) ==>
  (M,Oi,Os) sat (f' impf g)``),
REPEAT GEN_TAC THEN
REWRITE_TAC[sat_def,impf_def,eqf_eq] THEN
DISCH_THEN (fn th => REWRITE_TAC[th]))

val _ = save_thm("eqf_impf1",eqf_impf1)

val eqf_impf2 =
TAC_PROOF
(([],
``!M Oi Os f f' g.
  ((M:('a,'b,'c,'d,'e)Kripke),Oi:'d po,Os:'e po) sat (f eqf f') ==> (M,Oi,Os) sat (g impf f) ==>
  (M,Oi,Os) sat (g impf f')``),
REPEAT GEN_TAC THEN
REWRITE_TAC[sat_def,impf_def,eqf_eq] THEN
DISCH_THEN (fn th => REWRITE_TAC[th]))

val _ = save_thm("eqf_impf2",eqf_impf2)



(* -------------------------------------------------------------------------- *)
(* Equivalence and substitution over equivalence                              *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
val eqf_eqf1 =
TAC_PROOF
(([],
``!M Oi Os f f' g.
  ((M:('a,'b,'c,'d,'e)Kripke),Oi:'d po,Os:'e po) sat (f eqf f') ==> (M,Oi,Os) sat (f eqf g) ==>
  (M,Oi,Os) sat (f' eqf g)``),
REPEAT GEN_TAC THEN
REWRITE_TAC[sat_def,eqf_def,eqf_eq] THEN
DISCH_THEN (fn th => REWRITE_TAC[th]))

val _ = save_thm("eqf_eqf1",eqf_eqf1)

val eqf_eqf2 =
TAC_PROOF
(([],
``!M Oi Os f f' g.
  ((M:('a,'b,'c,'d,'e)Kripke),Oi:'d po,Os:'e po) sat (f eqf f') ==> (M,Oi,Os) sat (g eqf f) ==>
  (M,Oi,Os) sat (g eqf f')``),
REPEAT GEN_TAC THEN
REWRITE_TAC[sat_def,eqf_def,eqf_eq] THEN
DISCH_THEN (fn th => REWRITE_TAC[th]))

val _ = save_thm("eqf_eqf2",eqf_eqf2)

(* -------------------------------------------------------------------------- *)
(* Equivalence and substitution over says                                     *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
val eqf_says =
TAC_PROOF
(([],
``!M Oi Os P f f'.
  ((M:('a,'b,'c,'d,'e)Kripke),Oi:'d po,Os:'e po) sat (f eqf f') ==> (M,Oi,Os) sat (P says f) ==>
  (M,Oi,Os) sat (P says f')``),
REPEAT GEN_TAC THEN
REWRITE_TAC[sat_def,says_def,eqf_eq] THEN
DISCH_THEN (fn th => REWRITE_TAC[th]))

val _ = save_thm("eqf_says",eqf_says)


(* -------------------------------------------------------------------------- *)
(* Equivalence and substituion over controls                                  *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
val eqf_controls =
TAC_PROOF
(([],
``!M Oi Os P f f'.
  ((M:('a,'b,'c,'d,'e)Kripke),Oi:'d po,Os:'e po) sat (f eqf f') ==> (M,Oi,Os) sat (P controls f) ==>
  (M,Oi,Os) sat (P controls f')``),
REPEAT GEN_TAC THEN
REWRITE_TAC[sat_def,controls_def,eqf_eq] THEN
DISCH_THEN (fn th => REWRITE_TAC[th]))

val _ = save_thm("eqf_controls",eqf_controls)


(* -------------------------------------------------------------------------- *)
(* Equivalence and substitution over reps                                     *)
(*                                                                            *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
val eqf_reps =
TAC_PROOF
(([],
``!M Oi Os P Q f f'.
  ((M:('a,'b,'c,'d,'e)Kripke),Oi:'d po,Os:'e po) sat (f eqf f') ==> (M,Oi,Os) sat (reps P Q f) ==>
  (M,Oi,Os) sat (reps P Q f')``),
REPEAT GEN_TAC THEN
REWRITE_TAC[sat_def,reps_def,eqf_eq] THEN
DISCH_THEN (fn th => REWRITE_TAC[th]))

val _ = save_thm("eqf_reps",eqf_reps)

(**********
* Property of cmp
**********)

val Image_cmp =
store_thm
  ("Image_cmp",
  ``!R1 R2 R3:'k->bool u:'g.(((R1 O R2) u) SUBSET R3) =
    ((R2 u) SUBSET {y:'h | (R1 y) SUBSET R3})``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [SUBSET_DEF] THEN
  CONV_TAC (LAND_CONV (REWRITE_CONV [SPECIFICATION])) THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  REWRITE_TAC [O_DEF, SPECIFICATION] THEN
  EQ_TAC THENL
  [STRIP_GOAL_THEN (fn axi => REPEAT STRIP_TAC THEN MATCH_MP_TAC axi)
   THEN EXISTS_TAC (Term`x:'h`) THEN ASM_REWRITE_TAC []
  ,REPEAT STRIP_TAC THEN RES_TAC
  ]);

val Image_lemma =
TAC_PROOF(
  ([],
  ``~(!(x' :'b).
            Jext (jKS (M :('a, 'b, 'c, 'd, 'e) Kripke)) (P :'c Princ) x
              x' ==>
            !(x :'b).
              Jext (jKS M) (Q :'c Princ) x' x ==>
              Efn (Oi :'d po) (Os :'e po) M (f :('a, 'c, 'd, 'e) Form) x)
        \/
        !(x' :'b).
          Jext (jKS M) P x x' ==>
          !(x :'b). Jext (jKS M) Q x' x ==> Efn Oi Os M f x``),
 PROVE_TAC []);

val Quoting =
store_thm
   ("Quoting",
   ``!M Oi Os P Q f.(M,Oi,Os) sat ((P quoting Q) says f) eqf
                                             (P says (Q says f))``,
   REPEAT GEN_TAC THEN
   REWRITE_TAC
   [eqf_and_impf, sat_def, andf_def, INTER_DEF, Efn_def,
    quoting_def, Image_cmp] THEN
   REWRITE_TAC [DIFF_DEF, IN_UNIV, SUBSET_DEF, UNION_DEF] THEN
   CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
   REWRITE_TAC [IN_DEF] THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [Image_lemma, GSPEC_T]);


(******************************
* Quoting_Eq
*
* P quoting Q says f = P says Q says f
******************************)
val Quoting_Eq =
store_thm
   ("Quoting_Eq",
   ``!M Oi Os P Q f. ((M,Oi,Os) sat P quoting Q says f) =
                     ((M,Oi,Os) sat P says Q says f)``,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [sat_def, Efn_def, quoting_def, Image_cmp]);

(*****************************
* Controls_Eq
*
* P controls f = (P says f) impf f
*
*****************************)

val Controls_Eq =
store_thm
  ("Controls_Eq",
  ``!M Oi Os P f. (M,Oi,Os) sat (P controls f) =
                  (M,Oi,Os) sat ((P says f) impf f)``,
  PROVE_TAC [sat_def, controls_says]);

(*****************************
*Reps_Eq
*
* reps P Q f = (P quoting Q) says f impf (Q says f)
*
*****************************)
val reps_def_lemma =
store_thm
   ("reps_def_lemma",
   ``!M Oi Os P Q f. Efn Oi Os M (reps P Q f) =
       Efn Oi Os M ((P quoting Q) says f impf (Q says f))``,
   REWRITE_TAC [reps_def, says_def, impf_def]);

val Reps_Eq =
store_thm
   ("Reps_Eq",
    ``!M Oi Os P Q f. (M,Oi,Os) sat (reps P Q f) =
           (M,Oi,Os) sat ((P quoting Q) says f impf (Q says f))``,
    PROVE_TAC [sat_def, reps_def_lemma]);

(****************************
*
* And_Says_Eq
*
*****************************)
val And_Says_Eq =
let
 val th1 = 
 SPECL 
 [``(M :('a, 'b, 'c, 'd, 'e) Kripke)``, ``(Oi :'d po)``, ``(Os :'e po)``,
  ``(P meet Q says f):('a,'c,'d,'e)Form``,``(P says f andf Q says f):('a,'c,'d,'e)Form``] eqf_sat;
 val th2 = SPEC_ALL  And_Says
in
 MP th1 th2
end;

val _ = save_thm("And_Says_Eq",And_Says_Eq);



(* -------------------------------------------------------------------------- *)
(* (M,Oi,Os) sat TT                                                           *)
(* -------------------------------------------------------------------------- *)
val sat_TT =
TAC_PROOF(([],``(M,Oi,Os) sat TT``),
REWRITE_TAC[sat_def,TT_def])

val _ = save_thm("sat_TT",sat_TT)

val _ = print_theory "-";
val _ = export_theory ();

end;

