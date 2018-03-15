(* added semantics of arithmetic expressions, Aexp, 2/12/2009 *)
(* mutilated by lm, 1/24/09, and eqp removed 1/29/09 *)
(*=========================================================*)
(* We build the semantic definitions of the access-control logic *)
(*=========================================================*)
(*
load "aclfoundationTheory";
*)
structure aclsemanticsScript =
struct

open HolKernel boolLib Parse bossLib;
open aclfoundationTheory relationTheory;

val _ = new_theory "aclsemantics";

(****************************************************************
* Define the extended mapping Jext that maps principal expressions
* Princ to a relation on 'ws. It is parameterized on
* J:PName -> ('w -> 'w set).
*****************************************************************)
val Jext_def =
    Define
    `(Jext (J:'pn -> 'w ->'w set) (Name s) = J s) /\
     (Jext J (P1 meet P2) = ((Jext J P1) RUNION (Jext J P2))) /\
     (Jext J (P1 quoting P2) = (Jext J P2) O (Jext J P1))`;

val Jext_names = ["name_def", "meet_def", "quoting_def"];
val _ = map2 (fn x=>fn y=>save_thm(x,y)) Jext_names (CONJUNCTS Jext_def);

(****************************************************************
* Define the mapping from IntLevel to integrity levels at the
* semantic level. This function is Lifn.
****************************************************************)
val Lifn_def =
    Define
    `(Lifn M (iLab l) = l) /\
     (Lifn M (il name) = imapKS M name)`;

(****************************************************************
* Define the mapping from SecLevel to security levels at the
* semantic level. This function is Lsfn.
****************************************************************)
val Lsfn_def =
    Define
    `(Lsfn M (sLab l) = l) /\
     (Lsfn M (sl name) = smapKS M name)`;

(****************************************************************
* Define the semantic meaning function Efn. Efn is parameterized
* on partial orders Oi for integrity levels and Os for security levels
* and on Kripke structure
*                             KS Intrp Jfn imap smap
*
* UNIV:('w)set corresponds to W in the Kripke structure described
* in our book. UNIV is non-empty, as every type in HOL has at least
* one member.
****************************************************************)
val Efn_def =
    Define
    `(Efn (Oi:'il po) (Os:'is po) (M:('w,'v,'pn,'il,'is) Kripke)
                  TT = UNIV) /\
     (Efn Oi Os M FF = {}) /\
     (Efn Oi Os M (prop p) = ((intpKS M) p)) /\
     (Efn Oi Os M (notf f) = (UNIV DIFF (Efn Oi Os M f))) /\
     (Efn Oi Os M (f1 andf f2) =
           ((Efn Oi Os M f1) INTER (Efn Oi Os M f2))) /\
     (Efn Oi Os M (f1 orf f2) =
           ((Efn Oi Os M f1) UNION (Efn Oi Os M f2))) /\
     (Efn Oi Os M (f1 impf f2) =
           ((UNIV DIFF (Efn Oi Os M f1)) UNION (Efn Oi Os M f2)))  /\
     (Efn Oi Os M (f1 eqf f2) =
           ((UNIV DIFF (Efn Oi Os M f1) UNION (Efn Oi Os M f2)) INTER
            (UNIV DIFF (Efn Oi Os M f2) UNION (Efn Oi Os M  f1)))) /\
     (Efn Oi Os M(P says f) =
           {w | Jext (jKS M) P w SUBSET (Efn Oi Os M f)}) /\
     (Efn Oi Os M (P speaks_for Q) =
           (if ((Jext (jKS M) Q) RSUBSET (Jext (jKS M) P)) then UNIV else
           {})) /\
     (Efn Oi Os M(P controls f) =
           ((UNIV DIFF
           ({w | Jext (jKS M) P w SUBSET Efn Oi Os M f})) UNION
            (Efn Oi Os M f)))  /\
     (Efn Oi Os M (reps P Q f) =
           ((UNIV DIFF
           ({w | Jext (jKS M) (P quoting Q) w SUBSET
                 Efn Oi Os M f})) UNION
            {w | Jext (jKS M) Q w SUBSET Efn Oi Os M f})) /\
     (Efn Oi Os M (intl1 domi intl2) = (* note inversion 3/12/09 *)
           (if repPO Oi (Lifn M intl2) (Lifn M intl1)
           then UNIV else {})) /\
     (Efn Oi Os M (intl2 eqi intl1) = (* ** note inversion 7/30/09 ** *)
           (if repPO Oi (Lifn M intl2) (Lifn M intl1)
           then UNIV else {}) INTER
           (if repPO Oi (Lifn M intl1) (Lifn M intl2)
           then UNIV else {})) /\
     (Efn Oi Os M (secl1 doms secl2) = (* note inversion *)
           (if repPO Os (Lsfn M secl2) (Lsfn M secl1)
           then UNIV else {})) /\
     (Efn Oi Os M (secl2 eqs secl1) = (* ** note inversion ** *)
           (if repPO Os (Lsfn M secl2) (Lsfn M secl1)
           then UNIV else {}) INTER
           (if repPO Os (Lsfn M secl1) (Lsfn M secl2)
           then UNIV else {})) /\
     (Efn Oi Os M ((numExp1:num) eqn (numExp2:num)) =
           (if (numExp1 = numExp2)
            then UNIV else {})) /\
     (Efn Oi Os M ((numExp1:num) lte (numExp2:num)) =
           (if (numExp1 <= numExp2)
            then UNIV else {})) /\
     (Efn Oi Os M ((numExp1:num) lt (numExp2:num)) =
           (if (numExp1 < numExp2)
            then UNIV else {}))`;


(**********
* save each definition of Efn individually
**********)

val Efn_names = ["TT_def", "FF_def", "prop_def", "notf_def", "andf_def",
                 "orf_def", "impf_def", "eqf_def", "says_def",
                 "speaks_for_def", "controls_def", "reps_def",
                 "domi_def", "eqi_def", "doms_def", "eqs_def", "eqn_def", "lte_def", "lt_def"];

val _ = map2 (fn x => fn y => save_thm(x,y)) Efn_names (CONJUNCTS Efn_def);

(**************************
* Syntactic Sugar Properties
* This is to make sure that what we've defined here
* matches what we have in the textbook.
**************************)

(**********
* Fetch the individual theorems needed
**********)
val eqf_def = DB.fetch "aclsemantics" "eqf_def";
val andf_def = DB.fetch "aclsemantics" "andf_def";
val impf_def = DB.fetch "aclsemantics" "impf_def";
val controls_def = DB.fetch "aclsemantics" "controls_def";
val says_def = DB.fetch "aclsemantics" "says_def";
val eqi_def = DB.fetch "aclsemantics" "eqi_def";
val domi_def = DB.fetch "aclsemantics" "domi_def";
val eqs_def = DB.fetch "aclsemantics" "eqs_def";
val doms_def = DB.fetch "aclsemantics" "doms_def";

val eqf_impf =
store_thm(
        "eqf_impf",
        ``!M f1 f2.
        Efn Oi Os M (f1 eqf f2) =
        Efn Oi Os M((f1 impf f2) andf (f2 impf f1))``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC [eqf_def, andf_def, impf_def]);

val controls_says =
store_thm(
        "controls_says",
        ``!M P f.
        Efn Oi Os M (P controls f) =
        Efn Oi Os M ((P says f) impf f)``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC [controls_def, impf_def, says_def]);

val eqi_domi =
store_thm(
        "eqi_domi",
        ``!M intL1 intL2.
        Efn Oi Os M (intL1 eqi intL2) =
        Efn Oi Os M ((intL2 domi intL1) andf (intL1 domi intL2))``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC [eqi_def,andf_def,domi_def]);

val eqs_doms =
store_thm(
        "eqs_doms",
        ``!M secL1 secL2.
        Efn Oi Os M (secL1 eqs secL2) =
        Efn Oi Os M ((secL2 doms secL1) andf (secL1 doms secL2))``,
        REPEAT GEN_TAC THEN
        REWRITE_TAC [eqs_def,andf_def,doms_def]);

(********************
* Export the theory
********************)
val _ = print_theory "-";
val _ = export_theory();

end;

