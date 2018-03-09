(* Created by SKC 2/19/2009. *)
(* These are derived rules. *)

(* Interactive mode
set_trace "Unicode" 0;
app load ["pred_setTheory", "pred_setLib", "relationTheory", "aclfoundationTheory",
          "aclsemanticsTheory", "aclrulesTheory"];
*)

structure aclDrulesScript = struct

open HolKernel boolLib Parse;
open bossLib 
open pred_setLib pred_setTheory relationTheory;
open aclfoundationTheory aclsemanticsTheory aclrulesTheory;

val _ = new_theory "aclDrules";

(****************************
* Simplification1          Simplification2
*
*  f1 andf f2                 f1 andf f2
*  ---------                 ---------
*       f1                           f2
****************************)
(*****Proof of INTER_EQ_UNIV thanks to Lockwood Morris***********)
(*      It's much shorter than my original version below!                   *)
val INTER_EQ_UNIV = 
store_thm 
  ("INTER_EQ_UNIV", 
   Term `!s1 s2:'a -> bool. (s1 INTER s2 = UNIV) = (s1 = UNIV) /\ (s2 = UNIV)`,
   REPEAT GEN_TAC
   THEN REWRITE_TAC [EXTENSION, IN_INTER, IN_UNIV]
   THEN CONV_TAC (RAND_CONV AND_FORALL_CONV) THEN REFL_TAC);

(********** Old proof of INTER_EQ_UNIV  
val INTER_EQ_UNIV_lemma1 =
TAC_PROOF(
   ([],``!s1 s2.(s1 INTER s2 = UNIV) ==> ((s1 = UNIV) /\ (s2 = UNIV))``),
  REPEAT GEN_TAC THEN
  REWRITE_TAC [UNIV_DEF, INTER_DEF,IN_DEF,(REWRITE_RULE [SPECIFICATION] EXTENSION)] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC [SYM(SPEC_ALL FORALL_AND_THM)] THEN
  DISCH_TAC THEN
  GEN_TAC THEN
  UNDISCH_TAC ``!(x :'a). {x | (s1 :'a -> bool) x /\ (s2 :'a -> bool) x} x`` THEN
  DISCH_THEN 
  (fn th => 
       MP_TAC 
       (SUBS 
        [SYM(SPECL [``{(x :'a) | (s1 :'a -> bool) x /\ (s2 :'a -> bool) x}``, ``x``] SPECIFICATION)] 
	(SPEC_ALL th))) THEN
  REWRITE_TAC [SET_SPEC_CONV ``(x :'a) IN {x | (s1 :'a -> bool) x /\ (s2 :'a -> bool) x}``]);

val INTER_EQ_UNIV_lemma2 =
TAC_PROOF(
  ([],``!s1 s2.((s1 = UNIV) /\ (s2 = UNIV)) ==> (s1 INTER s2 = UNIV)``),
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC [INTER_UNIV]);

val INTER_EQ_UNIV =
store_thm
 ("INTER_EQ_UNIV",``!s1 s2.(s1 INTER s2 = UNIV) = ((s1 = UNIV) /\ (s2 = UNIV))``,
  REPEAT GEN_TAC THEN
  EQ_TAC THEN
  REWRITE_TAC [INTER_EQ_UNIV_lemma1, INTER_EQ_UNIV_lemma2]);
***************old proof of INTER_EQ_UNIV************)

val Simplification1 =
store_thm
   ("Simplification1",
   ``!M Oi Os f1 f2. ((M,Oi,Os) sat (f1 andf f2)) ==> ((M,Oi,Os) sat f1)``,
  REPEAT GEN_TAC THEN
  PROVE_TAC [sat_def, Efn_def, INTER_EQ_UNIV]);

val Simplification2 =
store_thm
   ("Simplification2",
   ``!M Oi Os f1 f2. ((M,Oi,Os) sat (f1 andf f2)) ==> ((M,Oi,Os) sat f2)``,
  REPEAT GEN_TAC THEN
  PROVE_TAC [sat_def, Efn_def, INTER_EQ_UNIV]);


(********ACL INFERENCE RULES FOR HOL*******************************)
(* These reduce the need for dealing with (M,Oi,Os) sat                         *)
(********************************************************************)
val ACL_TAUT_TAC =
    REWRITE_TAC 
    [sat_allworld, world_T, world_F, world_not, 
     world_and, world_or, world_imp, world_eq,
     world_eqn, world_lte, world_lt]
    THEN DECIDE_TAC;
fun ACL_TAUT f =
    TAC_PROOF(([],(Term `(M,Oi,Os) sat ^f`)),
    ACL_TAUT_TAC);
fun ACL_ASSUM f = ASSUME (Term `(M,Oi,Os) sat ^f`);
fun ACL_MP th1 th2 = MATCH_MP (MATCH_MP (SPEC_ALL Modus_Ponens) th1) th2;
fun ACL_SIMP1 th = MATCH_MP Simplification1 th;
fun ACL_SIMP2 th = MATCH_MP Simplification2 th;


(****************************
* Controls
*
* P controls f    P says f
*----------------------
*              f
****************************)
val Controls =
let
	val a1 = ACL_ASSUM ``(P:'c Princ) controls (f:('a,'c,'d,'e)Form)``
	val a2 = ACL_ASSUM ``(P:'c Princ) says (f:('a,'c,'d,'e)Form)``
	val th3 = REWRITE_RULE [Controls_Eq] a1
	val th4 = ACL_MP a2 th3
	val th5 = 
	 GENL [``(M :('a, 'b, 'c, 'd, 'e) Kripke)``,``(Oi :'d po)``,``(Os :'e po)``,
	         ``(P :'c Princ)``,``(f :('a, 'c, 'd, 'e) Form)``]
		 (DISCH_ALL th4)
in
	save_thm("Controls",th5)
end;


(********ACL INFERENCE RULES FOR HOL*******************************)
(* These reduce the need for dealing with (M,Oi,Os) sat                         *)
(********************************************************************)
fun CONTROLS th1 th2 = MATCH_MP (MATCH_MP Controls th2) th1;

(*****************************
* Reps
*
*  Q controls f    reps P Q f    P quoting Q says f
*   --------------------------------------------
*                                  f
*****************************)
val Reps = 
let
	val a1 = ACL_ASSUM ``(Q:'c Princ) controls (f:('a,'c,'d,'e)Form) ``
	val a2 = ACL_ASSUM ``reps (P:'c Princ) (Q:'c Princ) (f:('a,'c,'d,'e)Form)``
	val a3 = ACL_ASSUM ``((P:'c Princ) quoting (Q:'c Princ)) says (f:('a,'c,'d,'e)Form)``
	val th4 = REWRITE_RULE [Reps_Eq] a2
	val th5 = ACL_MP a3 th4
	val th6 = REWRITE_RULE [Controls_Eq] a1
	val th7 = ACL_MP th5 th6
	val th8 = GENL [``(M :('a, 'b, 'c, 'd, 'e) Kripke)``,``(Oi :'d po)``,``(Os :'e po)``,
	               	     ``(P :'c Princ)``,``(Q: 'c Princ)``,``(f :('a, 'c, 'd, 'e) Form)``]
		      	     (DISCH_ALL th7)
in
	save_thm("Reps",th8)
end;

(****************************
* Rep_Controls_eq
*
*-------------------------------
* reps A B f = A controls (B says f)
****************************)

val Rep_Controls_Eq =
store_thm
   ("Rep_Controls_Eq",
   ``!M Oi Os (A:'c Princ) B (f:('a,'c,'d,'e)Form).
     ((M,Oi,Os) sat reps A B f) = ((M,Oi,Os) sat (A controls (B says f)))``,
   REWRITE_TAC [Reps_Eq, Controls_Eq, sat_def,Efn_def, quoting_def, Image_cmp]);

(****************************
* Rep_Says
*
* rep A B f    A quoting B says f
*----------------------------
*             B says f
****************************)
val Rep_Says =
let
	val a1 = ACL_ASSUM ``reps (P:'c Princ) (Q:'c Princ) (f:('a,'c,'d,'e)Form)``
	val a2 = ACL_ASSUM ``(P:'c Princ) quoting (Q:'c Princ) says (f:('a,'c,'d,'e)Form)``
	val th3 = REWRITE_RULE [Rep_Controls_Eq] a1
	val th4 = REWRITE_RULE [Quoting_Eq] a2
	val th5 = CONTROLS th3 th4
	val th6 = GENL [``(M :('a, 'b, 'c, 'd, 'e) Kripke)``,``(Oi :'d po)``,``(Os :'e po)``,
	               	     ``(P :'c Princ)``,``(Q: 'c Princ)``,``(f :('a, 'c, 'd, 'e) Form)``]
			     (DISCH (hd (hyp a1)) (DISCH (hd (hyp a2)) th5))
in
	save_thm("Rep_Says",th6)
end;

(***************************************
* Conjunction
*
*    f1   f2
*  ---------
*  f1 andf f2
***************************************)
val Conjunction = 
store_thm
   ("Conjunction",
    ``!M Oi Os f1 f2.(M,Oi,Os) sat f1 ==> (M,Oi,Os) sat f2 ==> (M,Oi,Os) sat (f1 andf f2)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [sat_def,world_and,andf_def] THEN
  REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC [INTER_EQ_UNIV]);

(***************************************
* Disjunction1
*
*      f1
*  ---------
*  f1 orf f2
***************************************)
val Disjunction1 = 
store_thm
  ("Disjunction1",
   ``!M Oi Os f1 f2.(M,Oi,Os) sat f1 ==> (M,Oi,Os) sat f1 orf f2``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [sat_def,world_or,orf_def] THEN
  REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC [UNION_UNIV]);

(***************************************
* Disjunction2
*
*      f2
*  ---------
*  f1 orf f2
***************************************)
val Disjunction2 = 
store_thm
  ("Disjunction2",
   ``!M Oi Os f1 f2.(M,Oi,Os) sat f2 ==> (M,Oi,Os) sat f1 orf f2``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [sat_def,world_or,orf_def] THEN
  REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC [UNION_UNIV]);

(***************************************
* Modus Tollens
*
*  f1 impf f2   notf f2
*  -----------------
*          notf f1
***************************************)
val Modus_Tollens =
let 
    val th1 = ACL_ASSUM ``(f1:('a,'c,'d,'e)Form) impf (f2:('a,'c,'d,'e)Form)``
    val th2 = ACL_ASSUM ``notf (f2:('a,'c,'d,'e)Form)``
    val th3 = ACL_TAUT ``(f1:('a,'c,'d,'e)Form) impf (f2:('a,'c,'d,'e)Form) eqf (notf f2 impf notf f1)``
    val th4 = REWRITE_RULE [eqf_and_impf] th3
    val th5 = ACL_SIMP1 th4
    val th6 = ACL_MP th1 th5
    val th7 = ACL_MP th2 th6
    val th8 = GENL 
    	[``(M :('a, 'b, 'c, 'd, 'e) Kripke)``,``(Oi :'d po)``,``(Os :'e po)``,
     	``(f1 :('a,'c, 'd,'e) Form)``,``(f2 :('a, 'c, 'd, 'e) Form)``] 
     	(DISCH_ALL th7)
in
   save_thm("Modus_Tollens",th8)
end;

(***************************************
* Double Negation
*
*   notf (notf f)
*  -------------
*          f
***************************************)
val Double_Negation =
let
val th1 = ACL_ASSUM ``notf (notf (f:('a,'c,'d,'e)Form))``
val th2 = ACL_TAUT ``(notf(notf (f:('a,'c,'d,'e)Form))) eqf (f:('a,'c,'d,'e)Form)``
val th3 = MATCH_MP eqf_sat th2
val th4 = REWRITE_RULE [th3] th1
val th5 = 
 GENL 
 [``(M :('a, 'b, 'c, 'd, 'e) Kripke)``,``(Oi :'d po)``,``(Os :'e po)``,
  ``(f :('a, 'c, 'd, 'e) Form)``]
(DISCH_ALL th4)
in
 save_thm("Double_Negation",th5)
end;

(***************************************
* Hypothetical Syllogism
*
*   f1 impf f2   f2 impf f3
*  ---------------------
*          f1 impf f3
***************************************)

val Hypothetical_Syllogism =
let
 val th1 = ACL_ASSUM ``(f1:('a,'c,'d,'e)Form) impf (f2:('a,'c,'d,'e)Form)``
 val th2 = ACL_ASSUM ``(f2:('a,'c,'d,'e)Form) impf (f3:('a,'c,'d,'e)Form)``
 val th3 = 
  ACL_TAUT 
  ``((f1:('a,'c,'d,'e)Form) impf (f2:('a,'c,'d,'e)Form)) impf 
    (f2 impf (f3:('a,'c,'d,'e)Form)) impf (f1 impf f3)``
 val th4 = ACL_MP th1 th3
 val th5 = ACL_MP th2 th4
 val th6 = 
  DISCH ``((M :('a,'b, 'c, 'd, 'e) Kripke),(Oi :'d po),(Os :'e po)) sat
          (f2 :('a,'c, 'd, 'e) Form) impf (f3 :('a, 'c, 'd, 'e) Form)`` th5
 val th7 = 
   GENL [``(M :('a, 'b, 'c, 'd, 'e) Kripke)``,``(Oi :'d po)``,``(Os :'e po)``,
	 ``(f1 :('a, 'c, 'd, 'e) Form)``,``(f2 :('a, 'c, 'd, 'e) Form)``,
         ``(f3 :('a, 'c, 'd, 'e) Form)``]
   (DISCH_ALL th6)
in
 save_thm("Hypothetical_Syllogism",th7)
end;

fun HS th1 th2 = MATCH_MP(MATCH_MP (SPEC_ALL Hypothetical_Syllogism) th1) th2;

(***************************************
* Disjunctive Syllogism
*
*   f1 orf f2  notf f1
*  ---------------------
*           f1
***************************************)
val Disjunctive_Syllogism =
let
	val th1 = ACL_ASSUM ``notf (f1:('a,'c,'d,'e)Form)``
	val th2 = ACL_ASSUM ``(f1:('a,'c,'d,'e)Form) orf f2``
	val th3 = ACL_TAUT ``((f1:('a,'c,'d,'e)Form) orf f2) impf (notf f1) impf f2``
	val th4 = ACL_MP th2 th3
	val th5 = ACL_MP th1 th4
	val th6 = 
	    GENL [``(M :('a, 'b, 'c, 'd, 'e) Kripke)``,``(Oi :'d po)``,``(Os :'e po)``,
	       	     ``(f1 :('a, 'c, 'd, 'e) Form)``,``(f2 :('a, 'c, 'd, 'e) Form)``]
		    (DISCH_ALL th5)
in
	save_thm("Disjunctive_Syllogism",th6)
end;

fun SAYS princ form = 
    ISPECL [princ,form]  
    (ISPECL [``(M :('a, 'b, 'c, 'd, 'e) Kripke)``,``(Oi :'d po)``,``(Os :'e po)``]Says);

fun MP_SAYS princ f1 f2 = 
    ISPECL [princ, f1, f2](SPECL [``M:('a,'b,'c,'d,'e)Kripke``, ``Oi:'d po``, ``Os: 'e po``] MP_Says);

(***************************************
* Says Simplification 1
*
*   P says (f1 andf f2)
*  -----------------
*       P says f1
***************************************)
val Says_Simplification1 =
let
	val th1 = ACL_ASSUM ``P says ((f1:('a,'c,'d,'e)Form) andf f2)``
	val th2 = ACL_TAUT ``((f1:('a,'c,'d,'e)Form) andf f2) impf f1``
	val th3 = SAYS ``(P :'c Princ)`` ``((f1:('a,'c,'d,'e)Form) andf f2) impf f1``
	val th4 = MP th3 th2
	val th5 = 
	    MP_SAYS ``(P:'c Princ)`` ``(f1:('a,'c,'d,'e)Form) andf f2`` ``(f1:('a,'c,'d,'e)Form)``
	val th6 = ACL_MP th4 th5
	val th7 = ACL_MP th1 th6
	val th8 = 
	    GENL [``(M :('a, 'b, 'c, 'd, 'e) Kripke)``,``(Oi :'d po)``,``(Os :'e po)``,
	            ``(P :'c Princ)``,``(f1 :('a, 'c, 'd, 'e) Form)``,``(f2 :('a, 'c, 'd, 'e) Form)``]
		    (DISCH_ALL th7)
in
	save_thm("Says_Simplification1",th8)
end;


(***************************************
* Says Simplification 2
*
*   P says (f1 andf f2)
*  -----------------
*       P says f2
***************************************)
val Says_Simplification2 =
let
	val th1 = ACL_ASSUM ``P says ((f1:('a,'c,'d,'e)Form) andf f2)``
	val th2 = ACL_TAUT ``((f1:('a,'c,'d,'e)Form) andf f2) impf f2``
	val th3 = SAYS ``(P :'c Princ)`` ``((f1:('a,'c,'d,'e)Form) andf f2) impf f2``
	val th4 = MP th3 th2
	val th5 = 
	    MP_SAYS ``(P:'c Princ)`` ``(f1:('a,'c,'d,'e)Form) andf f2`` ``(f2:('a,'c,'d,'e)Form)``
	val th6 = ACL_MP th4 th5
	val th7 = ACL_MP th1 th6
	val th8 = GENL [``(M :('a, 'b, 'c, 'd, 'e) Kripke)``,``(Oi :'d po)``,``(Os :'e po)``,
	            ``(P :'c Princ)``,``(f1 :('a, 'c, 'd, 'e) Form)``,``(f2 :('a, 'c, 'd, 'e) Form)``]
		    (DISCH_ALL th7)
in
	save_thm("Says_Simplification2",th8)
end;

(***************************************
* Derived Speaks For
*
*   P speaks_for Q   P says f
*  ------------------------
*            Q says f
***************************************)
val Derived_Speaks_For =
let
	val th1 = ACL_ASSUM ``(P speaks_for Q):('a,'c,'d,'e)Form``
	val th2 = ACL_ASSUM ``(P: 'c Princ) says (f:('a,'c,'d,'e)Form)``
	(* For some reason, need to eliminate all quantifiers of Speaks_For *)
	val th3 = ACL_MP th1 (SPEC_ALL Speaks_For)
	val th4 = ACL_MP th2 th3
	val th5 = GENL [``(M :('a, 'b, 'c, 'd, 'e) Kripke)``,``(Oi :'d po)``,``(Os :'e po)``,
	            ``(P :'c Princ)``,``(Q :'c Princ)``,``(f :('a, 'c, 'd, 'e) Form)``]
		    (DISCH_ALL th4)
in
	save_thm("Derived_Speaks_For",th5)
end;

(**********************************************
* Derived Controls
*
*  P speaks_for Q    Q controls f
*  ----------------------------
*             P controls f
**********************************************)
val Derived_Controls =
let
	val th1 = ACL_ASSUM ``(P speaks_for Q):('a,'c,'d,'e)Form``
	val th2 = ACL_ASSUM ``Q controls (f:('a,'c,'d,'e)Form)``
	val th3 = REWRITE_RULE [Controls_Eq] th2
	val th4 = ACL_MP th1 (SPEC_ALL Speaks_For)
	val th5 = HS th4 th3
	val th6 = REWRITE_RULE [SYM(SPEC_ALL Controls_Eq)] th5
	val th7 = GENL [``(M :('a, 'b, 'c, 'd, 'e) Kripke)``,``(Oi :'d po)``,``(Os :'e po)``,
	                     ``(P :'c Princ)``,``(Q :'c Princ)``,``(f :('a, 'c, 'd, 'e) Form)``]
			    (DISCH_ALL th6)
in
	save_thm("Derived_Controls",th7)
end;

fun DC th1 th2 = MATCH_MP(MATCH_MP (SPEC_ALL Derived_Controls) th1) th2;


fun DOMS_TRANS th1 th2 = MATCH_MP(MATCH_MP (SPEC_ALL doms_transitive) th1) th2;
(******************************
* sl doms
*
*  sl(P) eqs l1   sl(Q) eqs l2   l2 doms l1
*  -------------------------------
*                sl(Q) doms sl(P)
******************************)

val sl_doms =
let
	val th1 = ACL_ASSUM ``(sl(P) eqs l1):('a,'c,'d,'e)Form``
	val th2 = ACL_ASSUM ``(sl(Q) eqs l2):('a,'c,'d,'e)Form``
	val th3 = ACL_ASSUM ``(l2 doms l1):('a,'c,'d,'e)Form``
	val th4 = REWRITE_RULE [eqs_Eq] th1
	val th5 = REWRITE_RULE [eqs_Eq] th2
	val th6 = ACL_SIMP1 th4
	val th7 = DOMS_TRANS th3 th6
	val th8 = ACL_SIMP2 th5
	val th9 = DOMS_TRANS th8 th7
	val th10 = 
	    DISCH 
	    ``(M,Oi,Os) sat sl P eqs l1`` 
	    (DISCH ``(M,Oi,Os) sat sl Q eqs l2`` 
	    (DISCH ``(M,Oi,Os) sat l2 doms l1`` th9))
	val th11 = 
    	    GENL [``(M :('a, 'b, 'c, 'd, 'e) Kripke)``,``(Oi :'d po)``,``(Os :'e po)``,
    	    	    ``(P:'c)``,``(Q:'c)``,``(l1 :('c, 'e) SecLevel)``,``(l2 :('c, 'e) SecLevel)``] th10
in
	save_thm("sl_doms",th11)
end;

fun SL_DOMS th1 th2 th3 = MATCH_MP(MATCH_MP(MATCH_MP sl_doms th1) th2) th3;
fun DOMI_TRANS th1 th2 = MATCH_MP(MATCH_MP (SPEC_ALL domi_transitive) th1) th2;
(******************************
* il domi
*
*  il(P) eqi l1   il(Q) eqi l2   l2 domi l1
*  -------------------------------
*                il(Q) domi il(P)
******************************)

val il_domi =
let
	val th1 = ACL_ASSUM ``(il(P) eqi l1):('a,'c,'d,'e)Form``
	val th2 = ACL_ASSUM ``(il(Q) eqi l2):('a,'c,'d,'e)Form``
	val th3 = ACL_ASSUM ``(l2 domi l1):('a,'c,'d,'e)Form``
	val th4 = REWRITE_RULE [eqi_Eq] th1
	val th5 = REWRITE_RULE [eqi_Eq] th2
	val th6 = ACL_SIMP1 th4
	val th7 = DOMI_TRANS th3 th6
	val th8 = ACL_SIMP2 th5
	val th9 = DOMI_TRANS th8 th7
	val th10 = 
	    DISCH 
	    ``(M,Oi,Os) sat il P eqi l1`` 
	    (DISCH ``(M,Oi,Os) sat il Q eqi l2`` 
	    (DISCH ``(M,Oi,Os) sat l2 domi l1`` th9))
	val th11 = 
    	    GENL [``(M :('a, 'b, 'c, 'd, 'e) Kripke)``,``(Oi :'d po)``,``(Os :'e po)``,
    	    	    ``(P:'c)``,``(Q:'c)``,``(l1 :('c, 'd) IntLevel)``,``(l2 :('c, 'd) IntLevel)``] th10
in
	save_thm("il_domi",th11)
end;

(***********************************************************
* IL_DOMI
*
* IL_DOMI : thm -> thm -> thm -> thm
*
* SYNOPSIS
* Applies il_domi to theorems in the access-control logic
*
* DESCRIPTION
*
*  A1 |- (M,Oi,Os) sat il P eqi l1   A2 |- (M,Oi,Os) sat il Q eqi l2  A3 |- (M,Oi,Os) sat l2 domi l1
*  ------------------------------------------------------------------------------------ IL_DOMI
*                                   A1 u A2 u A3 |- (M,Oi,Os) sat il Q domi il P
*
* FAILURE
* Fails unless the input theorems match in their corresponding terms in the
* access-control logic
***********************************************************)
fun IL_DOMI th1 th2 th3 = MATCH_MP(MATCH_MP(MATCH_MP il_domi th1) th2) th3;

val th1 = ACL_ASSUM ``(c1 eqn n1):('a,'c,'d,'e)Form``;
val th2 = ACL_ASSUM ``(c2 eqn n2):('a,'c,'d,'e)Form``;
val th3 = ACL_ASSUM ``(n1 lte n2):('a,'c,'d,'e)Form``;
val th4 = REWRITE_RULE[sat_def,eqn_def] th1;


(**************************************************
* val eqn_lte =
*    |- (M,Oi,Os) sat c1 eqn n1 ==>
*       (M,Oi,Os) sat c2 eqn n2 ==>
*       (M,Oi,Os) sat n1 lte n2 ==>
*       (M,Oi,Os) sat c1 lte c2 : thm
**************************************************)
val eqn_lte =
save_thm("eqn_lte",
TAC_PROOF(
 ([],
 ``((M :('a, 'b, 'c, 'd, 'e) Kripke),(Oi :'d po),(Os :'e po)) sat
    (((c1 :num) eqn (n1 :num)) :('a, 'c, 'd, 'e) Form) ==>
   ((M :('a, 'b, 'c, 'd, 'e) Kripke),(Oi :'d po),(Os :'e po)) sat
       (((c2 :num) eqn (n2 :num)) :('a, 'c, 'd, 'e) Form) ==>
   ((M :('a, 'b, 'c, 'd, 'e) Kripke),(Oi :'d po),(Os :'e po)) sat
       (((n1 :num) lte (n2 :num)) :('a, 'c, 'd, 'e) Form) ==>
   ((M :('a, 'b, 'c, 'd, 'e) Kripke),(Oi :'d po),(Os :'e po)) sat
       (((c1 :num) lte (c2 :num)) :('a, 'c, 'd, 'e) Form)``),
(REWRITE_TAC[sat_def,eqn_def,lte_def] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[EMPTY_NOT_UNIV] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[EMPTY_NOT_UNIV] THEN
  ASM_REWRITE_TAC[])));

(**************************************************
* val eqn_lt =
*    |- (M,Oi,Os) sat c1 eqn n1 ==>
*       (M,Oi,Os) sat c2 eqn n2 ==>
*       (M,Oi,Os) sat n1 lt n2 ==>
*       (M,Oi,Os) sat c1 lt c2 : thm
**************************************************)
val eqn_lt =
save_thm("eqn_lt",
TAC_PROOF(
 ([],
 ``((M :('a, 'b, 'c, 'd, 'e) Kripke),(Oi :'d po),(Os :'e po)) sat
    (((c1 :num) eqn (n1 :num)) :('a, 'c, 'd, 'e) Form) ==>
   ((M :('a, 'b, 'c, 'd, 'e) Kripke),(Oi :'d po),(Os :'e po)) sat
       (((c2 :num) eqn (n2 :num)) :('a, 'c, 'd, 'e) Form) ==>
   ((M :('a, 'b, 'c, 'd, 'e) Kripke),(Oi :'d po),(Os :'e po)) sat
       (((n1 :num) lt (n2 :num)) :('a, 'c, 'd, 'e) Form) ==>
   ((M :('a, 'b, 'c, 'd, 'e) Kripke),(Oi :'d po),(Os :'e po)) sat
       (((c1 :num) lt (c2 :num)) :('a, 'c, 'd, 'e) Form)``),
(REWRITE_TAC[sat_def,eqn_def,lt_def] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[EMPTY_NOT_UNIV] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[EMPTY_NOT_UNIV] THEN
  ASM_REWRITE_TAC[])));

(**************************************************
* val eqn_eqn =
*    |- (M,Oi,Os) sat c1 eqn n1 ==>
*       (M,Oi,Os) sat c2 eqn n2 ==>
*       (M,Oi,Os) sat n1 eqn n2 ==>
*       (M,Oi,Os) sat c1 eqn c2 : thm
**************************************************)
val eqn_eqn =
save_thm("eqn_eqn",
TAC_PROOF(
 ([],
 ``((M :('a, 'b, 'c, 'd, 'e) Kripke),(Oi :'d po),(Os :'e po)) sat
    (((c1 :num) eqn (n1 :num)) :('a, 'c, 'd, 'e) Form) ==>
   ((M :('a, 'b, 'c, 'd, 'e) Kripke),(Oi :'d po),(Os :'e po)) sat
       (((c2 :num) eqn (n2 :num)) :('a, 'c, 'd, 'e) Form) ==>
   ((M :('a, 'b, 'c, 'd, 'e) Kripke),(Oi :'d po),(Os :'e po)) sat
       (((n1 :num) eqn (n2 :num)) :('a, 'c, 'd, 'e) Form) ==>
   ((M :('a, 'b, 'c, 'd, 'e) Kripke),(Oi :'d po),(Os :'e po)) sat
       (((c1 :num) eqn (c2 :num)) :('a, 'c, 'd, 'e) Form)``),
(REWRITE_TAC[sat_def,eqn_def,eqn_def] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[EMPTY_NOT_UNIV] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[EMPTY_NOT_UNIV] THEN
  ASM_REWRITE_TAC[])));

val _ = print_theory "-";
val _ = export_theory ();

end;
