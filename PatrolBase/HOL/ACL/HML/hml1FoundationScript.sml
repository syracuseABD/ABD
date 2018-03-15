(* Hennessy-Milner Logic foundation with variables by SK Chin 26 April 2012 *)

(* Interactive Mode
app load ["pred_setTheory","pred_setLib","fixedPointTheory","hml1FoundationTheory"];
open pred_setTheory pred_setLib fixedPointTheory hml1FoundationTheory;
*)
(* HML Syntax *)

structure hml1FoundationScript = struct

open HolKernel boolLib Parse; 
open bossLib pred_setTheory pred_setLib fixedPointTheory;

val _ = new_theory "hml1Foundation";

(* Syntax of HML *)
val _ = Hol_datatype
    `hmlForm = tt 
             | ff
	     | proph of 'propvar
             | andh of hmlForm => hmlForm 
             | orh of hmlForm => hmlForm
             | Box of 'action set => hmlForm
             | Dia of 'action set => hmlForm`;

(* make andh and orh infix operators *)
val _ = set_fixity "andh" (Infixr 580);
val _ = set_fixity "orh" (Infixr 570);

(* Semantics of hmsat *)
val _ = set_fixity "hmsat" (Infixr 540);

val hmsat_def =
    Define
    `((((E:'configuration),(Trans:'action -> 'configuration -> 'configuration -> bool),(V:'propvar -> 'configuration set)) hmsat tt) = T) /\
     ((((E:'configuration),(Trans:'action -> 'configuration -> 'configuration -> bool),(V:'propvar -> 'configuration set)) hmsat ff) = F) /\
     ((((E:'configuration),(Trans:'action -> 'configuration -> 'configuration -> bool),(V:'propvar -> 'configuration set)) hmsat (proph Z)) 
      = (E IN (V Z))) /\
     ((((E:'configuration),(Trans:'action -> 'configuration -> 'configuration -> bool),(V:'propvar -> 'configuration set)) hmsat 
      (f1:('action,'propvar) hmlForm) andh (f2:('action,'propvar) hmlForm)) = (((E,Trans,V) hmsat f1) /\ (((E,Trans,V) hmsat f2)))) /\
     ((((E:'configuration),(Trans:'action -> 'configuration -> 'configuration -> bool),(V:'propvar -> 'configuration set)) hmsat 
      (f1:('action,'propvar) hmlForm) orh (f2:('action,'propvar) hmlForm)) = (((E,Trans,V) hmsat f1) \/ (((E,Trans,V) hmsat f2)))) /\
     ((((E:'configuration),(Trans:'action -> 'configuration -> 'configuration -> bool),(V:'propvar -> 'configuration set)) hmsat 
      (Box (Actions:'action set)(f:('action,'propvar) hmlForm))) = 
      (!(E':'configuration)(a:'action).(Trans a E E') ==> ((a IN Actions) ==> ((E',Trans,V) hmsat f)))) /\
     ((((E:'configuration),(Trans:'action -> 'configuration -> 'configuration -> bool),(V:'propvar -> 'configuration set)) hmsat 
      (Dia (Actions:'action set)(f:('action,'propvar) hmlForm))) = 
      (?(E':'configuration)(a:'action).(Trans a E E') /\ ((a IN Actions) /\ ((E',Trans,V) hmsat f))))`; 

(********************************************************************)
(* Meaning function for formulas given a transition relation Trans, *)
(* set of processes E, and a valuation function V.                  *)
(* UNIV:('configuration set) corresponds to the universe of process *)
(* names in Section 1.6 of Colin Stirling's book Modal and Temporal *)
(* Properties of Processes.                                         *)
(********************************************************************)
val HMfn_def =
Define
`HMfn 
 (Trans:'action -> 'configuration -> 'configuration -> bool)
 (f:('action,'propvar) hmlForm)
 (E:'configuration set)
 (V:'propvar -> 'configuration set)
  = {s | s ∈ E ∧ (s,Trans,V) hmsat f}`;

(* Update function for valuations *)
val HMUpdate_def =
Define
`HMUpdate (Z:'propvar)(V:'propvar -> 'configuration set)(E:'configuration set)(Y:'propvar) =
 if Y=Z then E else V Y`;

(* Extending a valuation                               *)
(* V' extends V if V(Z) subset V'(Z) for all variables *)

val extends_def =
Define
`extends V V' = 
!(Z:'propvar).((V:'propvar -> 'configuration set) Z) SUBSET ((V':'propvar -> 'configuration set) Z)`;

(* ========================================= *)
(* SOME PROPERTIES OF PREDICATE SETS WE NEED *)
(* ========================================= *)
val IN_CLAUSES = 
TAC_PROOF
(([],``({s | s IN (\x.P x \/ Q x)} = {s | (s IN \x.P x) \/ (s IN \x.Q x)}) /\
       ({s | s IN (\x.P x /\ Q x)} = {s | (s IN \x.P x) /\ (s IN \x.Q x)})``),
 (REWRITE_TAC[IN_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[]));

val _ = save_thm("IN_CLAUSES",IN_CLAUSES);

val IN_UNION_INTER_CLAUSES =
TAC_PROOF
(([],``({s | s IN (\x.P x /\ Q x)} = (\x.P x) INTER (\x.Q x)) /\
       ({s | s IN (\x.P x \/ Q x)} = (\x.P x) UNION (\x.Q x)) ``),
(REWRITE_TAC[IN_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[(GSYM INTER_DEF),(GSYM UNION_DEF)]));

val _ = save_thm("IN_UNION_INTER_CLAUSES",IN_UNION_INTER_CLAUSES);

(* ============================ *)
(* monotonicity of intersection *)
(* ============================ *)

val MONOTONE_INTER =
TAC_PROOF(([],``(A SUBSET A') ==> (B SUBSET B') ==> ((A INTER B) SUBSET (A' INTER B'))``),
 (REWRITE_TAC[SUBSET_DEF,IN_INTER] THEN
  REPEAT STRIP_TAC THEN
  RES_TAC));

val _ = save_thm("MONOTONE_INTER", MONOTONE_INTER);

(* ===================== *)
(* monotonicity of union *)
(* ===================== *)
val MONOTONE_UNION =
TAC_PROOF(([],``(A SUBSET A') ==> (B SUBSET B') ==> ((A UNION B) SUBSET (A' UNION B'))``),
 (REWRITE_TAC[SUBSET_DEF,IN_UNION] THEN
  REPEAT STRIP_TAC THEN
  RES_TAC THEN
  ASM_REWRITE_TAC[]));

val _ = save_thm("MONOTONE_UNION", MONOTONE_UNION);

(* ====================================================== *)
(* SOME PROPERTIES OF HMfn WITH RESPECT TO PREDICATE SETS *)
(* ====================================================== *)
val hmsat_IN_CLAUSES =
TAC_PROOF(([],
``(!(s:'configuration)(form:('action,'propvar)hmlForm)(V:'propvar -> 'configuration set)
   (Trans:'action -> 'configuration -> 'configuration -> bool).
   {s | (s,Trans,V) hmsat form} = {s | s IN \x.(x,Trans,V) hmsat form}) /\
  (!(s:'configuration)(f1:('action,'propvar)hmlForm)(f2:('action,'propvar)hmlForm)
    (V:'propvar -> 'configuration set).
   {s | (s,Trans,V) hmsat f1 /\ (s,Trans,V) hmsat f2} = 
   {s | (s IN \x.((x,Trans,V) hmsat f1)) /\ (s IN (\x.(x,Trans,V) hmsat f2))}) /\
  (!(s:'configuration)(f1:('action,'propvar)hmlForm)(f2:('action,'propvar)hmlForm)
    (V:'propvar -> 'configuration set).
   {s | (s,Trans,V) hmsat f1 \/ (s,Trans,V) hmsat f2} = 
   {s | (s IN \x.((x,Trans,V) hmsat f1)) \/ (s IN \x.((x,Trans,V) hmsat f2))})``),
 (REWRITE_TAC[IN_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[]));

val _ = save_thm("hmsat_IN_CLAUSES",hmsat_IN_CLAUSES);

val HMfn_CLAUSES =
TAC_PROOF(([],
 ``(!(f1:('action,'propvar)hmlForm)(f2:('action,'propvar)hmlForm)
   (V:'propvar -> 'configuration set)
   (Trans:'action -> 'configuration -> 'configuration -> bool).
   (HMfn Trans (f1 andh f2) (UNIV:'configuration set) V) =
   ((HMfn Trans f1 UNIV V) INTER (HMfn Trans f2 UNIV V))) /\
   (!(f1:('action,'propvar)hmlForm)(f2:('action,'propvar)hmlForm)
   (V:'propvar -> 'configuration set)
   (Trans:'action -> 'configuration -> 'configuration -> bool).
   (HMfn Trans (f1 orh f2) (UNIV:'configuration set) V) =
   ((HMfn Trans f1 UNIV V) UNION (HMfn Trans f2 UNIV V)))``),
 (REPEAT STRIP_TAC THEN
  REWRITE_TAC[HMfn_def,hmsat_def,IN_UNIV] THEN
  REWRITE_TAC[hmsat_IN_CLAUSES] THEN
  REWRITE_TAC[INTER_DEF, UNION_DEF, GSPEC_ID]));

val _ = save_thm("HMfn_CLAUSES",HMfn_CLAUSES);

val box_lemma1 =
TAC_PROOF(([],``{s |
     !(E' :'configuration) (a :'action).
       (Trans :'action -> 'configuration -> 'configuration -> bool) a s
         E' ==>
       a IN (f :'action -> bool) ==>
       (E',Trans,(V :'propvar -> 'configuration -> bool)) hmsat
       (form :('action, 'propvar) hmlForm)} =
  {s | s IN \s.(!(E' :'configuration) (a :'action).
       (Trans :'action -> 'configuration -> 'configuration -> bool) a s
         E' ==>
       a IN (f :'action -> bool) ==>
       (E',Trans,(V :'propvar -> 'configuration -> bool)) hmsat
       (form :('action, 'propvar) hmlForm))}``),
 (REWRITE_TAC[IN_DEF] THEN
  CONV_TAC(DEPTH_CONV(BETA_CONV)) THEN
  REWRITE_TAC[]));
val box_lemma2 =
TAC_PROOF(([],``(\s.(!E' a. Trans a s E' ==> a IN f ==> (E',Trans,V) hmsat form)) = (\s.(!E' a. Trans a s E' /\ a IN f ==> (E',Trans,V) hmsat form))``),
 (REPEAT STRIP_TAC THEN
  REWRITE_TAC[AND_IMP_INTRO]));
(* ======================================== *)
(* Beginning of proofs of HMfn monotonicity *)
(* ======================================== *)

(* =============================== *)
(* HMfn is monotonic wrt tt and ff *)
(* =============================== *)
val HMfn_tt_ff_CLAUSES =
TAC_PROOF(([],
 ``(!(Trans:'action -> 'configuration -> 'configuration -> bool)
     (V:'propvar -> 'configuration set)(V':'propvar -> 'configuration set).
      (HMfn Trans tt (UNIV:'configuration set) V) SUBSET (HMfn Trans tt (UNIV:'configuration set) V')) /\ 
   (!(Trans:'action -> 'configuration -> 'configuration -> bool)
     (V:'propvar -> 'configuration set)(V':'propvar -> 'configuration set).
      (HMfn Trans ff (UNIV:'configuration set) V) SUBSET (HMfn Trans ff (UNIV:'configuration set) V'))``),
 (REWRITE_TAC[HMfn_def,IN_UNIV] THEN
  REWRITE_TAC[hmsat_def,SUBSET_REFL]));

val _ = save_thm("HMfn_tt_ff_CLAUSES",HMfn_tt_ff_CLAUSES);

(* ================================================== *)
(* HMFn is monotonic on V wrt propositional variables *)
(* ================================================== *)
val HMfn_MONOTONIC_propvar =
TAC_PROOF(([],
``!(Z:'propvar)(V:'propvar -> 'configuration set)(V':'propvar -> 'configuration set). extends V V' ==>  
   ((HMfn (Trans:'action -> 'configuration -> 'configuration -> bool) 
          (proph (Z:'propvar))
	  (UNIV:'configuration set) 
          (V:'propvar -> 'configuration set)) SUBSET 
    (HMfn (Trans:'action -> 'configuration -> 'configuration -> bool) 
    	  (proph (Z:'propvar))
          (UNIV:'configuration set) 
          (V':'propvar -> 'configuration set)))``),
 (REPEAT GEN_TAC THEN
  REWRITE_TAC[extends_def, HMfn_def,IN_UNIV] THEN
  REWRITE_TAC[hmsat_def,IN_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[GSPEC_ETA] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC[]));

val _ =
save_thm("HMfn_MONOTONIC_propvar",HMfn_MONOTONIC_propvar);

(* ==================================== *)
(* Proof that HMfn is monotonic on andh *)
(* ==================================== *)

val HMfn_MONOTONIC_andh =
TAC_PROOF(([],
``(!(V :'propvar -> 'configuration -> bool)
        (V' :'propvar -> 'configuration -> bool).
       extends V V' ==>
       HMfn (Trans :'action -> 'configuration -> 'configuration -> bool)
         (form :('action, 'propvar) hmlForm)
         univ((:'configuration) :'configuration itself) V SUBSET
       HMfn Trans form univ((:'configuration) :'configuration itself)
         V') ==>
    (!(V :'propvar -> 'configuration -> bool)
        (V' :'propvar -> 'configuration -> bool).
       extends V V' ==>
       HMfn Trans (form' :('action, 'propvar) hmlForm)
         univ((:'configuration) :'configuration itself) V SUBSET
       HMfn Trans form' univ((:'configuration) :'configuration itself)
         V') ==>
    extends (V :'propvar -> 'configuration -> bool)
      (V' :'propvar -> 'configuration -> bool) ==>
    HMfn Trans form univ((:'configuration) :'configuration itself) V INTER
    HMfn Trans form' univ((:'configuration) :'configuration itself) V SUBSET
    HMfn Trans form univ((:'configuration) :'configuration itself) V' INTER
    HMfn Trans form' univ((:'configuration) :'configuration itself) V'``),
(REPEAT DISCH_TAC THEN 
  RES_TAC THEN
(* remove extends V V' from subgoal assumption list                  *)
(* and remove one extends V V' ==> term from subgoal assumption list *)
  PAT_ASSUM ``extends A B`` (fn th => ALL_TAC) THEN
  PAT_ASSUM 
  ``!(V :'propvar -> 'configuration -> bool)
           (V' :'propvar -> 'configuration -> bool).
          extends V V' ⇒ A``
  (fn th => ALL_TAC) THEN
(* remove one more extends V V' ==> term from the subgoal *)
  PAT_ASSUM 
  ``!(V :'propvar -> 'configuration -> bool)(V' :'propvar -> 'configuration -> bool). 
   extends V V' ⇒ A`` (fn th => ALL_TAC) THEN
IMP_RES_TAC MONOTONE_INTER));

val _ = save_thm("HMfn_MONOTONIC_andh",HMfn_MONOTONIC_andh);
(* =================================== *)
(* Proof that HMfn is monotonic on orh *)
(* =================================== *)
val HMfn_MONOTONIC_orh =
TAC_PROOF(([],
``(!(V :'propvar -> 'configuration -> bool)
        (V' :'propvar -> 'configuration -> bool).
       extends V V' ==>
       HMfn (Trans :'action -> 'configuration -> 'configuration -> bool)
         (form :('action, 'propvar) hmlForm)
         univ((:'configuration) :'configuration itself) V SUBSET
       HMfn Trans form univ((:'configuration) :'configuration itself)
         V') ==>
    (!(V :'propvar -> 'configuration -> bool)
        (V' :'propvar -> 'configuration -> bool).
       extends V V' ==>
       HMfn Trans (form' :('action, 'propvar) hmlForm)
         univ((:'configuration) :'configuration itself) V SUBSET
       HMfn Trans form' univ((:'configuration) :'configuration itself)
         V') ==>
    extends (V :'propvar -> 'configuration -> bool)
      (V' :'propvar -> 'configuration -> bool) ==>
    HMfn Trans form univ((:'configuration) :'configuration itself) V UNION
    HMfn Trans form' univ((:'configuration) :'configuration itself) V SUBSET
    HMfn Trans form univ((:'configuration) :'configuration itself) V' UNION
    HMfn Trans form' univ((:'configuration) :'configuration itself) V'``),
(REPEAT DISCH_TAC THEN 
  RES_TAC THEN
(* remove extends V V' from subgoal assumption list                  *)
(* and remove one extends V V' ==> term from subgoal assumption list *)
  PAT_ASSUM ``extends A B`` (fn th => ALL_TAC) THEN
  PAT_ASSUM 
  ``!(V :'propvar -> 'configuration -> bool)
           (V' :'propvar -> 'configuration -> bool).
          extends V V' ⇒ A``
  (fn th => ALL_TAC) THEN
(* remove one more extends V V' ==> term from the subgoal *)
  PAT_ASSUM 
  ``!(V :'propvar -> 'configuration -> bool)(V' :'propvar -> 'configuration -> bool). 
   extends V V' ⇒ A`` (fn th => ALL_TAC) THEN
IMP_RES_TAC MONOTONE_UNION));

val _ = save_thm("HMfn_MONOTONIC_orh",HMfn_MONOTONIC_orh);

(* Some conversions we will use for Box and Dia proofs *)
val th1 =
SET_SPEC_CONV
``x IN {s |
        (s,(Trans :'action -> 'configuration -> 'configuration -> bool),
         (V :'propvar -> 'configuration -> bool)) hmsat
        (form :('action, 'propvar) hmlForm)}``;
val th2 =
SET_SPEC_CONV
``x IN
       {s |
        (s,Trans,(V' :'propvar -> 'configuration -> bool)) hmsat form}``;
val th3 =
SET_SPEC_CONV
``x IN
      {s |
       !(E' :'configuration) (a :'action).
         Trans a s E' ==>
         a IN (f :'action -> bool) ==>
         (E',Trans,V) hmsat form}``;

val th4 =
SET_SPEC_CONV
``x IN
      {s |
       !(E' :'configuration) (a :'action).
         Trans a s E' ==> a IN f ==> (E',Trans,V') hmsat form}``;

(* =========================== *)
(* Proof that Box is monotonic *)
(* =========================== *)

val HMfn_MONOTONIC_Box =
TAC_PROOF(([],
``(!(V :'propvar -> 'configuration -> bool)
        (V' :'propvar -> 'configuration -> bool).
       extends V V' ==>
       HMfn (Trans :'action -> 'configuration -> 'configuration -> bool)
         (form :('action, 'propvar) hmlForm)
         univ((:'configuration) :'configuration itself) V SUBSET
       HMfn Trans form univ((:'configuration) :'configuration itself)
         V') ==>
    extends (V :'propvar -> 'configuration -> bool)
      (V' :'propvar -> 'configuration -> bool) ==>
    HMfn Trans (Box (f :'action -> bool) form)
      univ((:'configuration) :'configuration itself) V SUBSET
    HMfn Trans (Box f form) univ((:'configuration) :'configuration itself)
      V'``),
(REWRITE_TAC[HMfn_MONOTONIC_propvar, HMfn_tt_ff_CLAUSES,HMfn_CLAUSES] THEN
(* move extends V V' into assumptions and do resolution *)
  REPEAT DISCH_TAC THEN 
  RES_TAC THEN
(* remove extends V V' from subgoal assumption list                  *)
(* and remove one extends V V'==> term from subgoal assumption list *)
  PAT_ASSUM ``extends A B`` (fn th => ALL_TAC) THEN
  PAT_ASSUM ``!V V'.extends A B ==> term`` (fn th => ALL_TAC) THEN UNDISCH_TAC
``HMfn (Trans :'action -> 'configuration -> 'configuration -> bool)
        (form :('action, 'propvar) hmlForm)
        univ((:'configuration) :'configuration itself)
        (V :'propvar -> 'configuration -> bool) SUBSET
      HMfn Trans form univ((:'configuration) :'configuration itself)
        (V' :'propvar -> 'configuration -> bool)`` THEN
REWRITE_TAC[SUBSET_DEF,HMfn_def,hmsat_def,IN_UNIV,th1,th2,th3,th4] THEN
REPEAT STRIP_TAC THEN
REPEAT RES_TAC));

val _ = save_thm("HMfn_MONOTONIC_Box",HMfn_MONOTONIC_Box);

(* =========================== *)
(* Proof that Dia is monotonic *)
(* =========================== *)
val th5 =
SET_SPEC_CONV
``x IN
      {s |
       ?(E' :'configuration) (a :'action).
         Trans a s E' /\ a IN (f :'action -> bool) /\
         (E',Trans,V) hmsat form}``;

val th6 =
SET_SPEC_CONV
``x IN
      {s |
       ?(E' :'configuration) (a :'action).
         Trans a s E' /\ a IN f /\ (E',Trans,V') hmsat form}``;

val HMfn_MONOTONIC_Dia =
TAC_PROOF(([],
``(!(V :'propvar -> 'configuration -> bool)
        (V' :'propvar -> 'configuration -> bool).
       extends V V' ==>
       HMfn (Trans :'action -> 'configuration -> 'configuration -> bool)
         (form :('action, 'propvar) hmlForm)
         univ((:'configuration) :'configuration itself) V SUBSET
       HMfn Trans form univ((:'configuration) :'configuration itself)
         V') ==>
    extends (V :'propvar -> 'configuration -> bool)
      (V' :'propvar -> 'configuration -> bool) ==>
    HMfn Trans (Dia (f :'action -> bool) form)
      univ((:'configuration) :'configuration itself) V SUBSET
    HMfn Trans (Dia f form) univ((:'configuration) :'configuration itself)
      V'``),
(REWRITE_TAC[HMfn_MONOTONIC_propvar, HMfn_tt_ff_CLAUSES,HMfn_CLAUSES] THEN
(* move extends V V' into assumptions and do resolution *)
  REPEAT DISCH_TAC THEN 
  RES_TAC THEN
(* remove extends V V' from subgoal assumption list                  *)
(* and remove one extends V V'==> term from subgoal assumption list *)
  PAT_ASSUM ``extends A B`` (fn th => ALL_TAC) THEN
  PAT_ASSUM ``!V V'.extends A B ==> term`` (fn th => ALL_TAC) THEN UNDISCH_TAC
``HMfn (Trans :'action -> 'configuration -> 'configuration -> bool)
        (form :('action, 'propvar) hmlForm)
        univ((:'configuration) :'configuration itself)
        (V :'propvar -> 'configuration -> bool) SUBSET
      HMfn Trans form univ((:'configuration) :'configuration itself)
        (V' :'propvar -> 'configuration -> bool)`` THEN
REWRITE_TAC[SUBSET_DEF,HMfn_def,hmsat_def,IN_UNIV,th1,th2,th5,th6] THEN
 REPEAT STRIP_TAC THEN
 EXISTS_TAC ``(E' :'configuration)`` THEN
 EXISTS_TAC ``(a :'action)`` THEN
 RES_TAC THEN
 ASM_REWRITE_TAC[]));

val _ = save_thm("HMfn_MONOTONIC_Dia",HMfn_MONOTONIC_Dia);

val HMfn_MONOTONIC =
TAC_PROOF(([],
``!(form:('action,'propvar)hmlForm)(V:'propvar -> 'configuration set)(V':'propvar -> 'configuration set). extends V V' ==>  
   ((HMfn (Trans:'action -> 'configuration -> 'configuration -> bool) 
          form
	  (UNIV:'configuration set) 
          (V:'propvar -> 'configuration set)) SUBSET 
    (HMfn (Trans:'action -> 'configuration -> 'configuration -> bool) 
    	  form
          (UNIV:'configuration set) 
          (V':'propvar -> 'configuration set)))``),
(Induct THEN
(* Proof of tt, ff, propvar *)
  REPEAT GEN_TAC THEN
  REWRITE_TAC[HMfn_MONOTONIC_propvar, HMfn_tt_ff_CLAUSES,HMfn_CLAUSES] THEN
  PROVE_TAC[HMfn_MONOTONIC_andh,HMfn_MONOTONIC_orh,HMfn_MONOTONIC_Box,HMfn_MONOTONIC_Dia]));

val _ = save_thm("HMfn_MONOTONIC",HMfn_MONOTONIC);

(* Define f[phi,Z](E) in Stirling p.93 *)
val satFun_def =
    Define
    `satFun 
     (Trans:'action -> 'configuration -> 'configuration -> bool)
     (Z:'propvar)(V:'propvar -> 'configuration set)
     (form:('action,'propvar)hmlForm)(E:'configuration set) =
     (HMfn 
      Trans form(UNIV:'configuration set)(HMUpdate Z V E))`;

(* ======================== *)
(* Monotonicity of HMUpdate *)
(* ======================== *)
val HMUpdate_MONOTONIC =
TAC_PROOF(([],``!(V:'propvar -> 'configuration set)
   (Z:'propvar)(E:'configuration set)(F:'configuration set).
   (E SUBSET F) ==> (extends (HMUpdate Z V E)(HMUpdate Z V F))``),
(REWRITE_TAC[SUBSET_DEF,extends_def,HMUpdate_def,SPECIFICATION] THEN
 REPEAT GEN_TAC THEN
 DISCH_TAC THEN
 REPEAT GEN_TAC THEN
 COND_CASES_TAC THEN
 ASM_REWRITE_TAC[]));

val _ = save_thm("HMUpdate_MONOTONIC",HMUpdate_MONOTONIC);
(* =========================== *)
(* Corollary 1: p. 94 Stirling *)
(* =========================== *)
val satFun_MONOTONIC =
TAC_PROOF(([],``!(V:'propvar -> 'configuration set)
   (Trans:'action -> 'configuration -> 'configuration -> bool)
   (Z:'propvar)(form:('action,'propvar)hmlForm)
   (E1:'configuration set)(E2:'configuration set).
   (E1 SUBSET E2) ==> 
   ((satFun Trans Z V form E1) SUBSET (satFun Trans Z V form E2))``),
(REWRITE_TAC[satFun_def] THEN
 REPEAT STRIP_TAC THEN
 IMP_RES_TAC HMUpdate_MONOTONIC THEN
 PAT_ASSUM ``!x.P`` (fn th => ASSUME_TAC (SPEC_ALL th)) THEN
 IMP_RES_TAC
 (ISPECL
  [``form:('action,'propvar)hmlForm``,
   ``(HMUpdate (Z :'propvar) (V :'propvar -> 'configuration set)(E1 :'configuration set))``,
   ``(HMUpdate (Z :'propvar) (V :'propvar -> 'configuration set)(E2 :'configuration set))``]
   HMfn_MONOTONIC) THEN
 ASM_REWRITE_TAC[]));

val _ = save_thm("satFun_MONOTONIC",satFun_MONOTONIC);

(* ============ *)
(* FIXED POINTS *)
(* ============ *)

(* ================================================================= *)
(* Define least fixed point of satFun Trans Z form E, which is       *)
(* f[form,Z](E) in Stirling p.97 as INTERSECTION {E | f(E) SUBSET E} *)
(* We take advantage of the existing fixed_point theory in HOL.      *)
(* ================================================================= *)

(* =============================================== *)
(* Define our least fixed point function using lfp *)
(* =============================================== *)
val hmLFP_def =
Define
`hmLFP (Trans :'action -> 'configuration -> 'configuration -> bool)
    (Z :'propvar)
    (V :'propvar -> 'configuration set)
    (form :('action, 'propvar) hmlForm)
     =
  lfp  (satFun Trans Z V form)`;

(* =========================================== *)
(* show that satFun Tranz Z V form is monotone *)
(* =========================================== *)
val satFun_monotone =
TAC_PROOF(([],``monotone (satFun Trans Z V form)``),
(REWRITE_TAC[monotone_def,satFun_MONOTONIC]));

val _ = save_thm("satFun_monotone",satFun_monotone);

(* ====================================== *)
(* show that hmLFP is a least fixed point *)
(* ====================================== *)
val hmLFP_fixedpoint =
TAC_PROOF(([],``!Trans Z V form.(hmLFP Trans Z V form = satFun Trans Z V form (hmLFP Trans Z V form)) /\
  !X.((X = (satFun Trans Z V form X)) ==> ((hmLFP Trans Z V form) SUBSET X))``),
(PROVE_TAC[hmLFP_def,lfp_fixedpoint,satFun_monotone]));

val _ = save_thm("hmLFP_fixedpoint",hmLFP_fixedpoint);

(* ================================================== *)
(* Define our greatest fixed point function using gfp *)
(* ================================================== *)
val hmGFP_def =
Define
`hmGFP (Trans :'action -> 'configuration -> 'configuration -> bool)
    (Z :'propvar)
    (V :'propvar -> 'configuration set)
    (form :('action, 'propvar) hmlForm)
     =
  gfp  (satFun Trans Z V form)`;

(* ========================================= *)
(* show that hmGFP is a greatest fixed point *)
(* ========================================= *)
val hmGFP_fixedpoint =
TAC_PROOF(([],``!Trans Z V form.(hmGFP Trans Z V form = satFun Trans Z V form (hmGFP Trans Z V form)) /\
  !X.((X = (satFun Trans Z V form X)) ==> (X SUBSET (hmGFP Trans Z V form)))``),
(PROVE_TAC[hmGFP_def,gfp_greatest_fixedpoint,satFun_monotone]));

val _ = save_thm("hmGFP_fixedpoint",hmGFP_fixedpoint);

val _ = print_theory "-";
val _ = export_theory();

end;