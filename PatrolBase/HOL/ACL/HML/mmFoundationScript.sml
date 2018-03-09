(* Modal Mu Calculus foundation with variables by SK Chin 30 May 2012 *)

(* Interactive Mode
app load ["pred_setTheory","pred_setLib","fixedPointTheory","mmFoundationTheory"];
open pred_setTheory pred_setLib fixedPointTheory mmFoundationTheory;
*)
(* Modal Mu Syntax *)

structure mmFoundationScript = struct

open HolKernel boolLib Parse; 
open bossLib pred_setTheory pred_setLib fixedPointTheory;

val _ = new_theory "mmFoundation";

(* Syntax of HML *)
val _ = Hol_datatype
    `mmForm = tt 
             | ff
	     | propmm of 'propvar
             | andmm of mmForm => mmForm 
             | ormm of mmForm => mmForm
             | Box of 'action set => mmForm
             | Dia of 'action set => mmForm
	     | nu of 'propvar => mmForm
	     | mu of 'propvar => mmForm`;

(* make andmm and ormm infix operators *)
val _ = set_fixity "andmm" (Infixr 580);
val _ = set_fixity "ormm" (Infixr 570);

(* Update function for valuations *)
val mmUpdate_def =
Define
`mmUpdate (Z:'propvar)(V:'propvar -> 'configuration set)(E:'configuration set)(Y:'propvar) =
 if Y=Z then E else V Y`;

(* Semantics of mmsat *)
val _ = set_fixity "mmsat" (Infixr 540);

val mmsat_def =
    Define
    `((((E:'configuration),(Trans:'action -> 'configuration -> 'configuration -> bool),(V:'propvar -> 'configuration set)) mmsat tt) = T) /\
     ((((E:'configuration),(Trans:'action -> 'configuration -> 'configuration -> bool),(V:'propvar -> 'configuration set)) mmsat ff) = F) /\
     ((((E:'configuration),(Trans:'action -> 'configuration -> 'configuration -> bool),(V:'propvar -> 'configuration set)) mmsat (propmm Z)) 
      = (E IN (V Z))) /\
     ((((E:'configuration),(Trans:'action -> 'configuration -> 'configuration -> bool),(V:'propvar -> 'configuration set)) mmsat 
      (f1:('action,'propvar) mmForm) andmm (f2:('action,'propvar) mmForm)) = (((E,Trans,V) mmsat f1) /\ (((E,Trans,V) mmsat f2)))) /\
     ((((E:'configuration),(Trans:'action -> 'configuration -> 'configuration -> bool),(V:'propvar -> 'configuration set)) mmsat 
      (f1:('action,'propvar) mmForm) ormm (f2:('action,'propvar) mmForm)) = (((E,Trans,V) mmsat f1) \/ (((E,Trans,V) mmsat f2)))) /\
     ((((E:'configuration),(Trans:'action -> 'configuration -> 'configuration -> bool),(V:'propvar -> 'configuration set)) mmsat 
      (Box (Actions:'action set)(f:('action,'propvar) mmForm))) = 
      (!(E':'configuration)(a:'action).(Trans a E E') ==> ((a IN Actions) ==> ((E',Trans,V) mmsat f)))) /\
     ((((E:'configuration),(Trans:'action -> 'configuration -> 'configuration -> bool),(V:'propvar -> 'configuration set)) mmsat 
      (Dia (Actions:'action set)(f:('action,'propvar) mmForm))) = 
      (?(E':'configuration)(a:'action).(Trans a E E') /\ ((a IN Actions) /\ ((E',Trans,V) mmsat f)))) /\
(* == use definition without mmfn ==    ((((E:'configuration),(Trans:'action -> 'configuration -> 'configuration -> bool),(V:'propvar -> 'configuration set)) mmsate(REWRITE_TAC[mmUpdate_e(REWRITE_TAC[mmUpdate_def]);def]);
      (nu (Z:'propvar)(f:('action,'propvar) mmForm))) = (E IN gfp \setE.{s | (s,Trans,(mmUpdate Z V setE)) mmsat f})) /\ *)
      ((((E:'configuration),(Trans:'action -> 'configuration -> 'configuration -> bool),(V:'propvar -> 'configuration set)) mmsat
      (nu (Z:'propvar)(f:('action,'propvar) mmForm))) = (?(setE:'configuration set).E IN setE /\ !(E':'configuration).E' IN setE ==> (E',Trans, (mmUpdate Z V setE)) mmsat f)) /\
(* == use definition without mmfn ==      ((((E:'configuration),(Trans:'action -> 'configuration -> 'configuration -> bool),(V:'propvar -> 'configuration set)) mmsat
      (mu (Z:'propvar)(f:('action,'propvar) mmForm))) = (E IN lfp \setE.{s | (s,Trans,(mmUpdate Z V setE)) mmsat f})) *)
((((E:'configuration),(Trans:'action -> 'configuration -> 'configuration -> bool),(V:'propvar -> 'configuration set)) mmsat
      (mu (Z:'propvar)(f:('action,'propvar) mmForm))) = (!(setE:'configuration set).(~(E IN setE)) ==> (?(E':'configuration).((E',Trans,(mmUpdate Z V setE)) mmsat f /\ (E' NOTIN setE)))))`; 


(********************************************************************)
(* Meaning function for formulas given a transition relation Trans, *)
(* set of processes E, and a valuation function V.                  *)
(* UNIV:('configuration set) corresponds to the universe of process *)
(* names in Section 1.6 of Colin Stirling's book Modal and Temporal *)
(* Properties of Processes.                                         *)
(********************************************************************)
val mmfn_def =
Define
`mmfn 
 (Trans:'action -> 'configuration -> 'configuration -> bool)
 (f:('action,'propvar) mmForm)
 (E:'configuration set)
 (V:'propvar -> 'configuration set)
  = {s | s ∈ E ∧ (s,Trans,V) mmsat f}`;

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
(* SOME PROPERTIES OF mmfn WITH RESPECT TO PREDICATE SETS *)
(* ====================================================== *)
val mmsat_IN_CLAUSES =
TAC_PROOF(([],
``(!(s:'configuration)(form:('action,'propvar)mmForm)(V:'propvar -> 'configuration set)
   (Trans:'action -> 'configuration -> 'configuration -> bool).
   {s | (s,Trans,V) mmsat form} = {s | s IN \x.(x,Trans,V) mmsat form}) /\
  (!(s:'configuration)(f1:('action,'propvar)mmForm)(f2:('action,'propvar)mmForm)
    (V:'propvar -> 'configuration set).
   {s | (s,Trans,V) mmsat f1 /\ (s,Trans,V) mmsat f2} = 
   {s | (s IN \x.((x,Trans,V) mmsat f1)) /\ (s IN (\x.(x,Trans,V) mmsat f2))}) /\
  (!(s:'configuration)(f1:('action,'propvar)mmForm)(f2:('action,'propvar)mmForm)
    (V:'propvar -> 'configuration set).
   {s | (s,Trans,V) mmsat f1 \/ (s,Trans,V) mmsat f2} = 
   {s | (s IN \x.((x,Trans,V) mmsat f1)) \/ (s IN \x.((x,Trans,V) mmsat f2))})``),
 (REWRITE_TAC[IN_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[]));

val _ = save_thm("mmsat_IN_CLAUSES",mmsat_IN_CLAUSES);

val mmfn_CLAUSES =
TAC_PROOF(([],
 ``(!(f1:('action,'propvar)mmForm)(f2:('action,'propvar)mmForm)
   (V:'propvar -> 'configuration set)
   (Trans:'action -> 'configuration -> 'configuration -> bool).
   (mmfn Trans (f1 andmm f2) (UNIV:'configuration set) V) =
   ((mmfn Trans f1 UNIV V) INTER (mmfn Trans f2 UNIV V))) /\
   (!(f1:('action,'propvar)mmForm)(f2:('action,'propvar)mmForm)
   (V:'propvar -> 'configuration set)
   (Trans:'action -> 'configuration -> 'configuration -> bool).
   (mmfn Trans (f1 ormm f2) (UNIV:'configuration set) V) =
   ((mmfn Trans f1 UNIV V) UNION (mmfn Trans f2 UNIV V)))``),
 (REPEAT STRIP_TAC THEN
  REWRITE_TAC[mmfn_def,mmsat_def,IN_UNIV] THEN
  REWRITE_TAC[mmsat_IN_CLAUSES] THEN
  REWRITE_TAC[INTER_DEF, UNION_DEF, GSPEC_ID]));

val _ = save_thm("mmfn_CLAUSES",mmfn_CLAUSES);

val box_lemma1 =
TAC_PROOF(([],``{s |
     !(E' :'configuration) (a :'action).
       (Trans :'action -> 'configuration -> 'configuration -> bool) a s
         E' ==>
       a IN (f :'action -> bool) ==>
       (E',Trans,(V :'propvar -> 'configuration -> bool)) mmsat
       (form :('action, 'propvar) mmForm)} =
  {s | s IN \s.(!(E' :'configuration) (a :'action).
       (Trans :'action -> 'configuration -> 'configuration -> bool) a s
         E' ==>
       a IN (f :'action -> bool) ==>
       (E',Trans,(V :'propvar -> 'configuration -> bool)) mmsat
       (form :('action, 'propvar) mmForm))}``),
 (REWRITE_TAC[IN_DEF] THEN
  CONV_TAC(DEPTH_CONV(BETA_CONV)) THEN
  REWRITE_TAC[]));
val box_lemma2 =
TAC_PROOF(([],``(\s.(!E' a. Trans a s E' ==> a IN f ==> (E',Trans,V) mmsat form)) = (\s.(!E' a. Trans a s E' /\ a IN f ==> (E',Trans,V) mmsat form))``),
 (REPEAT STRIP_TAC THEN
  REWRITE_TAC[AND_IMP_INTRO]));


(* ======================================== *)
(* Beginning of proofs of mmfn monotonicity *)
(* ======================================== *)

(* =============================== *)
(* mmfn is monotonic wrt tt and ff *)
(* =============================== *)
val mmfn_tt_ff_CLAUSES =
TAC_PROOF(([],
 ``(!(Trans:'action -> 'configuration -> 'configuration -> bool)
     (V:'propvar -> 'configuration set)(V':'propvar -> 'configuration set).
      (mmfn Trans tt (UNIV:'configuration set) V) SUBSET (mmfn Trans tt (UNIV:'configuration set) V')) /\ 
   (!(Trans:'action -> 'configuration -> 'configuration -> bool)
     (V:'propvar -> 'configuration set)(V':'propvar -> 'configuration set).
      (mmfn Trans ff (UNIV:'configuration set) V) SUBSET (mmfn Trans ff (UNIV:'configuration set) V'))``),
 (REWRITE_TAC[mmfn_def,IN_UNIV] THEN
  REWRITE_TAC[mmsat_def,SUBSET_REFL]));

val _ = save_thm("mmfn_tt_ff_CLAUSES",mmfn_tt_ff_CLAUSES);

(* ================================================== *)
(* HMFn is monotonic on V wrt propositional variables *)
(* ================================================== *)
val mmfn_MONOTONIC_propvar =
TAC_PROOF(([],
``!(Z:'propvar)(V:'propvar -> 'configuration set)(V':'propvar -> 'configuration set). extends V V' ==>  
   ((mmfn (Trans:'action -> 'configuration -> 'configuration -> bool) 
          (propmm (Z:'propvar))
	  (UNIV:'configuration set) 
          (V:'propvar -> 'configuration set)) SUBSET 
    (mmfn (Trans:'action -> 'configuration -> 'configuration -> bool) 
    	  (propmm (Z:'propvar))
          (UNIV:'configuration set) 
          (V':'propvar -> 'configuration set)))``),
 (REPEAT GEN_TAC THEN
  REWRITE_TAC[extends_def, mmfn_def,IN_UNIV] THEN
  REWRITE_TAC[mmsat_def,IN_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[GSPEC_ETA] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC[]));

val _ =
save_thm("mmfn_MONOTONIC_propvar",mmfn_MONOTONIC_propvar);

(* ==================================== *)
(* Proof that mmfn is monotonic on andmm *)
(* ==================================== *)

val mmfn_MONOTONIC_andmm =
TAC_PROOF(([],
``(!(V :'propvar -> 'configuration -> bool)
        (V' :'propvar -> 'configuration -> bool).
       extends V V' ==>
       mmfn (Trans :'action -> 'configuration -> 'configuration -> bool)
         (form :('action, 'propvar) mmForm)
         univ((:'configuration) :'configuration itself) V SUBSET
       mmfn Trans form univ((:'configuration) :'configuration itself)
         V') ==>
    (!(V :'propvar -> 'configuration -> bool)
        (V' :'propvar -> 'configuration -> bool).
       extends V V' ==>
       mmfn Trans (form' :('action, 'propvar) mmForm)
         univ((:'configuration) :'configuration itself) V SUBSET
       mmfn Trans form' univ((:'configuration) :'configuration itself)
         V') ==>
    extends (V :'propvar -> 'configuration -> bool)
      (V' :'propvar -> 'configuration -> bool) ==>
    mmfn Trans form univ((:'configuration) :'configuration itself) V INTER
    mmfn Trans form' univ((:'configuration) :'configuration itself) V SUBSET
    mmfn Trans form univ((:'configuration) :'configuration itself) V' INTER
    mmfn Trans form' univ((:'configuration) :'configuration itself) V'``),
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

val _ = save_thm("mmfn_MONOTONIC_andmm",mmfn_MONOTONIC_andmm);
(* =================================== *)
(* Proof that mmfn is monotonic on ormm *)
(* =================================== *)
val mmfn_MONOTONIC_ormm =
TAC_PROOF(([],
``(!(V :'propvar -> 'configuration -> bool)
        (V' :'propvar -> 'configuration -> bool).
       extends V V' ==>
       mmfn (Trans :'action -> 'configuration -> 'configuration -> bool)
         (form :('action, 'propvar) mmForm)
         univ((:'configuration) :'configuration itself) V SUBSET
       mmfn Trans form univ((:'configuration) :'configuration itself)
         V') ==>
    (!(V :'propvar -> 'configuration -> bool)
        (V' :'propvar -> 'configuration -> bool).
       extends V V' ==>
       mmfn Trans (form' :('action, 'propvar) mmForm)
         univ((:'configuration) :'configuration itself) V SUBSET
       mmfn Trans form' univ((:'configuration) :'configuration itself)
         V') ==>
    extends (V :'propvar -> 'configuration -> bool)
      (V' :'propvar -> 'configuration -> bool) ==>
    mmfn Trans form univ((:'configuration) :'configuration itself) V UNION
    mmfn Trans form' univ((:'configuration) :'configuration itself) V SUBSET
    mmfn Trans form univ((:'configuration) :'configuration itself) V' UNION
    mmfn Trans form' univ((:'configuration) :'configuration itself) V'``),
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

val _ = save_thm("mmfn_MONOTONIC_ormm",mmfn_MONOTONIC_ormm);

(* Some conversions we will use for Box and Dia proofs *)
val th1 =
SET_SPEC_CONV
``x IN {s |
        (s,(Trans :'action -> 'configuration -> 'configuration -> bool),
         (V :'propvar -> 'configuration -> bool)) mmsat
        (form :('action, 'propvar) mmForm)}``;
val th2 =
SET_SPEC_CONV
``x IN
       {s |
        (s,Trans,(V' :'propvar -> 'configuration -> bool)) mmsat form}``;
val th3 =
SET_SPEC_CONV
``x IN
      {s |
       !(E' :'configuration) (a :'action).
         Trans a s E' ==>
         a IN (f :'action -> bool) ==>
         (E',Trans,V) mmsat form}``;

val th4 =
SET_SPEC_CONV
``x IN
      {s |
       !(E' :'configuration) (a :'action).
         Trans a s E' ==> a IN f ==> (E',Trans,V') mmsat form}``;

(* =========================== *)
(* Proof that Box is monotonic *)
(* =========================== *)

val mmfn_MONOTONIC_Box =
TAC_PROOF(([],
``(!(V :'propvar -> 'configuration -> bool)
        (V' :'propvar -> 'configuration -> bool).
       extends V V' ==>
       mmfn (Trans :'action -> 'configuration -> 'configuration -> bool)
         (form :('action, 'propvar) mmForm)
         univ((:'configuration) :'configuration itself) V SUBSET
       mmfn Trans form univ((:'configuration) :'configuration itself)
         V') ==>
    extends (V :'propvar -> 'configuration -> bool)
      (V' :'propvar -> 'configuration -> bool) ==>
    mmfn Trans (Box (f :'action -> bool) form)
      univ((:'configuration) :'configuration itself) V SUBSET
    mmfn Trans (Box f form) univ((:'configuration) :'configuration itself)
      V'``),
(REWRITE_TAC[mmfn_MONOTONIC_propvar, mmfn_tt_ff_CLAUSES,mmfn_CLAUSES] THEN
(* move extends V V' into assumptions and do resolution *)
  REPEAT DISCH_TAC THEN 
  RES_TAC THEN
(* remove extends V V' from subgoal assumption list                  *)
(* and remove one extends V V'==> term from subgoal assumption list *)
  PAT_ASSUM ``extends A B`` (fn th => ALL_TAC) THEN
  PAT_ASSUM ``!V V'.extends A B ==> term`` (fn th => ALL_TAC) THEN UNDISCH_TAC
``mmfn (Trans :'action -> 'configuration -> 'configuration -> bool)
        (form :('action, 'propvar) mmForm)
        univ((:'configuration) :'configuration itself)
        (V :'propvar -> 'configuration -> bool) SUBSET
      mmfn Trans form univ((:'configuration) :'configuration itself)
        (V' :'propvar -> 'configuration -> bool)`` THEN
REWRITE_TAC[SUBSET_DEF,mmfn_def,mmsat_def,IN_UNIV,th1,th2,th3,th4] THEN
REPEAT STRIP_TAC THEN
REPEAT RES_TAC));

val _ = save_thm("mmfn_MONOTONIC_Box",mmfn_MONOTONIC_Box);

(* =========================== *)
(* Proof that Dia is monotonic *)
(* =========================== *)
val th5 =
SET_SPEC_CONV
``x IN
      {s |
       ?(E' :'configuration) (a :'action).
         Trans a s E' /\ a IN (f :'action -> bool) /\
         (E',Trans,V) mmsat form}``;

val th6 =
SET_SPEC_CONV
``x IN
      {s |
       ?(E' :'configuration) (a :'action).
         Trans a s E' /\ a IN f /\ (E',Trans,V') mmsat form}``;

val mmfn_MONOTONIC_Dia =
TAC_PROOF(([],
``(!(V :'propvar -> 'configuration -> bool)
        (V' :'propvar -> 'configuration -> bool).
       extends V V' ==>
       mmfn (Trans :'action -> 'configuration -> 'configuration -> bool)
         (form :('action, 'propvar) mmForm)
         univ((:'configuration) :'configuration itself) V SUBSET
       mmfn Trans form univ((:'configuration) :'configuration itself)
         V') ==>
    extends (V :'propvar -> 'configuration -> bool)
      (V' :'propvar -> 'configuration -> bool) ==>
    mmfn Trans (Dia (f :'action -> bool) form)
      univ((:'configuration) :'configuration itself) V SUBSET
    mmfn Trans (Dia f form) univ((:'configuration) :'configuration itself)
      V'``),
(REWRITE_TAC[mmfn_MONOTONIC_propvar, mmfn_tt_ff_CLAUSES,mmfn_CLAUSES] THEN
(* move extends V V' into assumptions and do resolution *)
  REPEAT DISCH_TAC THEN 
  RES_TAC THEN
(* remove extends V V' from subgoal assumption list                  *)
(* and remove one extends V V'==> term from subgoal assumption list *)
  PAT_ASSUM ``extends A B`` (fn th => ALL_TAC) THEN
  PAT_ASSUM ``!V V'.extends A B ==> term`` (fn th => ALL_TAC) THEN UNDISCH_TAC
``mmfn (Trans :'action -> 'configuration -> 'configuration -> bool)
        (form :('action, 'propvar) mmForm)
        univ((:'configuration) :'configuration itself)
        (V :'propvar -> 'configuration -> bool) SUBSET
      mmfn Trans form univ((:'configuration) :'configuration itself)
        (V' :'propvar -> 'configuration -> bool)`` THEN
REWRITE_TAC[SUBSET_DEF,mmfn_def,mmsat_def,IN_UNIV,th1,th2,th5,th6] THEN
 REPEAT STRIP_TAC THEN
 EXISTS_TAC ``(E' :'configuration)`` THEN
 EXISTS_TAC ``(a :'action)`` THEN
 RES_TAC THEN
 ASM_REWRITE_TAC[]));

val _ = save_thm("mmfn_MONOTONIC_Dia",mmfn_MONOTONIC_Dia);

(* ======================== *)
(* Monotonicity of mmUpdate *)
(* ======================== *)
val mmUpdate_MONOTONIC =
TAC_PROOF(([],``(!(V:'propvar -> 'configuration set)
   (Z:'propvar)(E:'configuration set)(F:'configuration set).
   (E SUBSET F) ==> (extends (mmUpdate Z V E)(mmUpdate Z V F))) /\
   (!(V:'propvar -> 'configuration set)(V':'propvar -> 'configuration set)
   (Z:'propvar)(E:'configuration set).
   (extends V V') ==> (extends (mmUpdate Z V E)(mmUpdate Z V' E)))``),
(CONJ_TAC THEN
 REWRITE_TAC[SUBSET_DEF,extends_def,mmUpdate_def,SPECIFICATION] THEN
 REPEAT GEN_TAC THEN
 DISCH_TAC THEN
 REPEAT GEN_TAC THEN
 COND_CASES_TAC THEN
 ASM_REWRITE_TAC[]));

val _ = save_thm("mmUpdate_MONOTONIC",mmUpdate_MONOTONIC);

(* Some clauses we need in the nu and mu proofs *)

val th1 =
SET_SPEC_CONV 
`` x IN
        {s |
         ?(setE :'configuration -> bool).
           s IN setE /\
           !(E' :'configuration).
             E' IN setE ==>
             (E',(Trans :'a -> 'configuration -> 'configuration -> bool),
              mmUpdate (p :'propvar) V setE) mmsat
             (form :('a, 'propvar) mmForm)}``;

val th2 =
SET_SPEC_CONV
``x IN
        {s |
         ?(setE :'configuration -> bool).
           s IN setE /\
           !(E' :'configuration).
             E' IN setE ==> (E',Trans,mmUpdate p V' setE) mmsat form}``;

val th3 =
SET_SPEC_CONV
``E' IN
            {s |
             (s,
              (Trans :'action -> 'configuration -> 'configuration -> bool),
              mmUpdate (p :'propvar) (V :'propvar -> 'configuration -> bool)
                (setE :'configuration -> bool)) mmsat
             (form :('action, 'propvar) mmForm)}``;

val th4 =
SET_SPEC_CONV
``E' IN
            {s |
             (s,Trans,
              mmUpdate p (V' :'propvar -> 'configuration -> bool)
                setE) mmsat form}``;

(* ========================== *)
(* Proof that nu is monotonic *)
(* ========================== *)
val mmfn_MONOTONIC_nu =
TAC_PROOF(([],
``(!(V :'propvar -> 'configuration -> bool)
        (V' :'propvar -> 'configuration -> bool).
       extends V V' ==>
       mmfn (Trans :'action -> 'configuration -> 'configuration -> bool)
         (form :('action, 'propvar) mmForm)
         univ((:'configuration) :'configuration itself) V SUBSET
       mmfn Trans form univ((:'configuration) :'configuration itself)
         V') ==>
    extends (V :'propvar -> 'configuration -> bool)
      (V' :'propvar -> 'configuration -> bool) ==>
    mmfn Trans (nu (p :'propvar) form)
      univ((:'configuration) :'configuration itself) V SUBSET
    mmfn Trans (nu p form) univ((:'configuration) :'configuration itself) V'``),
 (REPEAT DISCH_TAC THEN
  REWRITE_TAC[mmfn_def,mmsat_def,IN_UNIV,SUBSET_DEF,th1,th2] THEN
  REPEAT STRIP_TAC THEN
  EXISTS_TAC ``setE:'configuration set`` THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT STRIP_TAC THEN
  PAT_ASSUM 
  ``!V V'.extends V V' ==> (A SUBSET B)`` 
  (fn th => 
    ASSUME_TAC
    (ISPECL 
     [``mmUpdate (p:'propvar) (V:'propvar -> 'configuration set) (setE:'configuration set)``,
      ``mmUpdate (p:'propvar) (V':'propvar -> 'configuration set) (setE:'configuration set)``] th)) THEN
  PAT_ASSUM
  ``extends V V'``
  (fn th => 
   ASSUME_TAC 
   (MP 
    (ISPECL 
     [``V:'propvar -> 'configuration set``,``V':'propvar -> 'configuration set``,
      ``p:'propvar``,``setE:'configuration set``](CONJUNCT2 mmUpdate_MONOTONIC)) th)) THEN
  PAT_ASSUM
  ``extends A B ==> (C SUBSET D)``
  (fn th1 =>
   (PAT_ASSUM
    ``extends A B``
    (fn th2 => ASSUME_TAC(MP th1 th2)))) THEN
  PAT_ASSUM
  ``A SUBSET B``
  (fn th => ASSUME_TAC(REWRITE_RULE[SUBSET_DEF,mmfn_def,IN_UNIV] th)) THEN
  PAT_ASSUM
  ``!x.(x IN A) ==> (x IN B)``
  (fn th => ASSUME_TAC(REWRITE_RULE[th3,th4](SPEC ``E':'configuration`` th))) THEN
  PROVE_TAC []));

val _ = save_thm("mmfn_MONOTONIC_nu",mmfn_MONOTONIC_nu);

(* ========================== *)
(* Proof that mu is monotonic *)
(*=========================== *)
(* =================== *)
(* Some helpful lemmas *)
(* =================== *)
val th1 =
SET_SPEC_CONV
``x IN
      {s |
       !(setE :'configuration -> bool).
         s NOTIN setE ==>
         ?(E' :'configuration).
           (E',(Trans :'action -> 'configuration -> 'configuration -> bool),
            mmUpdate (p :'propvar) (V :'propvar -> 'configuration -> bool)
              setE) mmsat (form :('action, 'propvar) mmForm) /\
           E' NOTIN setE}``;

val th2 =
SET_SPEC_CONV
``x IN
      {s |
       !(setE :'configuration -> bool).
         s NOTIN setE ==>
         ?(E' :'configuration).
           (E',Trans,
            mmUpdate p (V' :'propvar -> 'configuration -> bool) setE) mmsat
           form /\ E' NOTIN setE}``;

val th3 =
SET_SPEC_CONV
``x IN {s | (s,
              (Trans :'action -> 'configuration -> 'configuration -> bool),
              mmUpdate (p :'propvar) (V :'propvar -> 'configuration -> bool)
                (setE :'configuration -> bool)) mmsat
             (form :('action, 'propvar) mmForm)}``;

val th4 =
SET_SPEC_CONV 
``x IN {s | (s,Trans,
              mmUpdate p (V' :'propvar -> 'configuration -> bool)
                setE) mmsat form}``;

val th5 = 
SET_SPEC_CONV
``x IN {s | (s,(Trans : 'action -> 'configuration -> 'configuration -> bool), V) mmsat (form :('action, 'propvar) mmForm)}``;

val th6 =
SET_SPEC_CONV
``x IN {s | (s,(Trans : 'action -> 'configuration -> 'configuration -> bool), V') mmsat (form :('action, 'propvar) mmForm)}``;

val th7 =
TAC_PROOF(([],
``(!(setE :'configuration -> bool).
       (x :'configuration) NOTIN setE ==>
       ?(E' :'configuration).
         (E',(Trans :'action -> 'configuration -> 'configuration -> bool),
          mmUpdate (p :'propvar) (V :'propvar -> 'configuration -> bool)
            setE) mmsat (form :('action, 'propvar) mmForm) /\
         E' NOTIN setE) =
   (!(setE :'configuration -> bool).
    (!E'.((E',Trans,mmUpdate p V setE) mmsat form) ==> (E' IN setE)) ==> x IN setE)``),
(PROVE_TAC []));

val mmfn_MONOTONIC_mu =
TAC_PROOF(([],
``    (!(V :'propvar -> 'configuration -> bool)
        (V' :'propvar -> 'configuration -> bool).
       extends V V' ==>
       mmfn (Trans :'action -> 'configuration -> 'configuration -> bool)
         (form :('action, 'propvar) mmForm)
         univ((:'configuration) :'configuration itself) V SUBSET
       mmfn Trans form univ((:'configuration) :'configuration itself)
         V') ==>
    extends (V :'propvar -> 'configuration -> bool)
      (V' :'propvar -> 'configuration -> bool) ==>
    mmfn Trans (mu (p :'propvar) form)
      univ((:'configuration) :'configuration itself) V SUBSET
    mmfn Trans (mu p form) univ((:'configuration) :'configuration itself) V'``),
((* Simplify all terms to remove set abstractions *)
  REWRITE_TAC[mmfn_def,mmsat_def,IN_UNIV,SUBSET_DEF,th1,th2,th3,th4,th5,th6] THEN
  REPEAT DISCH_TAC THEN
  GEN_TAC THEN
  REWRITE_TAC[th7] THEN
  REPEAT STRIP_TAC THEN
(* Set up the inductive hypothesis by using mmUpdate p V setE for V *)
(* mmUpdate p V' setE for V'                                        *)
  PAT_ASSUM
  ``!V V'.extends V V' ==> A``
  (fn th =>
   ASSUME_TAC
   (ISPECL 
    [``mmUpdate (p:'propvar) (V:'propvar -> 'configuration set) (setE:'configuration set)``,
     ``mmUpdate (p:'propvar) (V':'propvar -> 'configuration set) (setE:'configuration set)``]
    th)) THEN
(* Prove extends (mmUpdate p V setE) (mmUpdate p V' setE) using *)
(* second clause of mmUpdate_MONOTONIC and the assumption       *)
(* extends V V'                                                 *)
  PAT_ASSUM
  ``extends V V'``
  (fn th =>
   ASSUME_TAC
   (MP 
    (ISPECL
     [``V:'propvar -> 'configuration set``,``V':'propvar -> 'configuration set``,
      ``p:'propvar``,``setE:'configuration set``]
     (CONJUNCT2 mmUpdate_MONOTONIC))
   th)) THEN
  PROVE_TAC[]));

val _ = save_thm("mmfn_MONOTONIC_mu",mmfn_MONOTONIC_mu);

(* =================================== *)
(* Final proof putting it all together *)
(* =================================== *)
val mmfn_MONOTONIC =
TAC_PROOF(([],
``!(form:('action,'propvar)mmForm)(V:'propvar -> 'configuration set)(V':'propvar -> 'configuration set). extends V V' ==>  
   ((mmfn (Trans:'action -> 'configuration -> 'configuration -> bool) 
          form
	  (UNIV:'configuration set) 
          (V:'propvar -> 'configuration set)) SUBSET 
    (mmfn (Trans:'action -> 'configuration -> 'configuration -> bool) 
    	  form
          (UNIV:'configuration set) 
          (V':'propvar -> 'configuration set)))``),
 (Induct THEN
(* Proof of tt, ff, propvar *)
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mmfn_MONOTONIC_propvar, mmfn_tt_ff_CLAUSES,mmfn_CLAUSES] THEN
(* Proof of the remaining cases *)
  PROVE_TAC[mmfn_MONOTONIC_andmm,mmfn_MONOTONIC_ormm,mmfn_MONOTONIC_Box,
            mmfn_MONOTONIC_Dia,mmfn_MONOTONIC_nu,mmfn_MONOTONIC_mu]));

val _ = save_thm("mmfn_MONOTONIC",mmfn_MONOTONIC);

(* Define f[phi,Z](E) in Stirling p.93 *)
val satFun_def =
    Define
    `satFun 
     (Trans:'action -> 'configuration -> 'configuration -> bool)
     (Z:'propvar)(V:'propvar -> 'configuration set)
     (form:('action,'propvar)mmForm)(E:'configuration set) =
     (mmfn 
      Trans form(UNIV:'configuration set)(mmUpdate Z V E))`;

(* =========================== *)
(* Corollary 1: p. 94 Stirling *)
(* =========================== *)
val satFun_MONOTONIC =
TAC_PROOF(([],``!(V:'propvar -> 'configuration set)
   (Trans:'action -> 'configuration -> 'configuration -> bool)
   (Z:'propvar)(form:('action,'propvar)mmForm)
   (E1:'configuration set)(E2:'configuration set).
   (E1 SUBSET E2) ==> 
   ((satFun Trans Z V form E1) SUBSET (satFun Trans Z V form E2))``),
(REWRITE_TAC[satFun_def] THEN
 REPEAT STRIP_TAC THEN
 IMP_RES_TAC mmUpdate_MONOTONIC THEN
 PAT_ASSUM ``!x.P`` (fn th => ASSUME_TAC (SPEC_ALL th)) THEN
 IMP_RES_TAC
 (ISPECL
  [``form:('action,'propvar)mmForm``,
   ``(mmUpdate (Z :'propvar) (V :'propvar -> 'configuration set)(E1 :'configuration set))``,
   ``(mmUpdate (Z :'propvar) (V :'propvar -> 'configuration set)(E2 :'configuration set))``]
   mmfn_MONOTONIC) THEN
 ASM_REWRITE_TAC[]));

val _ = save_thm("satFun_MONOTONIC",satFun_MONOTONIC);

val satFun_gfp_thm =
TAC_PROOF(([],
``gfp (satFun 
  (Trans:'action -> 'configuration -> 'configuration -> bool) 
  (Z:'propvar)
  (V:'propvar -> 'configuration set)
  (f:('action,'propvar)mmForm))
  =
  BIGUNION {setE | setE SUBSET (satFun 
  (Trans:'action -> 'configuration -> 'configuration -> bool) 
  (Z:'propvar)
  (V:'propvar -> 'configuration set)
  (f:('action,'propvar)mmForm)
  (setE:'configuration set))}``),
  REWRITE_TAC[gfp_def]);

val _ = save_thm("satFun_gfp_thm",satFun_gfp_thm);

val th1 =
SET_SPEC_CONV
``x IN {s | (s,Trans,mmUpdate Z V X) mmsat f}``;

val th2 =
SET_SPEC_CONV
``x IN {s | (s,Trans,mmUpdate Z V X) mmsat f}``;

val th3 =
SET_SPEC_CONV
``s IN {X | !x. x ∈ X ⇒ (x,Trans,mmUpdate Z V X) mmsat f}``;

val th4 =
SET_SPEC_CONV
``E IN {x | ?s. (!x. x IN s ⇒ (x,Trans,mmUpdate Z V s) mmsat f) ∧ x IN s}``;

val mmsat_nu_gfp =
TAC_PROOF(([],
``!(f :('action, 'propvar) mmForm) (Z :'propvar)
          (V :'propvar -> 'configuration -> bool)
          (Trans :'action -> 'configuration -> 'configuration -> bool)
          (E :'configuration).
         (((E,Trans,V) mmsat nu Z f) = 
         E IN (gfp (satFun 
  (Trans:'action -> 'configuration -> 'configuration -> bool) 
  (Z:'propvar)
  (V:'propvar -> 'configuration set)
  (f:('action,'propvar)mmForm))))``),
 (REWRITE_TAC
  [mmsat_def,satFun_def,mmfn_def,IN_UNIV,gfp_def,BIGUNION,SUBSET_DEF,
   th1,th2,th3,th4] THEN
  REPEAT STRIP_TAC THEN 
  EQ_TAC THEN
  REPEAT STRIP_TAC THENL
  [(* First subgoal: set s = setE *)
   (EXISTS_TAC``setE:'configuration set`` THEN
    REPEAT STRIP_TAC THEN 
    ASM_REWRITE_TAC [] THEN
    PAT_ASSUM
     ``!(E':'configuration).A``
     (fn th => ASSUME_TAC(SPEC ``x:'configuration`` th)) THEN
    RES_TAC),
    (* Second subgoal: setE = s *)
    (EXISTS_TAC ``s:'configuration set`` THEN
     ASM_REWRITE_TAC[])]));

val _ = save_thm("mmsat_nu_gfp",mmsat_nu_gfp);

val satFun_lfp_thm =
TAC_PROOF(([],
``lfp (satFun 
  (Trans:'action -> 'configuration -> 'configuration -> bool) 
  (Z:'propvar)
  (V:'propvar -> 'configuration set)
  (f:('action,'propvar)mmForm))
  =
  BIGINTER {setE | (satFun 
  (Trans:'action -> 'configuration -> 'configuration -> bool) 
  (Z:'propvar)
  (V:'propvar -> 'configuration set)
  (f:('action,'propvar)mmForm)
  (setE:'configuration set)) SUBSET setE}``),
  REWRITE_TAC[lfp_def]);

val _ = save_thm("satFun_lfp_thm",satFun_lfp_thm);

val th1 =
SET_SPEC_CONV
``x IN {s | (s,Trans,mmUpdate Z V X) mmsat f}``;

val th2 =
SET_SPEC_CONV
``s IN {X | !x. (x,Trans,mmUpdate Z V X) mmsat f ==> x IN X}``;

val th3 =
SET_SPEC_CONV
``E IN {x | !s. (!x. (x,Trans,mmUpdate Z V s) mmsat f ⇒ x IN s) ==> x IN s}``;

val th4 =
let
 val th1 = NOT_EXISTS_CONV ``¬(∃E'. (E',Trans,mmUpdate Z V setE) mmsat f ∧ E' ∉ setE)``
in
REWRITE_RULE[GSYM IMP_DISJ_THM](
ONCE_REWRITE_RULE[DE_MORGAN_THM](REWRITE_RULE [th1]
(CONTRAPOS_CONV
``(E NOTIN setE ==> ?E'. ((E',Trans,mmUpdate Z V setE) mmsat f /\ E' NOTIN setE))``)))
end;

val th5 =
CONTRAPOS_CONV
``(!x. (x,Trans,mmUpdate Z V s) mmsat f ==> x IN s) ==> E IN s``;

val th6 =
REWRITE_RULE[CONJUNCT2(SPEC_ALL DE_MORGAN_THM)]
(NOT_FORALL_CONV
`` ¬!(x :'configuration).
             ~((x,
                (Trans :
                  'action -> 'configuration -> 'configuration -> bool),
                mmUpdate (Z :'propvar)
                  (V :'propvar -> 'configuration -> bool)
                  (setE :'configuration -> bool)) mmsat
               (f :('action, 'propvar) mmForm)) \/ x IN setE``);

val mmsat_mu_lfp =
TAC_PROOF(([],
``!(f :('action, 'propvar) mmForm) (Z :'propvar)
          (V :'propvar -> 'configuration -> bool)
          (Trans :'action -> 'configuration -> 'configuration -> bool)
          (E :'configuration).
         (((E,Trans,V) mmsat mu Z f) = 
         E IN (lfp (satFun 
  (Trans:'action -> 'configuration -> 'configuration -> bool) 
  (Z:'propvar)
  (V:'propvar -> 'configuration set)
  (f:('action,'propvar)mmForm))))``),
 (REWRITE_TAC
  [mmsat_def,satFun_def,mmfn_def,IN_UNIV,lfp_def,BIGINTER,SUBSET_DEF,
   th1,th2,th3] THEN
  REPEAT STRIP_TAC THEN 
  EQ_TAC THEN
  REPEAT STRIP_TAC THENL
  [(* First subgoal *)
   (PAT_ASSUM
    ``!setE. E NOTIN setE ==> P``
    (fn th =>
     ASSUME_TAC(REWRITE_RULE[th4] th)) THEN
    PAT_ASSUM
    ``!setE.(!E'.P) ==> E IN setE``
    (fn th =>
     ASSUME_TAC(ISPEC ``s:'configuration set`` th)) THEN
    RES_TAC),
    (* Second subgoal *)
    (PAT_ASSUM
     ``!s:'configuration set.P ==> E IN s``
     (fn th =>
      (ASSUME_TAC(REWRITE_RULE[th5](ISPEC ``setE:'configuration set`` th)))) THEN
     RES_TAC THEN
     PAT_ASSUM
     ``~!x.P ==> Q``
     (fn th => 
      ASSUME_TAC 
      (REWRITE_RULE[IMP_DISJ_THM] th)) THEN
     PAT_ASSUM
     ``~!x. ~((x,Trans,mmUpdate Z V setE) mmsat f) \/ x IN setE``
     (fn th =>
      REWRITE_TAC[REWRITE_RULE[th6] th]))]));

val _ = save_thm("mmsat_mu_lfp",mmsat_mu_lfp);


val _ = print_theory "-";
val _ = export_theory();

end;