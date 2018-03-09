(* Unfolding proposition p. 105 Stirling                       *)
(* Proof based on Byoung Woo Min's dissertation and HOL proofs *)
(* SK Chin 21 July 2012                                        *)

(* Interactive mode
app load ["pred_setTheory","pred_setLib","fixedPointTheory","listTheory","pairTheory",
          "pairLib","mmFoundationTheory", "tautLib", "Datatype","TotalDefn","numLib","combinTheory",
	  "arithmeticTheory","res_quanTheory","res_quanLib","Rsyntax","substitutionTheory"];
open bossLib pred_setTheory pred_setLib fixedPointTheory listTheory pairTheory pairLib mmFoundationTheory;
open tautLib Datatype TotalDefn numLib combinTheory arithmeticTheory res_quanTheory res_quanLib Rsyntax;
open substitutionTheory;
*)

structure substitutionScript = struct

open HolKernel boolLib Parse; 
open bossLib pred_setTheory pred_setLib fixedPointTheory listTheory pairTheory pairLib mmFoundationTheory;
open tautLib Datatype TotalDefn numLib combinTheory arithmeticTheory res_quanTheory res_quanLib Rsyntax;

val _ = new_theory "substitution";

(* === Opt not to alter definition convention of storing definitions with _def
val _ = Defn.def_suffix := ""; 
 === *)

(**********************************************************)
(* Defined by F. Lockwood Morris                          *)
(* Abbreviations [1st 2 also found in unit ante_allTacs]: *)
(**********************************************************)

val AR = ASM_REWRITE_TAC [];
fun ulist x = [x];
val FUN_EQ_TAC = CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC;

val COND_NOT = store_thm ("COND_NOT", Term
`!P (A:'a) B. (if ~P then A else B) = (if P then B else A)`,
REPEAT STRIP_TAC THEN Q_TAC ASM_CASES_TAC `P` THEN AR);

val COND_NOT_DISJ = store_thm ("COND_NOT_DISJ", Term`!P Q (A:'a) B.
       (if ~Q \/ P then A else B) = (if P then A else if Q then B else A)`,
REPEAT GEN_TAC THEN Q_TAC ASM_CASES_TAC `P`
THEN ASM_REWRITE_TAC [COND_NOT]);

val in_not_in_not_eq = store_thm ("in_not_in_not_eq", Term
`!X:'a Y s. X IN s /\ ~(Y IN s) ==> ~(X = Y)`,
REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC []
THEN DISCH_THEN SUBST1_TAC THEN TAUT_TAC);

val INSERT_INSERT_DELETE = store_thm ("INSERT_INSERT_DELETE", Term
`!a:'a t. a INSERT t DELETE a = a INSERT t`,
REPEAT GEN_TAC THEN REWRITE_TAC [EXTENSION, IN_INSERT, IN_DELETE]
THEN TAUT_TAC);

(****************************************************************)
(* Define size of formulas in terms of the number of components *)
(****************************************************************)
val fmla_size_def =
Define
`(fmla_size tt = 0) /\
 (fmla_size ff = 0) /\
 (fmla_size (propmm Z) = 1) /\
 (fmla_size (f1 andmm f2) = 1 + (fmla_size f1) + (fmla_size f2)) /\
 (fmla_size (f1 ormm f2) = 1 + (fmla_size f1) + (fmla_size f2)) /\
 (fmla_size (Box Actions f) = 1 + fmla_size f) /\
 (fmla_size (Dia Actions f) = 1 + fmla_size f) /\
 (fmla_size (nu Z f) = 1 + fmla_size f) /\
 (fmla_size (mu Z f) = 1 + fmla_size f)`;

(****************************************************************************)
(* following definition of "extend_env" uses abstract functions to serve as *)
(* valuations assigning process sets to variables; can be changed to suit   *)
(* if, say, a list representation is preferred.                             *)
(****************************************************************************)
val extend_env_def = Define
`extend_env (x:'a) (v:'b) f = (\y. if y = x then v else f y)`;

(*********************************)
(* Relate extend_env to mmUpdate *)
(*********************************)
val extend_env_mmUpdate_lemma =
TAC_PROOF
(([],``extend_env Z E V Y = mmUpdate Z V E Y``),
(REWRITE_TAC[extend_env_def,mmUpdate_def] THEN
 CONV_TAC(DEPTH_CONV BETA_CONV) THEN
 PROVE_TAC[]));

val _ = save_thm("extend_env_mmUpdate_lemma",extend_env_mmUpdate_lemma);

val extend_env_mmUpdate_EQ =
REWRITE_RULE[ETA_CONV``\Y.mmUpdate Z V E Y``]
(TAC_PROOF
(([],``extend_env Z E V = \Y. mmUpdate Z V E Y``),
 PROVE_TAC [extend_env_def,mmUpdate_def,extend_env_mmUpdate_lemma]));

val _ = save_thm("extend_env_mmUpdate_EQ",extend_env_mmUpdate_EQ);

val last_extension_counts = store_thm ("last_extension_counts", Term
`!x:'a v v':'p->bool f.
 extend_env x v (extend_env x v' f) = extend_env x v f`,
REPEAT GEN_TAC THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC
THEN REWRITE_TAC [extend_env_def] THEN BETA_TAC
THEN COND_CASES_TAC THEN REWRITE_TAC []);

val last_update_counts = 
let 
 val th1 = BETA_RULE(X_FUN_EQ_CONV ``Y:'a`` ``(\(Y :'a). mmUpdate x (\(Y :'a). mmUpdate x f v' Y) v Y) =
         (\(Y :'a). mmUpdate x f v Y)``)
 val th2 = BETA_RULE(BETA_RULE(REWRITE_RULE[extend_env_mmUpdate_EQ] last_extension_counts))
in
 REWRITE_RULE[th1]th2
end;

val _ = save_thm("last_update_counts",last_update_counts);

val uneq_extensions_commute = store_thm ("uneq_extensions_commute", Term
`!v w:'p->bool x y:'a f. ~(y = x) ==> (extend_env y w (extend_env x v f) =
                                       extend_env x v (extend_env y w f))`,
REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC
THEN REWRITE_TAC [extend_env_def] THEN BETA_TAC
THEN COND_CASES_TAC THEN AR);

val uneq_mmUpdates_commute =
let
 val th1 = BETA_RULE(X_FUN_EQ_CONV ``Y:'a`` ``((\(Y :'a). mmUpdate y (\(Y :'a). mmUpdate x f v Y) w Y) =
          (\(Y :'a). mmUpdate x (\(Y :'a). mmUpdate y f w Y) v Y))``)
 val th2 = REWRITE_RULE[extend_env_mmUpdate_EQ] uneq_extensions_commute
in
 REWRITE_RULE[th1] th2
end;

val _ = save_thm("uneq_mmUpdates_commute",uneq_mmUpdates_commute);

(* The semantic function "setsat" corresponds to semantic brackets, or
 Stirling's double absolute value signs. For Fm a formula and V a function
 assigning sets of "processes" to strings,  setsat Fm V  will denote a
 set of procesees. (We care nothing here for what processes are - a type
 variable 'p stands in for them.) The turnstile-ish form of assertion,
 "pp_sat", notionally the notation E |=_V Fm, will be defined simply as
    pp_sat E V Fm = E IN setsat Fm V . *)

(* ==== Lockwood's definition for his stripped down language
val setsat = Define
`(setsat ttm (V:string->'p set) = (UNIV:'p set)) /\
 (setsat (Var Z) V = V Z) /\
 (setsat (conj Fm1 Fm2) V = setsat Fm1 V INTER setsat Fm2 V) /\
 (setsat (mu Z Fm) V = lfp (\Q. setsat Fm (extend_env Z Q V)))`;
 ==== *)

(* ==== Our Definition of setsat in the full language ==== *)
val setsat_def =
    Define
    `setsat Trans f V = {E | (E,Trans,V) mmsat f}`; 

(*********************************************************************)
(* Prove that setsat Trans f V is equivalent to mmfn Trans f UNIV V *)
(*********************************************************************)
val setsat_is_mmfn_UNIV =
TAC_PROOF
(([],
 ``setsat Trans f V = mmfn Trans f UNIV V``),
 (REWRITE_TAC[setsat_def,mmfn_def,IN_UNIV]));

val _ = save_thm("setsat_is_mmfn_UNIV",setsat_is_mmfn_UNIV);


(*************************************************)
(* Define the set of free variables in a formula *)
(*************************************************)
val frees_def =
Define
`(frees tt = {}) /\
 (frees ff = {}) /\
 (frees (propmm Z) = {Z}) /\
 (frees (f1 andmm f2) = (frees f1) UNION (frees f2)) /\
 (frees (f1 ormm f2) = (frees f1) UNION (frees f2)) /\
 (frees (Box Actions f) = frees f) /\
 (frees (Dia Actions f) = frees f) /\
 (frees (nu Z f) = frees f DELETE Z) /\
 (frees (mu Z f) = frees f DELETE Z)`;

(***************************************)
(* Prove that frees f is always finite *)
(***************************************)
val frees_finite =
TAC_PROOF
(([],``!f.FINITE (frees f)``),
 (Induct THEN
  PROVE_TAC[frees_def,FINITE_EMPTY,FINITE_SING,FINITE_UNION, FINITE_DELETE]));

val _ = save_thm("frees_finite",frees_finite);

(******************************)
(* Variables in an expression *)
(******************************)
val vars_def =
Define
`(vars tt = {}) /\
 (vars ff = {}) /\
 (vars (propmm Z) = {Z}) /\
 (vars (f1 andmm f2) = (vars f1) UNION (vars f2)) /\
 (vars (f1 ormm f2) = (vars f1) UNION (vars f2)) /\
 (vars (Box Actions f) = vars f) /\
 (vars (Dia Actions f) = vars f) /\
 (vars (nu Z f) = vars f UNION {Z}) /\
 (vars (mu Z f) = vars f UNION {Z})`;

(* Properties of vars *)

(**********************************************)
(* vars produces a finite number of variables *)
(**********************************************)
val vars_finite =
TAC_PROOF
(([],``!f.FINITE (vars f)``),
 (Induct THEN
  PROVE_TAC[vars_def,FINITE_EMPTY,FINITE_SING,FINITE_UNION]));

val _ = save_thm("vars_finite",vars_finite);

(**************************************************************************)
(* x1 SUBSET y1 ==> x2 SUBSET y2 ==> ((x1 UNION x2) SUBSET (y1 UNION y2)) *)
(**************************************************************************)
val th1 = SET_SPEC_CONV ``x IN {x | x IN x1 \/ x IN x2}``;
val UNION_SUBSET_MONOTONIC =
TAC_PROOF
(([],
 ``x1 SUBSET y1 ==> x2 SUBSET y2 ==> ((x1 UNION x2) SUBSET (y1 UNION y2))``),
 (REWRITE_TAC[SUBSET_DEF,UNION_DEF,th1] THEN
  PROVE_TAC[]));

val _ = save_thm("UNION_SUBSET_MONOTONIC",UNION_SUBSET_MONOTONIC);

(*************************************)
(* (x DELETE p) SUBSET (x UNION {p}) *)
(*************************************)
val th1 = SET_SPEC_CONV ``x' IN {x' | x' IN x /\ x' NOTIN {p}}``;
val th2 = SET_SPEC_CONV ``x' IN {x' | x' IN x \/ x' IN {p}}``;

val DELETE_SUBSET_UNION =
TAC_PROOF
(([],
 ``(x SUBSET y) ==> (x DELETE p) SUBSET (y UNION {p})``),
 (REWRITE_TAC[DELETE_DEF,DIFF_DEF,UNION_DEF,SUBSET_DEF,th1,th2] THEN
  PROVE_TAC[]));

(******************************************************)
(* The set of free variables is a subset of variables *)
(******************************************************)
val frees_SUBSET_vars =
TAC_PROOF
(([],
 ``!f.frees f SUBSET vars f``),
 (Induct THEN
  ASM_REWRITE_TAC[frees_def,vars_def,SUBSET_REFL] THENL
  [(IMP_RES_TAC UNION_SUBSET_MONOTONIC),
   (IMP_RES_TAC UNION_SUBSET_MONOTONIC),
   (IMP_RES_TAC DELETE_SUBSET_UNION),
   (IMP_RES_TAC DELETE_SUBSET_UNION)]));

val _ = save_thm("frees_SUBSET_vars",frees_SUBSET_vars);

val _ = save_thm("frees_are_vars",(REWRITE_RULE[SUBSET_DEF] frees_SUBSET_vars));

(******************************************************************)
(* Begin setting up the infrastructure for unique variable names. *)
(* Start by postulating the properties of ``variant``, a function *)
(* that takes a set of variables and a variable as arguments and  *)
(* returns a variable that is not in the set of variables.        *)
(* Min's dissertation assumed variables were of type :string. We  *)
(* generalize this to type :'variable where UNIV:'variable is     *)
(* INFINITE.                                                      *)
(******************************************************************)
val variant_EXISTS =
TAC_PROOF
(([],
 ``?(variant:('variable set -> 'variable -> 'variable)).
   !exclvars:'variable set.INFINITE (UNIV:'variable set) ==> FINITE exclvars ==> !v:'variable.(variant exclvars v) NOTIN exclvars``),
 (SUBST1_TAC
  (SYM
   (X_SKOLEM_CONV
    (``variant:('variable set -> 'variable -> 'variable)``)
    (``!exclvars:'variable set.
       ?t:'variable -> 'variable.
       INFINITE (UNIV:'variable set) ==> FINITE exclvars ==> !v:'variable.(t v) NOTIN exclvars``))) THEN
  GEN_TAC THEN
  CONV_TAC EXISTS_IMP_CONV THEN
  DISCH_TAC THEN
  CONV_TAC EXISTS_IMP_CONV THEN
  DISCH_TAC THEN
  SUBST1_TAC
  (SYM
   (X_SKOLEM_CONV
    (``t:('variable -> 'variable)``)
    (``!v:'variable.? u:'variable.u NOTIN exclvars``))) THEN
  PROVE_TAC[NOT_IN_FINITE]));

val _ = save_thm("variant_EXISTS",variant_EXISTS);

(********************************************)
(* Specifying the properties of ``variant`` *)
(********************************************)
val variant_spec =
Definition.new_specification("variant_spec",["variant"],variant_EXISTS);

(*********************************************************)
(* Specialized variant of list induction will be helpful *)
(*********************************************************)

val pair_list_induction = store_thm ("pair_list_induction", Term
`!P. P [] /\ (!l. P l ==> !X:'a Y:'b. P ((X,Y) :: l)) ==> !l. P l`,
GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC list_induction
THEN AR THEN REPEAT STRIP_TAC
THEN CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV (GSYM PAIR)))
THEN RES_TAC THEN AR);

(* Application of a list of substitutions of one variable for another,      *)
(* to a single variable, RIGHTMOST first. A pair (Y,Z) means subst Z for Y. *)
(* fv [] (X:'propvar) = X is the case when there are no more substitutions. *)
(* fv ((Y,Z)::l) X is the case when there is at least one variable          *)
(* substitution, Z substituted for Y. As the substitution is done RIGHTMOST *)
(* first, we need to evaluate fv l X prior to considering the substitution  *)
(* (Y,Z).  If X' = fv l X, and if X' = Y, then we return Z, else X.         *)

val fv_def = Define
`(fv [] (X:'propvar) = X) /\
 (fv ((Y,Z) :: l) X = let X' = fv l X in (if X' = Y then Z else X'))`;

(* fv extended to a set (typically of the free variables of something: *)

(* Put one variable, Y, in place of another, X, in a set (of free
 variables of some expression), if X is present: *)

val rf_def = Define
`rf (Y:'a) X fs = if X IN fs then Y INSERT fs DELETE X else fs`;

val gf_def = Define
`(gf [] fs = fs) /\
 (gf ((X:'propvar, Y) :: l) fs = rf Y X (gf l fs))`;

(* More perspicuous definition of gf, proved by induction: *)

val gf_im =
TAC_PROOF
(([],
 ``!l. gf l = IMAGE (fv l)``),
(INDUCT_THEN pair_list_induction STRIP_ASSUME_TAC THEN 
 REPEAT GEN_TAC THEN 
 FUN_EQ_TAC THEN 
 ASM_REWRITE_TAC [gf_def, fv_def, rf_def, IMAGE_DEF, EXTENSION] THEN 
 GEN_TAC THEN CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THENL
 [REFL_TAC,
  (DISJ_CASES_THEN (fn nex => REWRITE_TAC [nex] THEN MP_TAC nex)
          (SPEC (Term`?x. (X = fv l x) /\ x IN f`) EXCLUDED_MIDDLE) THEN 
 CONV_TAC (ONCE_DEPTH_CONV let_CONV THENC ONCE_DEPTH_CONV SET_SPEC_CONV))] THENL
 [(STRIP_TAC THEN ASM_REWRITE_TAC [IN_INSERT, IN_DELETE]
   THEN CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN EQ_TAC THENL
   [STRIP_TAC THENL
    [Q_TAC EXISTS_TAC `x'` THEN AR
    ,Q_TAC EXISTS_TAC `x''`
     THEN REWRITE_TAC [SYM (ASSUME (Term`x = fv l x''`))] THEN AR
    ]
   ,STRIP_TAC THEN AR THEN (COND_CASES_TAC THEN1 REWRITE_TAC [])
    THEN DISJ2_TAC THEN AR THEN Q_TAC EXISTS_TAC `x''` THEN AR
   ]),
  (DISCH_THEN (STRIP_ASSUME_TAC o (CONV_RULE (NOT_EXISTS_CONV
                    THENC REWRITE_CONV [DE_MORGAN_THM, GSYM IMP_DISJ_THM]
                    THENC ONCE_DEPTH_CONV SYM_CONV)))
   THEN AP_TERM_TAC THEN FUN_EQ_TAC THEN EQ_TAC THEN STRIP_TAC THEN AR THENL
   [SUBGOAL_THEN (Term`~(fv l x' = X)`) (ASM_REWRITE_TAC o ulist) THEN
    IMP_RES_TAC (CONV_RULE (ONCE_DEPTH_CONV CONTRAPOS_CONV
                            THENC REWRITE_CONV [])
                 (ASSUME (Term`!x. (fv l x = X) ==> ~(x IN f)`)))
    ,SUBGOAL_THEN (Term`~(fv l x' = X)`) (ASM_REWRITE_TAC o ulist) THEN
    IMP_RES_TAC (CONV_RULE (ONCE_DEPTH_CONV CONTRAPOS_CONV
                            THENC REWRITE_CONV [])
                 (ASSUME (Term`!x. (fv l x = X) ==> ~(x IN f)`)))])]));

val _ = save_thm("gf_im",gf_im);


(* Given a list of variable-to-variable substitutions to be carried out
 in left-to-right order over a formula (mu Z ... ), producing the result
 (mu Z' ...'), also given Z itself and the set fs of variables
 occurring free in  ... , gl (short for grow-list) returns a possibly
 longer list to be carried out over the body; gv (short for grow-list's
 variable) returns the ultimate replacement, Z' for Z. The substitutions
 will not introduce additional occurrences of a variable already free. *)

(* Note that the list argument to gl represents the sequence of
 substitutions to be carried out on (mu Z ...), with fs the free variables
 of ... (possibly with Z thrown in for luck if not there already). *)

val gl_def = Define
`(gl [] Z fs = []) /\
 (gl ((X,Y) :: l) Z fs =
   let l' = gl l Z fs
   in let (fs', Z') = (gf l' fs, fv l' Z)
      in if ~(X IN fs') \/ (X = Z') then l'
         else if Y = Z'
         then (X, Y) :: (Z', variant (Y INSERT fs') Z') :: l'
         else (X, Y) :: l')`;

val gv_def = Define `gv l Z fs = fv (gl l Z fs) Z`;

(* Using fv, gv, and gl, we can define l_Sub, to carry out a list of
 variable_for_variable substitutions, on a formula. *)

val l_Sub_def = Define
`(l_Sub l tt = tt) /\
 (l_Sub l ff = ff) /\
 (l_Sub l (propmm Y) = propmm (fv l Y)) /\
 (l_Sub l (P andmm Q) = (l_Sub l P) andmm (l_Sub l Q)) /\
 (l_Sub l (P ormm Q) = (l_Sub l P) ormm (l_Sub l Q)) /\
 (l_Sub l (Box Actions P) = Box Actions (l_Sub l P)) /\
 (l_Sub l (Dia Actions P) = Dia Actions (l_Sub l P)) /\
 (l_Sub l (nu Z P) =
  let fs = frees P
  in let (Z', l') = (gv l Z fs, gl l Z fs)
     in nu Z' (l_Sub l' P)) /\
 (l_Sub l (mu Z P) =
  let fs = frees P
  in let (Z', l') = (gv l Z fs, gl l Z fs)
     in mu Z' (l_Sub l' P))`;

val l_Sub_same_size =
TAC_PROOF
(([],
 ``!Fm l. fmla_size (l_Sub l Fm) = fmla_size Fm``),
 (Induct THEN ASM_REWRITE_TAC [l_Sub_def]
 THEN ASM_REWRITE_TAC [fmla_size_def]
 THEN REPEAT GEN_TAC
 THEN CONV_TAC (DEPTH_CONV let_CONV)
 THEN ASM_REWRITE_TAC [fmla_size_def]));

val _ = save_thm("l_Sub_same_size",l_Sub_same_size);

val l_Sub_nil = 
TAC_PROOF
(([],``!Fm. l_Sub [] Fm = Fm``),
(Induct THEN ASM_REWRITE_TAC [l_Sub_def, fv_def, gl_def, gv_def]
THEN CONV_TAC (DEPTH_CONV let_CONV) THEN AR));

val _ = save_thm("l_Sub_nil",l_Sub_nil);

(* and now we can define substitution in general by reliance on l_Sub;
 but the big task is to show that the call on l_Sub can be replaced by
 a nested call on itself. *)

val Subst_defn = Hol_defn "Subst_defn"
`(Subst N (X:'b) (tt:('a,'b)mmForm) = tt) /\
 (Subst N X ff = ff) /\
 (Subst N X (propmm Y) = if Y = X then N else propmm Y) /\
 (Subst N X (P andmm Q) = (Subst N X P) andmm (Subst N X Q)) /\
 (Subst N X (P ormm Q) = (Subst N X P) ormm (Subst N X Q)) /\
 (Subst N X (Box Actions P) = Box Actions (Subst N X P)) /\
 (Subst N X (Dia Actions P) = Dia Actions (Subst N X P)) /\
 (Subst N X (nu Z P) =
  let fs = frees P
  in if ~(X IN fs) \/ (X = Z) then nu Z P
        else if Z IN frees N
             then let W = variant (frees N UNION fs) Z
                  in nu W (Subst N X (l_Sub [(Z, W)] P))
        else nu Z (Subst N X P)) /\
 (Subst N X (mu Z P) =
  let fs = frees P
  in if ~(X IN fs) \/ (X = Z) then mu Z P
        else if Z IN frees N
             then let W = variant (frees N UNION fs) Z
                  in mu W (Subst N X (l_Sub [(Z, W)] P))
        else mu Z (Subst N X P))`;

val (Subst_def, Subst_ind) = Defn.tprove (Subst_defn,
WF_REL_TAC `measure (fmla_size o SND o SND)`
THEN ASM_REWRITE_TAC [fmla_size_def, l_Sub_same_size]
THEN REPEAT STRIP_TAC THEN ARITH_TAC);

val _ = save_thm("Subst_def",Subst_def);
val _ = save_thm("Subst_ind",Subst_ind);

(* =========== From Min's Dissertation: we use Lockwood's definitions

(**********************************************************)
(* Define replace_free_occs that replaces free occurences *)
(* of a specified variable with another variable.         *)
(**********************************************************)
val replace_free_occs_def = 
Define
`(replace_free_occs X X' tt = tt) /\
 (replace_free_occs X X' ff = ff) /\
 (replace_free_occs X X' (propmm Z) = (propmm (if Z=X then X' else Z))) /\
 (replace_free_occs X X' (f1 andmm f2) = (replace_free_occs X X' f1) andmm (replace_free_occs X X' f2)) /\
 (replace_free_occs X X' (f1 ormm f2) = (replace_free_occs X X' f1) ormm (replace_free_occs X X' f2)) /\
 (replace_free_occs X X' (Box Actions f) = (Box Actions (replace_free_occs X X' f))) /\
 (replace_free_occs X X' (Dia Actions f) = (Dia Actions (replace_free_occs X X' f))) /\
 (replace_free_occs X X' (nu Z f) = if (Z=X) then (nu Z f) else (nu Z (replace_free_occs X X' f))) /\
 (replace_free_occs X X' (mu Z f) = if (Z=X) then (mu Z f) else (mu Z (replace_free_occs X X' f)))`;

(************************************)
(* Define the substitution function *)
(************************************)
val Subst_defn = 
Hol_defn "Subst_defn"
`(Subst p Z tt = tt) /\
 (Subst p Z ff = ff) /\
 (Subst p Z (propmm X) = if (X=Z) then p else (propmm X)) /\
 (Subst p Z (f1 andmm f2) = (Subst p Z f1) andmm (Subst p Z f2)) /\
 (Subst p Z (f1 ormm f2) = (Subst p Z f1) ormm (Subst p Z f2)) /\
 (Subst p Z (Box Actions f) = (Box Actions (Subst p Z f))) /\
 (Subst p Z (Dia Actions f) = (Dia Actions (Subst p Z f))) /\
 (Subst p Z (nu X f) = 
  if (X=Z) then (nu X f) else 
  if X IN frees p
  then
   let X' = variant (frees p UNION vars (nu X f) UNION {Z}) X
    in
    nu X' (Subst p Z (replace_free_occs X X' f))
  else
   nu X (Subst p Z f)) /\
 (Subst p Z (mu X f) = 
  if (X=Z) then (mu X f) else 
  if X IN frees p 
  then
   let X' = variant (frees p UNION vars (mu X f) UNION {Z}) X
    in
    mu X' (Subst p Z (replace_free_occs X X' f))
  else
   mu X (Subst p Z f))`;

(*******************************************)
(* Start working on termination conditions *)
(*******************************************)
val replace_same_size =
TAC_PROOF
(([],
 ``!X X' f.fmla_size(replace_free_occs X X' f) = fmla_size f``),
 (GEN_TAC THEN
  GEN_TAC THEN
  Induct THEN
  REWRITE_TAC [replace_free_occs_def,fmla_size_def] THEN
  ASM_REWRITE_TAC [] THENL
  [(GEN_TAC THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[fmla_size_def]),
   (REWRITE_TAC[replace_free_occs_def,fmla_size_def] THEN
    GEN_TAC THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[fmla_size_def])]));

val _ = save_thm("replace_same_size",replace_same_size);

(*********************)
(* Prove termination *)
(*********************)
val (Subst_def, Subst_induction) =
Defn.tprove
(Subst_defn,
 (WF_REL_TAC `measure(fmla_size o SND o SND)` THEN
  ASM_REWRITE_TAC[fmla_size_def,replace_same_size] THEN
  REPEAT STRIP_TAC THEN
  numLib.ARITH_TAC));

(*****************************************************)
(* Save the useful definition of Subst and induction *)
(*****************************************************)
val _ = save_thm("Subst_def",Subst_def);
val _ = save_thm("Subst_induction",Subst_induction);

 =================== End from Min's Dissertation ========== *)

(* From Lockwood *)
(* predicate ok_r is true if a list of variable replacements is O.K. to
 perform on a set of variables - i.e., will not conflate any two. *)

val ok_r_def = Define
`(ok_r [] fs = T) /\
 (ok_r ((X,Y) :: l) fs = ok_r l fs /\
                         (X IN gf l fs ==> ~(Y IN gf l fs)))`;
val fv_IN_gf = store_thm ("fv_IN_gf", Term
`!l fs. !A::fs. fv l A IN gf l fs`,
REPEAT RESQ_STRIP_TAC THEN REWRITE_TAC [gf_im, IMAGE_DEF]
THEN CONV_TAC SET_SPEC_CONV THEN Q_TAC EXISTS_TAC `A` THEN AR);

val fv_inj = store_thm ("fv_inj", Term
`!l fs. ok_r l fs ==> (!A B. A IN fs /\ B IN fs ==>
        ((fv l A = fv l B) ==> (A = B)))`,
INDUCT_THEN pair_list_induction MP_TAC THEN REWRITE_TAC [ok_r_def, fv_def]
THEN CONV_TAC (ONCE_DEPTH_CONV let_CONV) THEN DISCH_TAC THEN REPEAT GEN_TAC
THEN REWRITE_TAC [gf_im, IMAGE_DEF]
THEN CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV (REWR_CONV IMP_DISJ_THM)))
THEN CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV)
THEN CONV_TAC (ONCE_DEPTH_CONV NOT_EXISTS_CONV)
THEN REWRITE_TAC [DE_MORGAN_THM]
THEN CONV_TAC (LAND_CONV (RAND_CONV (BINOP_CONV (QUANT_CONV
         (ONCE_DEPTH_CONV SYM_CONV THENC REWR_CONV DISJ_SYM
          THENC REWR_CONV (GSYM IMP_DISJ_THM))))))
THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
[RES_THEN (REWRITE_TAC o ulist) THEN RES_TAC
,REPEAT COND_CASES_TAC THEN RES_TAC THEN AR
 THEN CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN AR
 THEN SUBGOAL_THEN (Term`fv l B = fv l A`)
                   (ANTE_RES_THEN (REWRITE_TAC o ulist)) THEN AR]);


(* replace last implication by equality in the above: *)

val fv_1_1 = store_thm ("fv_1_1", Term
`!l fs. ok_r l fs ==> (!A B. A IN fs /\ B IN fs ==>
        ((fv l A = fv l B) = (A = B)))`,
REPEAT STRIP_TAC THEN EQ_TAC THENL
[IMP_RES_TAC fv_inj, DISCH_TAC THEN AR]);

(* Following thm, fv_BIJ, is included for clarity; not now used. *)

val fv_BIJ = store_thm ("fv_BIJ", Term
`!l fs. ok_r l fs ==> BIJ (fv l) fs (gf l fs)`,
REPEAT STRIP_TAC THEN REWRITE_TAC [BIJ_DEF, INJ_DEF, SURJ_DEF]
THEN REWRITE_TAC [CONV_RULE (DEPTH_CONV RES_FORALL_CONV) fv_IN_gf]
THEN CONJ_TAC THENL
[MATCH_MP_TAC fv_inj THEN AR
,GEN_TAC THEN REWRITE_TAC [gf_im, IMAGE_DEF]
 THEN CONV_TAC (LAND_CONV SET_SPEC_CONV) THEN STRIP_TAC
 THEN Q_TAC EXISTS_TAC `x'` THEN AR]);

val gf_empty = store_thm ("gf_empty", Term
`!l. gf l {} = {}`,
INDUCT_THEN pair_list_induction STRIP_ASSUME_TAC
THEN ASM_REWRITE_TAC [gf_def, rf_def, NOT_IN_EMPTY]);

val fv_LEM = store_thm ("fv_LEM", Term
`!l s. gf l {s} = {fv l s}`,
REWRITE_TAC [gf_im, IMAGE_DEF, IN_SING, EXTENSION] THEN REPEAT GEN_TAC
THEN CONV_TAC (LAND_CONV SET_SPEC_CONV)
THEN EQ_TAC THEN STRIP_TAC THEN AR THEN Q_TAC EXISTS_TAC `s` THEN AR);

val gf_union = store_thm ("gf_union", Term
`!l fs fs'. gf l (fs UNION fs') = gf l fs UNION gf l fs'`,
REWRITE_TAC [gf_im, IMAGE_UNION]);

val gf_insert = store_thm ("gf_insert", Term
`!l fs Z. gf l (Z INSERT fs) = fv l Z INSERT gf l fs`,
REWRITE_TAC [gf_im, IMAGE_INSERT]);

val gf_monotone = store_thm ("gf_monotone", Term
`!l big sma. sma SUBSET big ==> gf l sma SUBSET gf l big`,
REWRITE_TAC [SUBSET_UNION_ABSORPTION, GSYM gf_union]
THEN REPEAT STRIP_TAC THEN AR);

val gf_finite = store_thm ("gf_finite", Term
`!fs. FINITE fs ==> !l. FINITE (gf l fs)`,
REPEAT STRIP_TAC THEN REWRITE_TAC [gf_im]
THEN MATCH_MP_TAC IMAGE_FINITE THEN ASM_REWRITE_TAC []);

val ok_r_subset = store_thm ("ok_r_subset", Term
`!l big sma. sma SUBSET big ==> ok_r l big ==> ok_r l sma`,
INDUCT_THEN pair_list_induction STRIP_ASSUME_TAC THEN REPEAT GEN_TAC
THEN ASM_REWRITE_TAC [ok_r_def]
THEN DISCH_TAC THEN CONV_TAC ANTE_CONJ_CONV
THEN DISCH_TAC THEN RES_TAC THEN AR
THEN IMP_RES_THEN (ASSUME_TAC o REWRITE_RULE [SUBSET_DEF] o SPEC_ALL)
                  gf_monotone
THEN DISCH_TAC THEN DISCH_TAC THEN RES_TAC
THEN ANTE_RES_THEN MP_TAC (ASSUME (Term`X IN gf l big`))
THEN CONV_TAC CONTRAPOS_CONV THEN AR);

val fv_not_in = store_thm ("fv_not_in", Term
`!fs gs Z l. ok_r l fs /\ gs SUBSET fs /\ Z IN fs /\ ~(Z IN gs) ==>
             ~(fv l Z IN gf l gs)`,
REPEAT GEN_TAC THEN STRIP_TAC
THEN REWRITE_TAC [gf_im, IMAGE_DEF]
THEN CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV THENC NOT_EXISTS_CONV)
THEN GEN_TAC THEN ONCE_REWRITE_TAC [CONJ_SYM]
THEN REWRITE_TAC [DE_MORGAN_THM, GSYM IMP_DISJ_THM]
THEN DISCH_TAC THEN IMP_RES_TAC SUBSET_DEF
THEN IMP_RES_TAC fv_1_1 THEN AR
THEN CONV_TAC (RAND_CONV SYM_CONV)
THEN MATCH_MP_TAC in_not_in_not_eq THEN Q_TAC EXISTS_TAC `gs` THEN AR);

(* minor fixes: l' in Lockwood's proofs now are x' due to HOL behavior change *)
val gf_delete = store_thm ("gf_delete", Term
`!l fs Z. ok_r l (Z INSERT fs) ==>
              (gf l (fs DELETE Z) = gf l fs DELETE fv l Z)`,
REPEAT STRIP_TAC THEN REWRITE_TAC [gf_im, IMAGE_DEF, EXTENSION, IN_DELETE]
THEN GEN_TAC THEN CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV)
THEN CONV_TAC (RAND_CONV LEFT_AND_EXISTS_CONV)
THEN AP_TERM_TAC THEN FUN_EQ_TAC
THEN Q_TAC ASM_CASES_TAC `x = fv l x'` THEN AR
THEN Q_TAC ASM_CASES_TAC `x' IN fs` THEN AR
THEN SUBGOAL_THEN (Term`x':'a IN (Z INSERT fs) /\ Z IN (Z INSERT fs)`)
 (fn cj => REWRITE_TAC [MATCH_MP (MATCH_MP fv_1_1
                         (ASSUME (Term`ok_r l (Z INSERT fs)`))) cj])
THEN ASM_REWRITE_TAC [IN_INSERT]);

(*************************************************************************)
(* note: because variable s:'a in our development, as opposed to Min and *)
(* Lockwood's original assumption s:string, we have to include the       *)
(* additional condition  INFINITE (UNIV:'a set)                          *)
(*************************************************************************)
val variant_not_in = store_thm ("variant_not_in", Term
`!(s:'a) excl. INFINITE (UNIV:'a set) ==> FINITE excl ==> ~(variant excl s IN excl)`,
REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN IMP_RES_TAC variant_spec THEN AR);

(*************************************************************************)
(* note: because variable s:'a in our development, as opposed to Min and *)
(* Lockwood's original assumption s:string, we have to include the       *)
(* additional condition  INFINITE (UNIV:'a set)                          *)
(*************************************************************************)
val not_in_gf = store_thm ("not_in_gf", Term
`!(A:'a) excl l fs Q. INFINITE (UNIV:'a set) ==> FINITE excl ==>
 ~(A IN gf ((A, variant (A INSERT excl) Q) :: l) fs)`,
REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN REWRITE_TAC [gf_im, IMAGE_DEF]
THEN CONV_TAC (RAND_CONV SET_SPEC_CONV THENC NOT_EXISTS_CONV) THEN GEN_TAC
THEN REWRITE_TAC [fv_def] THEN CONV_TAC (ONCE_DEPTH_CONV let_CONV)
THEN COND_CASES_TAC THENL
[REWRITE_TAC [DE_MORGAN_THM] THEN DISJ1_TAC
 THEN MATCH_MP_TAC in_not_in_not_eq
 THEN Q_TAC EXISTS_TAC `A INSERT excl` THEN CONJ_TAC THENL
 [REWRITE_TAC [IN_INSERT]
(* slight modification to convert variant_not_in to form A /\ B ==> C to work with MATCH_MP_TAC *)
 ,MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO] variant_not_in) THEN ASM_REWRITE_TAC [FINITE_INSERT]
 ]
,CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN AR
]);

(* The main lemma about gl: preserves frees and ok_r *)
val ok_r_gl_insert = store_thm ("ok_r_gl_insert", Term
`!l (Z:'a) fs. INFINITE (UNIV:'a set) /\ FINITE fs /\ ok_r l (fs DELETE Z) ==>
          ok_r (gl l Z fs) (Z INSERT fs) /\
          (!X::fs DELETE Z. fv (gl l Z fs) X = fv l X)`,
INDUCT_THEN pair_list_induction STRIP_ASSUME_TAC
THEN REPEAT GEN_TAC THENL
[REWRITE_TAC [gl_def, ok_r_def, gv_def, fv_def, gf_def]
 THEN REPEAT DISCH_TAC THEN AR THEN RESQ_STRIP_TAC THEN AR
,REWRITE_TAC [ok_r_def] THEN STRIP_TAC THEN RES_TAC
 THEN (SUBGOAL_THEN
   (Term`~(fv (gl l Z fs) Z IN gf (gl l Z fs) (fs DELETE Z))`) ASSUME_TAC
   THEN1 (MATCH_MP_TAC fv_not_in THEN Q_TAC EXISTS_TAC `Z INSERT fs`
    THEN ASM_REWRITE_TAC [IN_INSERT, SUBSET_DEF, IN_DELETE] THEN TAUT_TAC))
 THEN REWRITE_TAC [gl_def, COND_NOT_DISJ] THEN CONV_TAC (DEPTH_CONV let_CONV)
 THEN COND_CASES_TAC THEN AR THENL
 [RESQ_GEN_TAC THEN RESQ_RES_THEN SUBST1_TAC
  THEN REWRITE_TAC [fv_def] THEN CONV_TAC (RAND_CONV let_CONV)
  THEN SUBGOAL_THEN (Term`~(fv l X' = fv (gl l Z fs) Z)`)
       (fn th => REWRITE_TAC [th] THEN RESQ_RES_THEN SUBST1_TAC THEN AR)
  THEN MATCH_MP_TAC in_not_in_not_eq
  THEN Q_TAC EXISTS_TAC `gf (gl l Z fs) (fs DELETE Z)` THEN AR
  THEN REWRITE_TAC [gf_im, IMAGE_DEF] THEN CONV_TAC SET_SPEC_CONV
  THEN Q_TAC EXISTS_TAC `X'` THEN RESQ_RES_THEN SUBST1_TAC THEN AR
 ,REPEAT COND_CASES_TAC THENL
  [ASM_REWRITE_TAC [ok_r_def, fv_def]
   THEN (SUBGOAL_THEN
         (Term`FINITE (gf (gl l Z fs) (Z INSERT fs)) /\
               FINITE (gf (gl l Z fs) fs)`)
         STRIP_ASSUME_TAC THEN1 (CONJ_TAC THEN
            MATCH_MP_TAC gf_finite THEN ASM_REWRITE_TAC [FINITE_INSERT]))
   THEN REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC [gf_insert]
    THEN MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO] variant_not_in) THEN ASM_REWRITE_TAC [GSYM gf_insert]
   ,DISCH_TAC THEN MATCH_MP_TAC (REWRITE_RULE[AND_IMP_INTRO]not_in_gf) THEN AR
   ,RESQ_GEN_TAC THEN CONV_TAC (DEPTH_CONV let_CONV)
    THEN (SUBGOAL_THEN (Term`~(fv (gl l Z fs) X' = fv (gl l Z fs) Z)`)
     (REWRITE_TAC o ulist)
     THEN1 ((SUBGOAL_THEN
             (Term`X':'a IN (Z INSERT fs) /\ Z IN (Z INSERT fs)`)
             (fn cj => REWRITE_TAC [MATCH_MP
               (MATCH_MP fv_1_1 (ASSUME
                 (Term`ok_r (gl l Z fs) (Z INSERT fs)`))) cj]) THEN1
              (REWRITE_TAC [IN_INSERT] THEN IMP_RES_TAC IN_DELETE THEN AR))
            THEN MATCH_MP_TAC in_not_in_not_eq
            THEN Q_TAC EXISTS_TAC`fs DELETE Z`
            THEN ASM_REWRITE_TAC [IN_DELETE]))
    THEN RESQ_RES_THEN SUBST1_TAC THEN REFL_TAC
   ]
  ,ASM_REWRITE_TAC [ok_r_def, fv_def] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC [GSYM INSERT_INSERT_DELETE]
    THEN ASM_REWRITE_TAC [gf_insert, IN_INSERT]
    THEN REWRITE_TAC [gf_im, IMAGE_DEF]
    THEN CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV
                   THENC LEFT_IMP_EXISTS_CONV) THEN GEN_TAC
    THEN CONV_TAC (LAND_CONV (REWR_CONV CONJ_SYM) THENC ANTE_CONJ_CONV)
    THEN DISCH_TAC THEN RESQ_RES_THEN SUBST1_TAC
    THEN DISCH_TAC THEN CONV_TAC (NOT_EXISTS_CONV)
    THEN GEN_TAC THEN REWRITE_TAC [DE_MORGAN_THM]
    THEN CONV_TAC (REWR_CONV DISJ_SYM) THEN REWRITE_TAC [GSYM IMP_DISJ_THM]
    THEN DISCH_TAC THEN RESQ_RES_THEN SUBST1_TAC
    THEN (SUBGOAL_THEN (Term`X IN gf l (fs DELETE Z)`)
          (ANTE_RES_THEN (MP_TAC o REWRITE_RULE [gf_im, IMAGE_DEF]))
          THEN1 (REWRITE_TAC [gf_im, IMAGE_DEF] THEN CONV_TAC SET_SPEC_CONV
                 THEN Q_TAC EXISTS_TAC `x` THEN AR))
    THEN CONV_TAC (LAND_CONV
                   (RAND_CONV SET_SPEC_CONV THENC NOT_EXISTS_CONV))
    THEN REWRITE_TAC [DE_MORGAN_THM, GSYM IMP_DISJ_THM]
    THEN DISCH_THEN (IMP_RES_TAC o
          CONV_RULE (ONCE_DEPTH_CONV CONTRAPOS_CONV THENC REWRITE_CONV []))
   ,RESQ_GEN_TAC THEN RESQ_RES_THEN SUBST1_TAC THEN REFL_TAC
   ]
  ,AR THEN RESQ_GEN_TAC
   THEN REWRITE_TAC [fv_def] THEN CONV_TAC (RAND_CONV let_CONV)
   THEN RESQ_RES_THEN (SUBST1_TAC o SYM)
   THEN SUBGOAL_THEN (Term`~(fv (gl l Z fs) X' = X)`)
        (fn th => REWRITE_TAC [th] THEN RESQ_RES_THEN SUBST1_TAC THEN AR)
   THEN MATCH_MP_TAC in_not_in_not_eq
   THEN Q_TAC EXISTS_TAC `gf (gl l Z fs) (fs DELETE Z)`
   THEN (CONJ_TAC THEN1 (RESQ_IMP_RES_TAC fv_IN_gf THEN AR))
   THEN Q_TAC UNDISCH_TAC `~(X IN gf (gl l Z fs) fs)`
   THEN CONV_TAC CONTRAPOS_CONV
   THEN SPEC_TAC (Term`X:'a`, Term`X:'a`)
   THEN REWRITE_TAC [GSYM SUBSET_DEF] THEN MATCH_MP_TAC gf_monotone
   THEN REWRITE_TAC [SUBSET_DEF, IN_DELETE] THEN TAUT_TAC
]]]);


val half_gl_ok = store_thm ("half_gl_ok", Term (* use with MATCH_MP_TAC *)
`!l (Z:'a) fs. INFINITE (UNIV:'a set) /\ FINITE fs /\ ok_r l (fs DELETE Z) ==>
          ok_r (gl l Z fs) (Z INSERT fs)`,
REPEAT STRIP_TAC THEN IMP_RES_TAC ok_r_gl_insert);

val muvar_not_free = store_thm ("muvar_not_free", Term
`!s Fm. ~(s IN frees (mu s Fm))`,
REPEAT GEN_TAC THEN REWRITE_TAC [frees_def, IN_DELETE]);

(* added for full language *)
val nuvar_not_free = store_thm ("nuvar_not_free", Term
`!s Fm. ~(s IN frees (nu s Fm))`,
REPEAT GEN_TAC THEN REWRITE_TAC [frees_def, IN_DELETE]);

(* Modified Lockwood's proof to eliminate need for SUBGOAL_THEN *)
(* Added clause for nu                                          *)
val th1 =
ISPECL [``(gl (l :('b # 'b) list) (s :'b) (frees (Fm :('a, 'b) mmForm)))``,``(s:'b) INSERT frees (Fm:('a,'b)mmForm)``,``frees (Fm:('a,'b)mmForm)``] ok_r_subset

val th2 =
TAC_PROOF(([],``frees (Fm:('a,'b)mmForm) SUBSET (s:'b) INSERT frees Fm``),
PROVE_TAC[SUBSET_DEF,IN_INSERT]);

val th3 = MP th1 th2

val simple_ok_r_gl_nu = store_thm ("simple_ok_r_gl_nu", Term`(!l (s:'b) Fm.
        INFINITE (UNIV:'b set) /\ ok_r l (frees (nu s Fm)) ==> ok_r (gl l s (frees Fm)) (frees Fm))`,
REWRITE_TAC [frees_def] THEN REPEAT STRIP_TAC
THEN ASSUME_TAC (ISPEC ``Fm:('a,'b)mmForm`` frees_finite)
THEN IMP_RES_TAC half_gl_ok
THEN IMP_RES_TAC th3);

val simple_ok_r_gl_mu = store_thm ("simple_ok_r_gl_mu", Term`(!l (s:'b) Fm.
        INFINITE (UNIV:'b set) /\ ok_r l (frees (mu s Fm)) ==> ok_r (gl l s (frees Fm)) (frees Fm))`,
REWRITE_TAC [frees_def] THEN REPEAT STRIP_TAC
THEN ASSUME_TAC (ISPEC ``Fm:('a,'b)mmForm`` frees_finite)
THEN IMP_RES_TAC half_gl_ok
THEN IMP_RES_TAC th3);

(* This is the augmented version of Lockwood's theorem for nu and mu *)
val simple_ok_r_gl = save_thm("simple_ok_r_gl",CONJ simple_ok_r_gl_nu simple_ok_r_gl_mu);

(* too much infrastructure has at last made the following feasible: *)
val frees_LEM = store_thm ("frees_LEM", Term
`!(Fm:('a,'b)mmForm) l. INFINITE (UNIV:'b set) ==> ok_r l (frees Fm) ==>
          (frees (l_Sub l Fm) = gf l (frees Fm))`,
Induct THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
[(* tt *) REWRITE_TAC [l_Sub_def, frees_def, gf_empty]
,(* ff *) REWRITE_TAC [l_Sub_def, frees_def, gf_empty]
,(* propmm *) REWRITE_TAC [l_Sub_def, frees_def, fv_LEM]
,(* andmm *) REWRITE_TAC [frees_def, gf_union]
 THEN ASSUME_TAC
      (ISPECL [Term`frees Fm`, Term`frees Fm'`] (CONJUNCT1 SUBSET_UNION))
 THEN ASSUME_TAC
      (ISPECL [Term`frees Fm'`, Term`frees Fm`] (CONJUNCT2 SUBSET_UNION))
 THEN DISCH_TAC THEN IMP_RES_TAC ok_r_subset
 THEN RES_TAC THEN ASM_REWRITE_TAC [l_Sub_def, frees_def]
,(* ormm *) REWRITE_TAC [frees_def, gf_union]
 THEN ASSUME_TAC
      (ISPECL [Term`frees Fm`, Term`frees Fm'`] (CONJUNCT1 SUBSET_UNION))
 THEN ASSUME_TAC
      (ISPECL [Term`frees Fm'`, Term`frees Fm`] (CONJUNCT2 SUBSET_UNION))
 THEN DISCH_TAC THEN IMP_RES_TAC ok_r_subset
 THEN RES_TAC THEN ASM_REWRITE_TAC [l_Sub_def, frees_def]
,(* Box *) RES_TAC THEN ASM_REWRITE_TAC[frees_def,l_Sub_def]
,(* Dia *) RES_TAC THEN ASM_REWRITE_TAC[frees_def,l_Sub_def]
,(* nu *) REWRITE_TAC [l_Sub_def] THEN CONV_TAC (DEPTH_CONV let_CONV)
 THEN DISCH_THEN (ASSUME_TAC o REWRITE_RULE [frees_def])
 THEN ASSUME_TAC (SPEC ``Fm:('a,'b)mmForm`` frees_finite)
 THEN IMP_RES_TAC ok_r_gl_insert THEN REWRITE_TAC [gv_def]
 THEN REWRITE_TAC [frees_def]
(* missing an assumption after next step *)
 THEN (SUBGOAL_THEN (Term`frees (Fm:('a,'b)mmForm) SUBSET ((p:'b) INSERT frees Fm)`)
       (IMP_RES_TAC o MATCH_MP ok_r_subset)
       THEN1 (ONCE_REWRITE_TAC [INSERT_SING_UNION]
              THEN REWRITE_TAC [SUBSET_UNION]))
 THEN RES_TAC THEN ASM_REWRITE_TAC[]
(* replaced THEN RES_THEN SUBST1_TAC by line above *)
 THEN IMP_RES_THEN (REWRITE_TAC o ulist o GSYM) gf_delete
 THEN REWRITE_TAC [gf_im, IMAGE_DEF, EXTENSION] THEN GEN_TAC
 THEN CONV_TAC (BINOP_CONV SET_SPEC_CONV) THEN AP_TERM_TAC THEN FUN_EQ_TAC
 THEN Q_TAC ASM_CASES_TAC `x' IN frees Fm DELETE p` THEN AR
 THEN RESQ_RES_THEN SUBST1_TAC THEN REFL_TAC
,(* mu *) REWRITE_TAC [l_Sub_def] THEN CONV_TAC (DEPTH_CONV let_CONV)
 THEN DISCH_THEN (ASSUME_TAC o REWRITE_RULE [frees_def])
 THEN ASSUME_TAC (SPEC ``Fm:('a,'b)mmForm`` frees_finite)
 THEN IMP_RES_TAC ok_r_gl_insert THEN REWRITE_TAC [gv_def]
 THEN REWRITE_TAC [frees_def]
(* missing an assumption after next step *)
 THEN (SUBGOAL_THEN (Term`frees (Fm:('a,'b)mmForm) SUBSET ((p:'b) INSERT frees Fm)`)
       (IMP_RES_TAC o MATCH_MP ok_r_subset)
       THEN1 (ONCE_REWRITE_TAC [INSERT_SING_UNION]
              THEN REWRITE_TAC [SUBSET_UNION]))
 THEN RES_TAC THEN ASM_REWRITE_TAC[]
(* replaced THEN RES_THEN SUBST1_TAC by line above *)
 THEN IMP_RES_THEN (REWRITE_TAC o ulist o GSYM) gf_delete
 THEN REWRITE_TAC [gf_im, IMAGE_DEF, EXTENSION] THEN GEN_TAC
 THEN CONV_TAC (BINOP_CONV SET_SPEC_CONV) THEN AP_TERM_TAC THEN FUN_EQ_TAC
 THEN Q_TAC ASM_CASES_TAC `x' IN frees Fm DELETE p` THEN AR
 THEN RESQ_RES_THEN SUBST1_TAC THEN REFL_TAC]);


(* first moves towards Subst_nested: *)

val fv_append = store_thm ("fv_append", Term
`!l m. fv (APPEND l m) = fv l o fv m`,
Induct THEN REPEAT GEN_TAC THEN CONV_TAC FUN_EQ_CONV
THEN REWRITE_TAC [fv_def, APPEND, o_THM]
THEN REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [GSYM PAIR]
THEN ASM_REWRITE_TAC [fv_def, o_THM]);

val gf_append = store_thm ("gf_append", Term
`!l m fs. gf (APPEND l m) fs = gf l (gf m fs)`,
REWRITE_TAC [gf_im, fv_append, IMAGE_COMPOSE]);

val gl_append = store_thm ("gl_append", Term
`!Z fs m l. gl (APPEND l m) Z fs =
  APPEND (gl l (fv (gl m Z fs) Z) (gf (gl m Z fs) fs))
         (gl m Z fs)`,
GEN_TAC THEN GEN_TAC THEN GEN_TAC
THEN INDUCT_THEN pair_list_induction STRIP_ASSUME_TAC
THEN REPEAT GEN_TAC THEN REWRITE_TAC [APPEND, gl_def, gf_def]
THEN CONV_TAC (DEPTH_CONV let_CONV)
THEN ASM_REWRITE_TAC [gf_append, fv_append, o_THM]
THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC [APPEND]);

val l_Sub_append = store_thm ("l_Sub_append", Term
`!(P:('a,'b)mmForm) (l:('b#'b)list) (m:('b#'b)list). INFINITE (UNIV:'b set) ==> ok_r m (frees P) ==>
 (l_Sub (APPEND l m) P = l_Sub l (l_Sub m P))`,
Induct THEN REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC
THEN ASM_REWRITE_TAC [fv_append, gl_append, gv_def, l_Sub_def, o_THM] THENL
[((* andmm *) SUBGOAL_THEN (Term`frees (P:('a,'b)mmForm) SUBSET frees (P andmm P') /\
                     frees P' SUBSET frees (P andmm P')`) STRIP_ASSUME_TAC
  THEN1 REWRITE_TAC [frees_def, SUBSET_UNION])
 THEN IMP_RES_TAC ok_r_subset
 THEN RES_TAC THEN ASM_REWRITE_TAC [l_Sub_def]
,((* ormm *) SUBGOAL_THEN (Term`frees (P:('a,'b)mmForm) SUBSET frees (P ormm P') /\
                     frees P' SUBSET frees (P ormm P')`) STRIP_ASSUME_TAC
  THEN1 REWRITE_TAC [frees_def, SUBSET_UNION])
 THEN IMP_RES_TAC ok_r_subset
 THEN RES_TAC THEN ASM_REWRITE_TAC [l_Sub_def]
,(* Box *) PAT_ASSUM``ok_r m (frees Fm)`` (fn th => (ASSUME_TAC(REWRITE_RULE[frees_def]th)))
 THEN RES_TAC THEN ASM_REWRITE_TAC[]
,(* Dia *) PAT_ASSUM``ok_r m (frees Fm)`` (fn th => (ASSUME_TAC(REWRITE_RULE[frees_def]th)))
 THEN RES_TAC THEN ASM_REWRITE_TAC[]
,(* nu *) IMP_RES_TAC simple_ok_r_gl THEN RES_TAC THEN
 CONV_TAC (DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC [l_Sub_def, gv_def]
 THEN CONV_TAC (DEPTH_CONV let_CONV)
 THEN IMP_RES_TAC frees_LEM THEN AR
,(* mu *) IMP_RES_TAC simple_ok_r_gl THEN RES_TAC THEN
 CONV_TAC (DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC [l_Sub_def, gv_def]
 THEN CONV_TAC (DEPTH_CONV let_CONV)
 THEN IMP_RES_TAC frees_LEM THEN AR]);

(* ==== From Min's Thesis === not needed ====
(***************)
(* Subst_lemm0 *)
(***************)
val Subst_lemm0 =
TAC_PROOF
(([],
 ``!Trans f Z V setE.
   {C | (C,Trans,V) mmsat (mu Z f)} =
   {C | C IN BIGINTER {setE | satFun Trans Z V f setE SUBSET setE}}``),
 REWRITE_TAC[mmsat_mu_lfp,satFun_lfp_thm]);

val _ = save_thm("Subst_lemm0",Subst_lemm0);

 ==== end from Min's thesis not needed ==== *)

(* Specialized "fmla_size_induction", cut to fit proofs about Subst *)
val fmla_size_ind =
CONV_RULE
(DEPTH_CONV BETA_CONV)
(TAC_PROOF
 (([],
 ``!P. (!f. (!g. fmla_size g < fmla_size f ==> P g) ==> P f) ==>
       (!n. (\m. !f. (fmla_size f = m) ==> P f) n)``),
 (GEN_TAC THEN 
  DISCH_TAC THEN 
  MATCH_MP_TAC arithmeticTheory.COMPLETE_INDUCTION THEN 
  BETA_TAC THEN REPEAT STRIP_TAC THEN 
   Q_TAC UNDISCH_TAC
   `!f. (!g. fmla_size g < fmla_size f ==> P g) ==> P f` THEN 
  DISCH_THEN MATCH_MP_TAC THEN 
  ASM_REWRITE_TAC [] THEN 
  REPEAT STRIP_TAC THEN RES_TAC THEN 
  ANTE_RES_THEN ACCEPT_TAC (REFL (Term`fmla_size g`)))));

val _ = save_thm("fmla_size_ind",fmla_size_ind);

(*********************************)
(* Induction on size of formulas *)
(*********************************)
val fmla_size_induction =
TAC_PROOF
(([],
 ``!P. P tt /\ P ff /\ (!s. P (propmm s)) /\
     (!f g. P f /\ P g ==> P (f andmm g)) /\ 
     (!f g. P f /\ P g ==> P (f ormm g)) /\
     (!Actions f. P f ==> P(Box Actions f)) /\
     (!Actions f. P f ==> P(Dia Actions f)) /\
     (!f. (!g. ((fmla_size g = fmla_size f) ==> P g)) ==> !s. P (nu s f)) /\
     (!f. (!g. ((fmla_size g = fmla_size f) ==> P g)) ==> !s. P (mu s f)) ==>
     !f. P f``),
 (REPEAT STRIP_TAC THEN 
  (SUBGOAL_THEN (Term`?n. fmla_size f = n`) MP_TAC
      THEN1 (Q_TAC EXISTS_TAC `fmla_size f` THEN REFL_TAC)) THEN 
  CONV_TAC LEFT_IMP_EXISTS_CONV THEN GEN_TAC THEN 
  SPEC_TAC (Term`f:('a,'b)mmForm`, Term`f:('a,'b)mmForm`) THEN 
  SPEC_TAC (Term`n:num`, Term`n:num`) THEN 
  MATCH_MP_TAC fmla_size_ind THEN 
  Induct THEN ASM_REWRITE_TAC [] THEN 
  Q_TAC UNDISCH_TAC `P tt` THEN DISCH_THEN (fn _ => ALL_TAC) THEN
  Q_TAC UNDISCH_TAC `P ff` THEN DISCH_THEN (fn _ => ALL_TAC) THENL
[(DISCH_TAC THEN
  SUBGOAL_THEN 
  (``fmla_size f < fmla_size (f andmm f') /\ fmla_size f' < fmla_size (f andmm f')``)
  (fn cj => STRIP_ASSUME_TAC cj THEN RES_TAC THEN RES_TAC) THEN 
  REWRITE_TAC [fmla_size_def] THEN numLib.ARITH_TAC),
 (DISCH_TAC THEN
  SUBGOAL_THEN 
  (``fmla_size f < fmla_size (f ormm f') /\ fmla_size f' < fmla_size (f ormm f')``)
  (fn cj => STRIP_ASSUME_TAC cj THEN RES_TAC THEN RES_TAC) THEN 
  REWRITE_TAC [fmla_size_def] THEN numLib.ARITH_TAC),
  (GEN_TAC THEN
  DISCH_TAC THEN
  PAT_ASSUM ``!g.fmla_size g < fmla_size (Box f' f) ==> P g``
  (fn th => ASSUME_TAC (SPEC ``f:('a,'b)mmForm`` th)) THEN
  SUBGOAL_THEN
  (``fmla_size f < fmla_size (Box f' f)``)
  (fn th => ASSUME_TAC th) THENL 
  [(REWRITE_TAC[fmla_size_def] THEN numLib.ARITH_TAC),
   (RES_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[])]),
  (GEN_TAC THEN
  DISCH_TAC THEN
  PAT_ASSUM ``!g.fmla_size g < fmla_size (Dia f' f) ==> P g``
  (fn th => ASSUME_TAC (SPEC ``f:('a,'b)mmForm`` th)) THEN
  SUBGOAL_THEN
  (``fmla_size f < fmla_size (Dia f' f)``)
  (fn th => ASSUME_TAC th) THENL 
  [(REWRITE_TAC[fmla_size_def] THEN numLib.ARITH_TAC),
   (RES_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[])]),
   (REPEAT STRIP_TAC THEN 
   MATCH_MP_TAC 
   (ASSUME 
    ``!(f:('a,'b)mmForm). (!(g:('a,'b)mmForm). 
       (fmla_size g = fmla_size f) ==> P g) ==> !(s:'b). P (nu s f)``) THEN 
   REPEAT STRIP_TAC THEN 
   SUBGOAL_THEN ``fmla_size (g:('a,'b)mmForm) < fmla_size (nu (s:'b) (f:('a,'b)mmForm))``
        (ANTE_RES_THEN ACCEPT_TAC) THEN 
   ASM_REWRITE_TAC [fmla_size_def] THEN
   REWRITE_TAC[numLib.ARITH_CONV ``fmla_size (f:('a,'b)mmForm) < 1 + fmla_size f``] THEN
   PAT_ASSUM 
   ``fmla_size g = fmla_size f``
   (fn th2 => 
    (PAT_ASSUM
     ``!g.fmla_size g < fmla_size (nu p f) ==> P g``
      (fn th1 => ASSUME_TAC(REWRITE_RULE[th2] (SPEC ``g:('a,'b)mmForm`` th1))))) THEN
   PAT_ASSUM
   ``fmla_size f < fmla_size (nu p f) ==> (P g)``
    (fn th => 
     ACCEPT_TAC
     (REWRITE_RULE
      [fmla_size_def,
       (numLib.ARITH_CONV ``fmla_size (f:('a,'b)mmForm) < 1 + fmla_size f``)] th))),
  (REPEAT STRIP_TAC THEN 
   MATCH_MP_TAC 
   (ASSUME 
    ``!(f:('a,'b)mmForm). (!(g:('a,'b)mmForm). 
       (fmla_size g = fmla_size f) ==> P g) ==> !(s:'b). P (mu s f)``) THEN 
   REPEAT STRIP_TAC THEN 
   SUBGOAL_THEN ``fmla_size (g:('a,'b)mmForm) < fmla_size (mu (s:'b) (f:('a,'b)mmForm))``
        (ANTE_RES_THEN ACCEPT_TAC) THEN 
   ASM_REWRITE_TAC [fmla_size_def] THEN
   REWRITE_TAC[numLib.ARITH_CONV ``fmla_size (f:('a,'b)mmForm) < 1 + fmla_size f``] THEN
   PAT_ASSUM 
   ``fmla_size g = fmla_size f``
   (fn th2 => 
    (PAT_ASSUM
     ``!g.fmla_size g < fmla_size (mu p f) ==> P g``
      (fn th1 => ASSUME_TAC(REWRITE_RULE[th2] (SPEC ``g:('a,'b)mmForm`` th1))))) THEN
   PAT_ASSUM
   ``fmla_size f < fmla_size (mu p f) ==> (P g)``
    (fn th => 
     ACCEPT_TAC
     (REWRITE_RULE
      [fmla_size_def,
       (numLib.ARITH_CONV ``fmla_size (f:('a,'b)mmForm) < 1 + fmla_size f``)] th)))]));

val _ = save_thm("fmla_size_induction",fmla_size_induction);

(* As promised: Subst related to l_Sub at last *)

(* Identities for fv *)
val fv_lemma1 =
TAC_PROOF
(([],``fv ((Y,Y) :: l) X = (if (fv l X) = Y then Y else (fv l X))``),
 (REWRITE_TAC[fv_def,LET_DEF] THEN
 CONV_TAC(DEPTH_CONV BETA_CONV) THEN
 REFL_TAC));

val fv_lemma2 =
TAC_PROOF
(([],``fv [(Y,Y)] X = X``),
 REWRITE_TAC [fv_def,LET_DEF] THEN
 CONV_TAC(DEPTH_CONV BETA_CONV) THEN
 PROVE_TAC[]);

val l_Sub_ID =
TAC_PROOF
(([],``!Fm.l_Sub [(X,X)] Fm = Fm``),
(MATCH_MP_TAC
(BETA_RULE 
 (SPEC 
  ``\(Fm:('a,'b)mmForm).(!(X:'b).
     l_Sub [(X,X)] Fm = Fm)`` fmla_size_induction)) THEN
REPEAT STRIP_TAC THEN
ASM_REWRITE_TAC[l_Sub_def,fv_lemma2] THEN
REWRITE_TAC[LET_DEF] THEN
CONV_TAC(DEPTH_CONV BETA_CONV) THEN
REWRITE_TAC
 [(PairedLambda.PAIRED_BETA_CONV 
   ``(\(Z',l'). nu Z' (l_Sub l' f))(gv [(X,X)] s (frees f),gl [(X,X)] s (frees f))``),
  (PairedLambda.PAIRED_BETA_CONV 
   ``(\(Z',l'). mu Z' (l_Sub l' f))(gv [(X,X)] s (frees f),gl [(X,X)] s (frees f))``),
   gv_def,gl_def,gf_def,rf_def,LET_DEF] THEN
CONV_TAC(DEPTH_CONV BETA_CONV) THEN
ASM_REWRITE_TAC
[(PairedLambda.PAIRED_BETA_CONV 
  ``((λ(fs',Z').
             if X ∉ fs' ∨ (X = Z') then
               []
             else if X = Z' then
               [(X,X); (Z',variant (X INSERT fs') Z')]
             else
               [(X,X)]) (gf [] (frees f),fv [] s))``),
 (PairedLambda.PAIRED_BETA_CONV 
  ``((λ(fs',Z').
             if X ∉ fs' ∨ (X = Z') then
               []
             else if X = Z' then
               [(X,X); (Z',variant (X INSERT fs') Z')]
             else
               [(X,X)]) (gf [] (frees f),fv [] s))``),
 fv_def,gv_def,gf_def] THEN
REPEAT COND_CASES_TAC THEN
REWRITE_TAC[fv_def,l_Sub_nil,l_Sub_def,LET_DEF] THEN
CONV_TAC(DEPTH_CONV BETA_CONV) THEN
ASM_REWRITE_TAC[] THEN
REPEAT COND_CASES_TAC THEN
PAT_ASSUM 
 ``~(A \/ B)`` 
 (fn th => STRIP_ASSUME_TAC (REWRITE_RULE[DE_MORGAN_THM]th))THEN
PAT_ASSUM
``!g.P ==> Q``
(fn th => REWRITE_TAC[REWRITE_RULE[](SPEC ``f:('a,'b)mmForm``th)]) THEN
PROVE_TAC[]));

val _ = save_thm("l_Sub_ID",l_Sub_ID);


val l_Sub_ID_CONS =
TAC_PROOF(([],``!(f:('a,'b)mmForm) l.l_Sub ((X,X)::l) f = l_Sub l f``),
(MATCH_MP_TAC
(BETA_RULE 
 (SPEC 
  ``\(f:('a,'b)mmForm).(!(l:('b#'b)list).
     l_Sub ((X,X)::l) f = (l_Sub l f))`` fmla_size_induction))
THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THENL
[((* tt *) REWRITE_TAC[l_Sub_def,fv_def])
,((* ff *) REWRITE_TAC[l_Sub_def,fv_def])
,((* propmm *) REWRITE_TAC[l_Sub_def,fv_def] 
  THEN REWRITE_TAC[LET_DEF] THEN CONV_TAC(DEPTH_CONV BETA_CONV)
 THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [])
,((* andmm *) REWRITE_TAC[l_Sub_def,fv_def] THEN ASM_REWRITE_TAC[])
,((* ormm *) REWRITE_TAC[l_Sub_def,fv_def]  THEN ASM_REWRITE_TAC[])
,((* Box *) REWRITE_TAC[l_Sub_def,fv_def]  THEN ASM_REWRITE_TAC[])
,((* Dia *) REWRITE_TAC[l_Sub_def,fv_def]  THEN ASM_REWRITE_TAC[])
,((* nu *) REWRITE_TAC[l_Sub_def,LET_DEF] THEN CONV_TAC(DEPTH_CONV BETA_CONV)
 THEN REWRITE_TAC
 [(PairedLambda.PAIRED_BETA_CONV 
 ``(λ(Z',l'). nu Z' (l_Sub l' f))
   (gv ((X,X)::l) s (frees f),gl ((X,X)::l) s (frees f))``),
  (PairedLambda.PAIRED_BETA_CONV
   ``(λ(Z',l'). nu Z' (l_Sub l' f)) (gv l s (frees f),gl l s (frees f))``),
  gv_def,gl_def]
THEN REWRITE_TAC[LET_DEF] THEN CONV_TAC(DEPTH_CONV BETA_CONV)
THEN REWRITE_TAC
     [(PairedLambda.PAIRED_BETA_CONV 
       ``((λ(fs',Z').
               if X ∉ fs' ∨ (X = Z') then
                 gl l s (frees f)
               else if X = Z' then
                 (X,X)::(Z',variant (X INSERT fs') Z')::gl l s (frees f)
               else
                 (X,X)::gl l s (frees f))
              (gf (gl l s (frees f)) (frees f),fv (gl l s (frees f)) s))``),
      (PairedLambda.PAIRED_BETA_CONV 
       ``((λ(fs',Z').
               if X ∉ fs' ∨ (X = Z') then
                 gl l s (frees f)
               else if X = Z' then
                 (X,X)::(Z',variant (X INSERT fs') Z')::gl l s (frees f)
               else
                 (X,X)::gl l s (frees f))
              (gf (gl l s (frees f)) (frees f),fv (gl l s (frees f)) s))``)]
THEN REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[fv_def,LET_DEF]
THEN CONV_TAC(DEPTH_CONV BETA_CONV)
THEN PAT_ASSUM``~(P \/ Q)`` (fn th => STRIP_ASSUME_TAC(REWRITE_RULE[DE_MORGAN_THM]th))
THEN PAT_ASSUM ``~(X = Y)`` (fn th => REWRITE_TAC[NOT_EQ_SYM th]) THEN 
 PAT_ASSUM ``!g. P`` (fn th => REWRITE_TAC[REWRITE_RULE[](ISPEC``f:('a,'b)mmForm``th)]))
,((* mu *) REWRITE_TAC[l_Sub_def,LET_DEF] THEN CONV_TAC(DEPTH_CONV BETA_CONV)
 THEN REWRITE_TAC
 [(PairedLambda.PAIRED_BETA_CONV 
 ``(λ(Z',l'). mu Z' (l_Sub l' f))
   (gv ((X,X)::l) s (frees f),gl ((X,X)::l) s (frees f))``),
  (PairedLambda.PAIRED_BETA_CONV
   ``(λ(Z',l'). mu Z' (l_Sub l' f)) (gv l s (frees f),gl l s (frees f))``),
  gv_def,gl_def]
THEN REWRITE_TAC[LET_DEF] THEN CONV_TAC(DEPTH_CONV BETA_CONV)
THEN REWRITE_TAC
     [(PairedLambda.PAIRED_BETA_CONV 
       ``((λ(fs',Z').
               if X ∉ fs' ∨ (X = Z') then
                 gl l s (frees f)
               else if X = Z' then
                 (X,X)::(Z',variant (X INSERT fs') Z')::gl l s (frees f)
               else
                 (X,X)::gl l s (frees f))
              (gf (gl l s (frees f)) (frees f),fv (gl l s (frees f)) s))``),
      (PairedLambda.PAIRED_BETA_CONV 
       ``((λ(fs',Z').
               if X ∉ fs' ∨ (X = Z') then
                 gl l s (frees f)
               else if X = Z' then
                 (X,X)::(Z',variant (X INSERT fs') Z')::gl l s (frees f)
               else
                 (X,X)::gl l s (frees f))
              (gf (gl l s (frees f)) (frees f),fv (gl l s (frees f)) s))``)]
THEN REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[fv_def,LET_DEF]
THEN CONV_TAC(DEPTH_CONV BETA_CONV)
THEN PAT_ASSUM``~(P \/ Q)`` (fn th => STRIP_ASSUME_TAC(REWRITE_RULE[DE_MORGAN_THM]th))
THEN PAT_ASSUM ``~(X = Y)`` (fn th => REWRITE_TAC[NOT_EQ_SYM th]) THEN 
 PAT_ASSUM ``!g. P`` (fn th => REWRITE_TAC[REWRITE_RULE[](ISPEC``f:('a,'b)mmForm``th)]))]));

val _ = save_thm("l_Sub_ID_CONS",l_Sub_ID_CONS);

val lem1 = 
REWRITE_RULE[DE_MORGAN_THM,IN_INSERT]
(TAC_PROOF(
([],
 ``!(s:'b)(f:('a,'b)mmForm).
   INFINITE (UNIV:'b set) ==> ~(variant (s INSERT frees f) s IN (s INSERT frees f))``),
PROVE_TAC[variant_not_in,frees_finite,FINITE_INSERT]));

val lem2 = GSYM
(TAC_PROOF(
([``(X:'b) IN frees (f:('a,'b)mmForm)``,``!(s:'b) (f:('a,'b)mmForm). variant (s INSERT frees f) s NOTIN frees f``],``~(X = variant ((s:'b) INSERT frees (f:('a,'b)mmForm)) s)``),
(MATCH_MP_TAC in_not_in_not_eq 
 THEN EXISTS_TAC ``frees (f:('a,'b)mmForm)`` THEN AR)));

val lem3 =
TAC_PROOF(([],``(!(g:('a,'b)mmForm).
            (fmla_size g = fmla_size f) ==>
            !X Y. INFINITE 𝕌(:β) ==> (Subst (propmm Y) X g = l_Sub [(X,Y)] g)) =
            (!(g:('a,'b)mmForm).
            INFINITE 𝕌(:β) ==> (fmla_size g = fmla_size f) ==>
            !X Y. (Subst (propmm Y) X g = l_Sub [(X,Y)] g))``),
PROVE_TAC[]);

val Subst_l_Sub =
TAC_PROOF
(([],
 ``!(f:('a,'b)mmForm) (X:'b) (Y:'b). INFINITE (UNIV:'b set) ==> (Subst (propmm Y) X f = l_Sub [(X,Y)] f)``),
(MATCH_MP_TAC
(BETA_RULE 
 (SPEC 
  ``\(f:('a,'b)mmForm).(!(X:'b)(Y:'b).
     INFINITE (UNIV:'b set) ==> (Subst (propmm Y) X f = l_Sub [(X,Y)] f))`` fmla_size_induction)) THEN
(* We add RES_TAC to deal with implication involving INFINITE (UNIV:'b set) *)
REPEAT STRIP_TAC THEN RES_TAC
THEN ASM_REWRITE_TAC[l_Sub_def, Subst_def, gv_def, fv_def] THENL
(* 3 subgoals to prove *)
[((* propmm *) CONV_TAC (DEPTH_CONV let_CONV THENC (RAND_CONV (REWR_CONV COND_RAND)))
 THEN REFL_TAC)
,(* nu *) REWRITE_TAC [gl_def] THEN CONV_TAC (DEPTH_CONV let_CONV)
 THEN REWRITE_TAC [gf_def, fv_def]
 THEN COND_CASES_TAC THEN REWRITE_TAC [] THENL
 (* 2 subgoals to prove *)
 [(REWRITE_TAC [fv_def, l_Sub_nil])
  ,Q_TAC UNDISCH_TAC `~(~(X IN frees f) \/ (X = s))`
   THEN REWRITE_TAC [DE_MORGAN_THM] THEN STRIP_TAC
   THEN ASM_REWRITE_TAC
        [frees_def,CONV_RULE (ONCE_DEPTH_CONV (RAND_CONV SYM_CONV)) IN_SING]
   THEN COND_CASES_TAC THEN REWRITE_TAC [] THENL
   (* 2 subgoals to prove *)
   [(SUBGOAL_THEN (Term`!x:'b s. {x} UNION s = x INSERT s`) (REWRITE_TAC o ulist)
     THEN1 REWRITE_TAC [EXTENSION, IN_SING, IN_UNION, IN_INSERT])
    THEN ASM_REWRITE_TAC [fv_def] THEN CONV_TAC (DEPTH_CONV let_CONV) THEN AR
    (* This is the step where we need to account for INFINITE UNIV:'a set *)
    (* We use lem1 instead of SUBGOAL_THEN                                *)
    (* ==  instead of the following: ==
    THEN (SUBGOAL_THEN (Term
         `~(variant (s INSERT frees f) s IN (s INSERT frees f))`)
         (STRIP_ASSUME_TAC o REWRITE_RULE [DE_MORGAN_THM, IN_INSERT])
         THEN1 (MATCH_MP_TAC (GEN_ALL(UNDISCH(SPEC_ALL(ISPEC ``s:'b`` variant_not_in))))
             THEN REWRITE_TAC [FINITE_INSERT]
             THEN MATCH_ACCEPT_TAC frees_finite))
       == end instead of following == *)
    THEN (* Our substitute for SUBGOAL_THEN above *) IMP_RES_TAC lem1
    (* == we rewrite with lem2 instead of SUBGOAL_THEN 
    THEN (SUBGOAL_THEN (Term`~(X = variant (s INSERT frees f) s)`)
          (REWRITE_TAC o ulist o GSYM)
           THEN1 (MATCH_MP_TAC in_not_in_not_eq
           THEN Q_TAC EXISTS_TAC `frees f` THEN AR))
       == end rewrite with lem2 instead of SUBGOAL_THEN == *)
    THEN REWRITE_TAC [lem2]
    THEN AP_TERM_TAC 
    (* We need to deal with INFINITE (UNIV:'b set) in the inductive hypothesis, *)
    (* which differs from Lockwood's proof because he assumed all variables     *)
    (* were strings. Rewrite the hypothesis to move INFINITE first.             *)
    THEN PAT_ASSUM
         ``!g.P ==> Q``
         (fn th => ASSUME_TAC(REWRITE_RULE[lem3]th) THEN RES_TAC)
    (* Back to Lockwood's proof *)
    THEN (SUBGOAL_THEN (Term
           `fmla_size (l_Sub [(s, variant (s INSERT frees f) s)] f) = fmla_size f`)
          (ANTE_RES_THEN (REWRITE_TAC o ulist))
          THEN1 REWRITE_TAC[l_Sub_same_size])
    THEN (SUBGOAL_THEN (Term`!A:'b#'b B. [A; B] = APPEND [A] [B]`)
          (REWRITE_TAC o ulist)
          THEN1 REWRITE_TAC [APPEND])
    (* Must deal with INFINITE antecedent in l_Sub_append *)
    (* Use IMP_RES_TAC to strip away INFINITE antecedent  *)
    (* then MATCH_MP_TAC within PAT_ASSUM to generate new *)
    (* goal.                                              *)
    THEN IMP_RES_TAC (GSYM l_Sub_append)
    (* === use PAT_ASSUM instead ===
    THEN MATCH_MP_TAC (GSYM l_Sub_append)
       === end use PAT_ASSUM instead === *)
    THEN PAT_ASSUM
         ``!m P. ok_r m (frees P) ==> A`` (fn th => MATCH_MP_TAC th)
    THEN ASM_REWRITE_TAC [ok_r_def, gf_def]
   ,ASM_REWRITE_TAC [fv_def]
    THEN CONV_TAC (RAND_CONV
         (ONCE_DEPTH_CONV let_CONV THENC ONCE_DEPTH_CONV SYM_CONV))
    (* We need to deal with INFINITE (UNIV:'b set) in the inductive hypothesis, *)
    (* which differs from Lockwood's proof because he assumed all variables     *)
    (* were strings. Rewrite the hypothesis to move INFINITE first.             *)
    THEN PAT_ASSUM
         ``!g.P ==> Q``
         (fn th => ASSUME_TAC(REWRITE_RULE[lem3]th) THEN RES_TAC)
    (* back to Lockwood's proof *)
    THEN ANTE_RES_THEN (ASM_REWRITE_TAC o ulist) (REFL (Term`fmla_size f`))]]
,(* mu *) REWRITE_TAC [gl_def] THEN CONV_TAC (DEPTH_CONV let_CONV)
 THEN REWRITE_TAC [gf_def, fv_def]
 THEN COND_CASES_TAC THEN REWRITE_TAC [] THENL
 (* 2 subgoals to prove *)
 [(REWRITE_TAC [fv_def, l_Sub_nil])
  ,Q_TAC UNDISCH_TAC `~(~(X IN frees f) \/ (X = s))`
   THEN REWRITE_TAC [DE_MORGAN_THM] THEN STRIP_TAC
   THEN ASM_REWRITE_TAC
        [frees_def,CONV_RULE (ONCE_DEPTH_CONV (RAND_CONV SYM_CONV)) IN_SING]
   THEN COND_CASES_TAC THEN REWRITE_TAC [] THENL
   (* 2 subgoals to prove *)
   [(SUBGOAL_THEN (Term`!x:'b s. {x} UNION s = x INSERT s`) (REWRITE_TAC o ulist)
     THEN1 REWRITE_TAC [EXTENSION, IN_SING, IN_UNION, IN_INSERT])
    THEN ASM_REWRITE_TAC [fv_def] THEN CONV_TAC (DEPTH_CONV let_CONV) THEN AR
    (* This is the step where we need to account for INFINITE UNIV:'a set *)
    (* We use lem1 instead of SUBGOAL_THEN                                *)
    (* ==  instead of the following: ==
    THEN (SUBGOAL_THEN (Term
         `~(variant (s INSERT frees f) s IN (s INSERT frees f))`)
         (STRIP_ASSUME_TAC o REWRITE_RULE [DE_MORGAN_THM, IN_INSERT])
         THEN1 (MATCH_MP_TAC (GEN_ALL(UNDISCH(SPEC_ALL(ISPEC ``s:'b`` variant_not_in))))
             THEN REWRITE_TAC [FINITE_INSERT]
             THEN MATCH_ACCEPT_TAC frees_finite))
       == end instead of following == *)
    THEN (* Our substitute for SUBGOAL_THEN above *) IMP_RES_TAC lem1
    (* == we rewrite with lem2 instead of SUBGOAL_THEN 
    THEN (SUBGOAL_THEN (Term`~(X = variant (s INSERT frees f) s)`)
          (REWRITE_TAC o ulist o GSYM)
           THEN1 (MATCH_MP_TAC in_not_in_not_eq
           THEN Q_TAC EXISTS_TAC `frees f` THEN AR))
       == end rewrite with lem2 instead of SUBGOAL_THEN == *)
    THEN REWRITE_TAC [lem2]
    THEN AP_TERM_TAC 
    (* We need to deal with INFINITE (UNIV:'b set) in the inductive hypothesis, *)
    (* which differs from Lockwood's proof because he assumed all variables     *)
    (* were strings. Rewrite the hypothesis to move INFINITE first.             *)
    THEN PAT_ASSUM
         ``!g.P ==> Q``
         (fn th => ASSUME_TAC(REWRITE_RULE[lem3]th) THEN RES_TAC)
    (* Back to Lockwood's proof *)
    THEN (SUBGOAL_THEN (Term
           `fmla_size (l_Sub [(s, variant (s INSERT frees f) s)] f) = fmla_size f`)
          (ANTE_RES_THEN (REWRITE_TAC o ulist))
          THEN1 REWRITE_TAC[l_Sub_same_size])
    THEN (SUBGOAL_THEN (Term`!A:'b#'b B. [A; B] = APPEND [A] [B]`)
          (REWRITE_TAC o ulist)
          THEN1 REWRITE_TAC [APPEND])
    (* Must deal with INFINITE antecedent in l_Sub_append *)
    (* Use IMP_RES_TAC to strip away INFINITE antecedent  *)
    (* then MATCH_MP_TAC within PAT_ASSUM to generate new *)
    (* goal.                                              *)
    THEN IMP_RES_TAC (GSYM l_Sub_append)
    (* === use PAT_ASSUM instead ===
    THEN MATCH_MP_TAC (GSYM l_Sub_append)
       === end use PAT_ASSUM instead === *)
    THEN PAT_ASSUM
         ``!m P. ok_r m (frees P) ==> A`` (fn th => MATCH_MP_TAC th)
    THEN ASM_REWRITE_TAC [ok_r_def, gf_def]
   ,ASM_REWRITE_TAC [fv_def]
    THEN CONV_TAC (RAND_CONV
         (ONCE_DEPTH_CONV let_CONV THENC ONCE_DEPTH_CONV SYM_CONV))
    (* We need to deal with INFINITE (UNIV:'b set) in the inductive hypothesis, *)
    (* which differs from Lockwood's proof because he assumed all variables     *)
    (* were strings. Rewrite the hypothesis to move INFINITE first.             *)
    THEN PAT_ASSUM
         ``!g.P ==> Q``
         (fn th => ASSUME_TAC(REWRITE_RULE[lem3]th) THEN RES_TAC)
    (* back to Lockwood's proof *)
    THEN ANTE_RES_THEN (ASM_REWRITE_TAC o ulist) (REFL (Term`fmla_size f`))]]]));

val _ = save_thm("Subst_l_Sub",Subst_l_Sub);

(* At last, Subst as we would like to think of it defined. *)
val Subst =
TAC_PROOF
(([],
 ``INFINITE (UNIV:'b set) ==> ((Subst p (X:'b) (tt:('a,'b)mmForm) = tt) /\
 (Subst p X ff = ff) /\
 (Subst p X (propmm Z) = (if Z = X then p else propmm Z)) /\
 (Subst p X (Fm1 andmm Fm2) = (Subst p X Fm1) andmm (Subst p X Fm2)) /\
 (Subst p X (Fm1 ormm Fm2) = (Subst p X Fm1) ormm (Subst p X Fm2)) /\
 (Subst p X (Box Actions Fm) = Box Actions (Subst p X Fm)) /\
 (Subst p X (Dia Actions Fm) = Dia Actions (Subst p X Fm)) /\
 (Subst p X (nu Z Fm) = let fs = frees Fm
  in (if ~(X IN frees (nu Z Fm)) then nu Z Fm
      else (if Z IN frees p then
             let Z' = variant (frees p UNION fs) Z
             in nu Z' (Subst p X (Subst (propmm Z') Z Fm))
            else nu Z (Subst p X Fm)))) /\
 (Subst p X (mu Z Fm) = let fs = frees Fm
  in (if ~(X IN frees (mu Z Fm)) then mu Z Fm
      else (if Z IN frees p then
             let Z' = variant (frees p UNION fs) Z
             in mu Z' (Subst p X (Subst (propmm Z') Z Fm))
            else mu Z (Subst p X Fm)))))``),
((* need to account for INFINITE (UNIV:'b set)  *)
(* this accounts for DISCH_TAC and IMP_RES_TAC *)
 DISCH_TAC THEN IMP_RES_TAC Subst_l_Sub THEN ASM_REWRITE_TAC [Subst_def]
 THEN REWRITE_TAC [fv_def, gv_def, gl_def]
 THEN CONV_TAC (DEPTH_CONV let_CONV)
 THEN REWRITE_TAC [gf_def,l_Sub_nil,frees_def,IN_SING,IN_DELETE,DE_MORGAN_THM]));

val _ = save_thm("Subst",Subst);

val Subst_same_size =  
TAC_PROOF(([],Term
`!(Fm:('a,'b)mmForm) (X:'b) (Z:'b). INFINITE (UNIV:'b set) ==> (fmla_size (Subst (propmm X) Z Fm) = fmla_size Fm)`),
(REPEAT GEN_TAC THEN DISCH_TAC THEN IMP_RES_TAC Subst_l_Sub THEN 
ASM_REWRITE_TAC [Subst_def, l_Sub_same_size]));

val _ = save_thm("Subst_same_size",Subst_same_size);

val Subst_not_free =
TAC_PROOF
(([],``!N X (Fm:('a,'b)mmForm). INFINITE (UNIV:'b set) ==> ~(X IN frees Fm) ==> (Subst N X Fm = Fm)``),
(GEN_TAC THEN GEN_TAC THEN Induct THEN STRIP_TAC THENL
[(* the following is to move INFINITE (UNIV:'b set) to the assumptions *)
(* tt *) ALL_TAC, (* ff *) ALL_TAC, (* propmm *) DISCH_TAC, (* andmm *) ALL_TAC,
(* ormm *) ALL_TAC, (* Box *) DISCH_TAC, (* Dia *) DISCH_TAC, (* nu *) DISCH_TAC,
(* mu *) DISCH_TAC]
THEN RES_TAC THEN ASM_REWRITE_TAC[(UNDISCH Subst),frees_def] THENL
[(* propmm *) REWRITE_TAC [CONV_RULE (ONCE_DEPTH_CONV (RAND_CONV SYM_CONV)) IN_SING]
 THEN REPEAT STRIP_TAC THEN AR
,(* andmm *) REWRITE_TAC [IN_UNION, DE_MORGAN_THM]
 THEN STRIP_TAC THEN RES_TAC THEN AR
,(* ormm *) REWRITE_TAC [IN_UNION, DE_MORGAN_THM]
 THEN STRIP_TAC THEN RES_TAC THEN AR
,(* Box *) DISCH_TAC THEN RES_TAC THEN AR
,(* Dia *) DISCH_TAC THEN RES_TAC THEN AR
,(* nu *) REWRITE_TAC [IN_DELETE, DE_MORGAN_THM]
 THEN CONV_TAC (ONCE_DEPTH_CONV let_CONV)
 THEN DISCH_TAC THEN AR
,(* mu *) REWRITE_TAC [IN_DELETE, DE_MORGAN_THM]
 THEN CONV_TAC (ONCE_DEPTH_CONV let_CONV)
 THEN DISCH_TAC THEN AR]));

val _ = save_thm("Subst_not_free",Subst_not_free);

val alpha_frees =
TAC_PROOF
(([],
``!Y X (Fm:('a,'b)mmForm). INFINITE (UNIV:'b set) ==> ~(Y IN frees Fm) ==> (frees (Subst (propmm Y) X Fm) = rf Y X (frees Fm))``),
(REPEAT STRIP_TAC THEN REWRITE_TAC [Subst_def, (UNDISCH (SPEC_ALL Subst_l_Sub))]
THEN (SUBGOAL_THEN (Term`ok_r [((X:'b),(Y:'b))] (frees (Fm:('a,'b)mmForm))`)
 (SUBST1_TAC o MATCH_MP (* need to take care of INFINITE *)
  (UNDISCH (SPEC_ALL frees_LEM))) THEN1 ASM_REWRITE_TAC [ok_r_def, gf_def])
THEN REWRITE_TAC [gf_def]));

val _ = save_thm("alpha_frees",alpha_frees);

val alpha_remove = 
TAC_PROOF
(([],``!(Y:'b)(X:'b)(Fm:('a,'b)mmForm). 
 INFINITE (UNIV:'b set) ==> ~(Y IN frees Fm) /\ ~(Y = X) ==>
          ~(X IN frees (Subst (propmm Y) X Fm))``),
(REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_THEN (STRIP_ASSUME_TAC o GSYM)
THEN IMP_RES_THEN (REWRITE_TAC o ulist) 
 ((* deal with INFINITE *)(UNDISCH(SPEC_ALL alpha_frees)))
THEN REWRITE_TAC [rf_def] THEN COND_CASES_TAC
THEN ASM_REWRITE_TAC [IN_INSERT, IN_DELETE]));

val _ = save_thm("alpha_remove",alpha_remove);

(* end of the section purely to do with substitution *)

(*******************************************************************)
(* The following are some lemmas used in the proof of setsat_lemma *)
(*******************************************************************)

val th1 = GEN_ALL(SYM(BETA_CONV ``(\E.(E,Trans,V) mmsat f) E``))
val th2 = 
 ISPECL 
 [``Fm:('a,'b)mmForm``,``Z:'b``, ``V:'b -> ('configuration set)``,
  ``Trans:'a -> 'configuration -> 'configuration -> bool``] mmsat_nu_gfp
val th3 = 
 ISPECL 
 [``Fm:('a,'b)mmForm``,``Z:'b``, ``V:'b -> ('configuration set)``,
  ``Trans:'a -> 'configuration -> 'configuration -> bool``] mmsat_mu_lfp
val th4 = 
 REWRITE_RULE
 [GEN_ALL th2]
 (ISPECL 
  [``Trans:'a -> 'configuration -> 'configuration -> bool``,
   ``nu (Z:'b) (Fm:('a,'b)mmForm)``,``V:'b -> ('configuration set)``] setsat_def)
val th5 = 
 REWRITE_RULE 
 [GEN_ALL th3]
 (ISPECL [``Trans:'a -> 'configuration -> 'configuration -> bool``,
          ``mu (Z:'b) (Fm:('a,'b)mmForm)``,``V:'b -> ('configuration set)``] setsat_def)

val satFun_lemma1 = 
TAC_PROOF
(([],
  ``(\(E:'configuration set).
     satFun (Trans:'a -> 'configuration -> 'configuration -> bool) (Z:'b) V (Fm:('a,'b)mmForm) E) = 
    (\E.(mmfn Trans Fm (UNIV:'configuration set) (mmUpdate Z V E)))``),
  PROVE_TAC[satFun_def]);

val satFun_lemma2 =
TAC_PROOF(([],``satFun Trans Z V Fm = (\E.satFun Trans Z V Fm E)``),
PROVE_TAC[]);

val mmUpdate_lemma =
SYM(TAC_PROOF(([],``mmUpdate Z V E = \Y.mmUpdate Z V E Y``),
PROVE_TAC[]));

(************************************************************)
(* This lemma corresponds to Lockwood's original definition *)
(* which we will use in subsequent proofs                   *)
(************************************************************)
val setsat_lemma =
TAC_PROOF(([],
``(!V. setsat Trans (tt:('a,'b)mmForm) V = (UNIV:'configuration set)) /\
  (!V. setsat Trans (ff:('a,'b)mmForm) V = ({}:'configuration set)) /\
  (!(Z:'b) V. setsat Trans (propmm Z) V = V Z) /\
  (!(Fm1:('a,'b)mmForm) Fm2 V. setsat Trans (Fm1 andmm Fm2) V = 
     (setsat Trans Fm1 V INTER setsat Trans Fm2 V)) /\
  (!(Fm1:('a,'b)mmForm) Fm2 V. setsat Trans (Fm1 ormm Fm2) V = 
     (setsat Trans Fm1 V UNION setsat Trans Fm2 V)) /\
  (!Z (Fm:('a,'b)mmForm) V. setsat Trans (Box (Actions:'a set) Fm) (V:'b -> 'configuration set) =
     {E | !(E':'configuration)(a:'a).Trans a E E' ==> a IN Actions ==> (E',Trans,V) mmsat Fm}) /\
  (!Z (Fm:('a,'b)mmForm) V. setsat Trans (Dia (Actions:'a set) Fm) (V:'b -> 'configuration set) =
     {E | ?(E':'configuration)(a:'a).Trans a E E'/\ a IN Actions /\ (E',Trans,V) mmsat Fm}) /\
  (!(Z:'b) (Fm:('a,'b)mmForm) V. setsat Trans (nu Z Fm) V = gfp (\Q. setsat Trans Fm (extend_env Z Q V))) /\
  (!(Z:'b) (Fm:('a,'b)mmForm) V. setsat Trans (mu Z Fm) V = lfp (\Q. setsat Trans Fm (extend_env Z Q V)))``),
(REWRITE_TAC[th4,th5,satFun_def] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[setsat_def,mmsat_def,GSPEC_T,GSPEC_F,GSPEC_ID]
 THEN ONCE_REWRITE_TAC[th1] THEN REWRITE_TAC[GSPEC_AND,GSPEC_OR]
 THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN AP_TERM_TAC 
 THEN REWRITE_TAC[satFun_lemma1,satFun_lemma2,mmfn_def,IN_UNIV,extend_env_mmUpdate_EQ]
 THEN ABS_TAC THEN REWRITE_TAC[mmUpdate_lemma]));

val _ = save_thm("setsat_lemma",setsat_lemma);


val EQ_SUBSET_SUBSET =
TAC_PROOF(([],``!(s1:'a set)(s2:'a set). (s1 = s2) = (s1 SUBSET s2) /\ (s2 SUBSET s1)``),
(REWRITE_TAC[SUBSET_DEF,IN_DEF] THEN CONV_TAC(DEPTH_CONV BETA_CONV) 
 THEN REWRITE_TAC[FUN_EQ_THM] THEN REWRITE_TAC[EQ_IMP_THM]
 THEN REWRITE_TAC
 [GSYM 
  (BETA_RULE
   (SPECL
    [``\x:'a.((s1:'a->bool) x ==> (s2:'a->bool) x)``,
     ``\x:'a.((s2:'a->bool) x ==> (s1:'a->bool) x)``]
    FORALL_AND_THM))]));

val _ = save_thm("EQ_SUBSET_SUBSET",EQ_SUBSET_SUBSET);

(* A helper theorem use to prove silly_extend *)
val th1 =
GSYM(REWRITE_RULE[GSYM EQ_IMP_THM]
 (BETA_RULE
  (ISPECL
    [``\x.((x,Trans,extend_env Z a V) mmsat (Fm:('a,'b)mmForm) ==> (x,Trans,V) mmsat (Fm:('a,'b)mmForm))``,
     ``\x.((x,Trans,V) mmsat (Fm:('a,'b)mmForm) ==> (x,Trans,extend_env Z a V) mmsat (Fm:('a,'b)mmForm))``]
    FORALL_AND_THM)))

val silly_extend = 
TAC_PROOF
(([],``!(Trans:'a -> 'configuration -> 'configuration -> bool) 
        (Z:'b) (Fm:('a,'b)mmForm) a V. ~(Z IN frees Fm) ==>
                   (setsat Trans Fm (extend_env Z a V) = setsat Trans Fm V)``),
(GEN_TAC THEN GEN_TAC THEN Induct
THEN REWRITE_TAC [frees_def, IN_SING, IN_UNION, DE_MORGAN_THM, IN_DELETE]
THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [setsat_lemma] THENL
[REWRITE_TAC [extend_env_def]
 THEN BETA_TAC THEN CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV SYM_CONV))
 THEN AR
,RES_TAC THEN AR
,RES_TAC THEN AR
,(* Box *) RES_TAC 
 THEN PAT_ASSUM
       ``!a V.P = Q`` 
       (fn th => 
        ASSUME_TAC
        (REWRITE_RULE
         [setsat_def,EQ_SUBSET_SUBSET,SUBSET_DEF,
          (SET_SPEC_CONV``x ∈ {E | (E,Trans,V) mmsat Fm}``),th1] th))
 THEN AR
,(* Dia *) RES_TAC 
 THEN PAT_ASSUM
       ``!a V.P = Q`` 
       (fn th => 
        ASSUME_TAC
        (REWRITE_RULE
         [setsat_def,EQ_SUBSET_SUBSET,SUBSET_DEF,
          (SET_SPEC_CONV``x ∈ {E | (E,Trans,V) mmsat Fm}``),th1] th))
 THEN AR
,(* nu *) Q_TAC ASM_CASES_TAC `p = Z` THENL
 [ASM_REWRITE_TAC [last_extension_counts]
 ,IMP_RES_THEN (fn th => REWRITE_TAC [th]) uneq_extensions_commute
  THEN RES_TAC THEN AR
 ]
,(* nu *) ASM_REWRITE_TAC [last_extension_counts]
,(* mu *)Q_TAC ASM_CASES_TAC `p = Z` THENL
 [ASM_REWRITE_TAC [last_extension_counts]
 ,IMP_RES_THEN (fn th => REWRITE_TAC [th]) uneq_extensions_commute
  THEN RES_TAC THEN AR
 ]
,(* mu *)ASM_REWRITE_TAC [last_extension_counts]]));

val _ = save_thm ("silly_extend",silly_extend);

(* alpha_LEM shows that alpha-conversion (done with Subst), with
 corresponding change of binding in the environment, preserves the
 value returned by setsat. *)

(* A helper theorem use to prove alpha_LEM *)
val th1 =
GSYM(REWRITE_RULE[GSYM EQ_IMP_THM]
 (BETA_RULE
  (ISPECL
    [``\x.(((x,Trans,extend_env X' Q V) mmsat (Subst (propmm X') X (Fm:('a,'b)mmForm)) ==> 
       (x,Trans,extend_env X Q V) mmsat (Fm:('a,'b)mmForm)))``,
     ``\x.(((x,Trans,extend_env X Q V) mmsat (Fm:('a,'b)mmForm)) ==> 
        ((x,Trans,extend_env X' Q V) mmsat (Subst (propmm X') X (Fm:('a,'b)mmForm))))``]
    FORALL_AND_THM)))

val th2 =
TAC_PROOF
(([],
 ``(INFINITE (UNIV:'b set)) ==>
   (!(g:('a,'b)mmForm).(fmla_size g = fmla_size f) ==>
    (!V Q (X:'b) (X':'b).
     INFINITE univ(:'b) ==>
     X' NOTIN frees g ==>
     (setsat Trans (Subst (propmm X') X g) (extend_env X' Q V) =
      setsat Trans g (extend_env X Q V)))) ==>
   (!(g:('a,'b)mmForm).(fmla_size g = fmla_size f) ==>
    !V Q (X:'b) (X':'b).
     X' NOTIN frees g ==>
     (setsat Trans (Subst (propmm X') X g) (extend_env X' Q V) =
      setsat Trans g (extend_env X Q V)))``),
PROVE_TAC[]);

val alpha_LEM =
TAC_PROOF
(([],
 ``!(Trans:'a -> 'configuration -> 'configuration -> bool)
    (Fm:('a,'b)mmForm) V Q X X'. 
    INFINITE (UNIV:'b set) ==> ~(X' IN frees Fm) ==>
    (setsat Trans (Subst (propmm X') X Fm) (extend_env X' Q V) = setsat Trans Fm (extend_env X Q V))``),
(GEN_TAC THEN
(MATCH_MP_TAC
(BETA_RULE 
 (SPEC 
  ``\(Fm:('a,'b)mmForm).(!(V :'b -> 'configuration -> bool)
       (Q :'configuration -> bool) (X :'b) (X' :'b).
      INFINITE(UNIV:'b set) ==> X' NOTIN frees Fm ==>
      (setsat (Trans :'a -> 'configuration -> 'configuration -> bool)
         (Subst (propmm X' :('a, 'b) mmForm) X Fm) (extend_env X' Q V) =
       setsat Trans Fm (extend_env X Q V)))`` fmla_size_induction))) THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
[(* tt DISCH_TAC THEN IMP_RES_TAC for INFINITE *)DISCH_TAC THEN IMP_RES_TAC Subst THEN ASM_REWRITE_TAC [setsat_lemma]
,(* ff DISCH_TAC THEN IMP_RES_TAC for INFINITE *)DISCH_TAC THEN IMP_RES_TAC Subst THEN ASM_REWRITE_TAC [setsat_lemma]
,(* propmm s DISCH_TAC THEN IMP_RES_TAC for INFINITE *)DISCH_TAC THEN IMP_RES_TAC Subst THEN ASM_REWRITE_TAC [frees_def,IN_SING]
 THEN CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV SYM_CONV)) THEN COND_CASES_TAC
 THEN REWRITE_TAC [setsat_lemma, extend_env_def] THEN BETA_TAC THEN AR
 THEN DISCH_THEN (REWRITE_TAC o ulist)
,(* andmm *)STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN RES_TAC 
 THEN PAT_ASSUM
 ``INFINITE (UNIV:'b set)`` 
 (fn th => REWRITE_TAC[(MATCH_MP Subst th),setsat_lemma,frees_def,IN_UNION,DE_MORGAN_THM])
 THEN REPEAT STRIP_TAC THEN RES_TAC THEN AR
,(* ormm *)STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN RES_TAC 
 THEN PAT_ASSUM
 ``INFINITE (UNIV:'b set)`` 
 (fn th => REWRITE_TAC[(MATCH_MP Subst th),setsat_lemma,frees_def,IN_UNION,DE_MORGAN_THM])
 THEN REPEAT STRIP_TAC THEN RES_TAC THEN AR
,(* Box *)STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN RES_TAC  
 THEN PAT_ASSUM
 ``INFINITE (UNIV:'b set)`` 
 (fn th => REWRITE_TAC[(MATCH_MP Subst th),frees_def]) 
 THEN DISCH_TAC THEN RES_TAC THEN REWRITE_TAC[setsat_lemma]
 THEN PAT_ASSUM
      ``!X V Q.setsat Trans (Subst (propmm X') X f) (extend_env X' Q V) =
        setsat Trans f (extend_env X Q V)``
      (fn th => ASSUME_TAC
                (REWRITE_RULE
                 [setsat_def,EQ_SUBSET_SUBSET,SUBSET_DEF,
                 (SET_SPEC_CONV``x IN {E | (E,Trans,V) mmsat Fm}``),th1]th)) THEN AR
,(* Dia *)STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN RES_TAC  
 THEN PAT_ASSUM
 ``INFINITE (UNIV:'b set)`` 
 (fn th => REWRITE_TAC[(MATCH_MP Subst th),frees_def]) 
 THEN DISCH_TAC THEN RES_TAC THEN REWRITE_TAC[setsat_lemma]
 THEN PAT_ASSUM
      ``!X V Q.setsat Trans (Subst (propmm X') X f) (extend_env X' Q V) =
        setsat Trans f (extend_env X Q V)``
      (fn th => ASSUME_TAC
                (REWRITE_RULE
                 [setsat_def,EQ_SUBSET_SUBSET,SUBSET_DEF,
                 (SET_SPEC_CONV``x IN {E | (E,Trans,V) mmsat Fm}``),th1]th)) THEN AR
,(* nu *)DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC
 THEN Q_TAC ASM_CASES_TAC `X IN frees (nu s f)` THENL
 [DISCH_THEN (fn n => ASSUME_TAC n THEN MP_TAC n)
  THEN REWRITE_TAC [frees_def, IN_DELETE, IN_SING, (UNDISCH Subst)]
  THEN CONV_TAC (ONCE_DEPTH_CONV let_CONV)
  THEN (SUBGOAL_THEN (Term`FINITE ({(X':'b)} UNION frees f)`) ASSUME_TAC
        THEN1 REWRITE_TAC [FINITE_SING, FINITE_UNION, frees_finite])
  THEN (SUBGOAL_THEN (Term`?(Z':'b). Z' = variant ({(X':'b)} UNION frees (f:('a,'b)mmForm)) (s:'b)`)
        (fn eq => STRIP_ASSUME_TAC eq 
         THEN IMP_RES_THEN (MP_TAC o SPEC_ALL) (GEN_ALL(UNDISCH(ISPECL [``s:'b``,``excl:'b set``] variant_not_in)))
         THEN SUBST1_TAC (SYM (ASSUME
          (Term`Z' = variant ({(X':'b)} UNION frees (f:('a,'b)mmForm)) (s:'b)`)))
         THEN DISCH_THEN (STRIP_ASSUME_TAC o
          REWRITE_RULE [IN_SING, IN_UNION, DE_MORGAN_THM]))
   THEN1 (EXISTS_TAC``variant ({(X':'b)} UNION frees (f:('a,'b)mmForm)) s`` THEN REFL_TAC))
  THEN CONV_TAC (ONCE_DEPTH_CONV let_CONV)
  THEN (SUBGOAL_THEN (Term`(X:'b) IN frees (f:('a,'b)mmForm) /\ ~(X = (s:'b))`)
        (REWRITE_TAC o ulist)
        THEN1 (Q_TAC UNDISCH_TAC `(X:'b) IN frees (nu (s:'b) (f:('a,'b)mmForm))`
               THEN REWRITE_TAC [frees_def, IN_DELETE]))
  THEN REWRITE_TAC [DE_MORGAN_THM]
  THEN CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV SYM_CONV))
  THEN DISJ_CASES_THEN (fn x => ASSUME_TAC x THEN REWRITE_TAC [x])
                       (ISPEC (Term`s:'b = X'`) EXCLUDED_MIDDLE) THENL
  [REWRITE_TAC [setsat_lemma] THEN AP_TERM_TAC
   THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC
   THEN IMP_RES_THEN (REWRITE_TAC o ulist) uneq_extensions_commute
  THEN IMP_RES_TAC th2
  THEN SUBGOAL_THEN (Term
   `(fmla_size (Subst (propmm (Z':'b)) (X':'b) (f:('a,'b)mmForm)) = fmla_size f) /\
    ~(X' IN frees (Subst (propmm Z') X' f))`)
   (fn cj => ANTE_RES_THEN (fn imp =>
     REWRITE_TAC [MATCH_MP imp (CONJUNCT2 cj)]) (CONJUNCT1 cj)) THENL
   [REWRITE_TAC [UNDISCH(SPEC_ALL Subst_same_size)]
    THEN MATCH_MP_TAC (UNDISCH(SPEC_ALL alpha_remove)) THEN AR
   ,(SUBGOAL_THEN (Term`~(X:'b = Z')`) ASSUME_TAC
     THEN1 (MATCH_MP_TAC in_not_in_not_eq
            THEN Q_TAC EXISTS_TAC `frees (f:('a,'b)mmForm)`
            THEN Q_TAC UNDISCH_TAC `X IN frees (nu (s:'b) (f:('a,'b)mmForm))`
            THEN ASM_REWRITE_TAC [frees_def, IN_DELETE] THEN TAUT_TAC))
    THEN IMP_RES_THEN (REWRITE_TAC o ulist) uneq_extensions_commute
    THEN ANTE_RES_THEN (IMP_RES_THEN (REWRITE_TAC o ulist))
                       (REFL (Term`fmla_size (f:('a,'b)mmForm)`))
   ]
  ,DISCH_TAC THEN REWRITE_TAC [setsat_lemma] THEN AP_TERM_TAC
   THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC
   THEN IMP_RES_THEN (REWRITE_TAC o ulist) uneq_extensions_commute
(* take care of INFINITE in 0th assumption *)
   THEN IMP_RES_TAC th2
   THEN ANTE_RES_THEN (IMP_RES_THEN (REWRITE_TAC o ulist))
                      (REFL (Term`fmla_size (f:('a,'b)mmForm)`))
   THEN SUBGOAL_THEN (Term`~(X:'b = s)`)
    (fn e => REWRITE_TAC [MATCH_MP uneq_extensions_commute e])
   THEN MATCH_MP_TAC in_not_in_not_eq
   THEN Q_TAC EXISTS_TAC `frees (nu (s:'b) (f:('a,'b)mmForm))`
   THEN ASM_REWRITE_TAC [nuvar_not_free]
  ]
 ,IMP_RES_THEN (REWRITE_TAC o ulist) (UNDISCH(SPEC_ALL Subst_not_free))
  THEN DISCH_TAC THEN IMP_RES_THEN (REWRITE_TAC o ulist) silly_extend
]
,(* mu *)DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC
 THEN Q_TAC ASM_CASES_TAC `X IN frees (mu s f)` THENL
 [DISCH_THEN (fn n => ASSUME_TAC n THEN MP_TAC n)
  THEN REWRITE_TAC [frees_def, IN_DELETE, IN_SING, (UNDISCH Subst)]
  THEN CONV_TAC (ONCE_DEPTH_CONV let_CONV)
  THEN (SUBGOAL_THEN (Term`FINITE ({(X':'b)} UNION frees f)`) ASSUME_TAC
        THEN1 REWRITE_TAC [FINITE_SING, FINITE_UNION, frees_finite])
  THEN (SUBGOAL_THEN (Term`?(Z':'b). Z' = variant ({(X':'b)} UNION frees (f:('a,'b)mmForm)) (s:'b)`)
        (fn eq => STRIP_ASSUME_TAC eq 
         THEN IMP_RES_THEN (MP_TAC o SPEC_ALL) (GEN_ALL(UNDISCH(ISPECL [``s:'b``,``excl:'b set``] variant_not_in)))
         THEN SUBST1_TAC (SYM (ASSUME
          (Term`Z' = variant ({(X':'b)} UNION frees (f:('a,'b)mmForm)) (s:'b)`)))
         THEN DISCH_THEN (STRIP_ASSUME_TAC o
          REWRITE_RULE [IN_SING, IN_UNION, DE_MORGAN_THM]))
   THEN1 (EXISTS_TAC``variant ({(X':'b)} UNION frees (f:('a,'b)mmForm)) s`` THEN REFL_TAC))
  THEN CONV_TAC (ONCE_DEPTH_CONV let_CONV)
  THEN (SUBGOAL_THEN (Term`(X:'b) IN frees (f:('a,'b)mmForm) /\ ~(X = (s:'b))`)
        (REWRITE_TAC o ulist)
        THEN1 (Q_TAC UNDISCH_TAC `(X:'b) IN frees (mu (s:'b) (f:('a,'b)mmForm))`
               THEN REWRITE_TAC [frees_def, IN_DELETE]))
  THEN REWRITE_TAC [DE_MORGAN_THM]
  THEN CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV SYM_CONV))
  THEN DISJ_CASES_THEN (fn x => ASSUME_TAC x THEN REWRITE_TAC [x])
                       (ISPEC (Term`s:'b = X'`) EXCLUDED_MIDDLE) THENL
  [REWRITE_TAC [setsat_lemma] THEN AP_TERM_TAC
   THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC
   THEN IMP_RES_THEN (REWRITE_TAC o ulist) uneq_extensions_commute
  THEN IMP_RES_TAC th2
  THEN SUBGOAL_THEN (Term
   `(fmla_size (Subst (propmm (Z':'b)) (X':'b) (f:('a,'b)mmForm)) = fmla_size f) /\
    ~(X' IN frees (Subst (propmm Z') X' f))`)
   (fn cj => ANTE_RES_THEN (fn imp =>
     REWRITE_TAC [MATCH_MP imp (CONJUNCT2 cj)]) (CONJUNCT1 cj)) THENL
   [REWRITE_TAC [UNDISCH(SPEC_ALL Subst_same_size)]
    THEN MATCH_MP_TAC (UNDISCH(SPEC_ALL alpha_remove)) THEN AR
   ,(SUBGOAL_THEN (Term`~(X:'b = Z')`) ASSUME_TAC
     THEN1 (MATCH_MP_TAC in_not_in_not_eq
            THEN Q_TAC EXISTS_TAC `frees (f:('a,'b)mmForm)`
            THEN Q_TAC UNDISCH_TAC `X IN frees (mu (s:'b) (f:('a,'b)mmForm))`
            THEN ASM_REWRITE_TAC [frees_def, IN_DELETE] THEN TAUT_TAC))
    THEN IMP_RES_THEN (REWRITE_TAC o ulist) uneq_extensions_commute
    THEN ANTE_RES_THEN (IMP_RES_THEN (REWRITE_TAC o ulist))
                       (REFL (Term`fmla_size (f:('a,'b)mmForm)`))
   ]
  ,DISCH_TAC THEN REWRITE_TAC [setsat_lemma] THEN AP_TERM_TAC
   THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC
   THEN IMP_RES_THEN (REWRITE_TAC o ulist) uneq_extensions_commute
(* take care of INFINITE in 0th assumption *)
   THEN IMP_RES_TAC th2
   THEN ANTE_RES_THEN (IMP_RES_THEN (REWRITE_TAC o ulist))
                      (REFL (Term`fmla_size (f:('a,'b)mmForm)`))
   THEN SUBGOAL_THEN (Term`~(X:'b = s)`)
    (fn e => REWRITE_TAC [MATCH_MP uneq_extensions_commute e])
   THEN MATCH_MP_TAC in_not_in_not_eq
   THEN Q_TAC EXISTS_TAC `frees (mu (s:'b) (f:('a,'b)mmForm))`
   THEN ASM_REWRITE_TAC [muvar_not_free]
  ]
 ,IMP_RES_THEN (REWRITE_TAC o ulist) (UNDISCH(SPEC_ALL Subst_not_free))
  THEN DISCH_TAC THEN IMP_RES_THEN (REWRITE_TAC o ulist) silly_extend
]]));

val _ = save_thm("alpha_LEM",alpha_LEM);

(* A helper theorem use to prove Subst_LEM *)
val th1 =
GSYM(REWRITE_RULE[GSYM EQ_IMP_THM]
 (BETA_RULE
  (ISPECL
    [``\x.(((x,Trans,V) mmsat (Subst p Z (f:('a,'b)mmForm)) ==> 
       (x,Trans,extend_env Z {E | (E,Trans,V) mmsat p} V) mmsat (f:('a,'b)mmForm)))``,
     ``\x.(((x,Trans,extend_env Z {E | (E,Trans,V) mmsat p} V) mmsat (f:('a,'b)mmForm)) ==>
        ((x,Trans,V) mmsat (Subst p Z (f:('a,'b)mmForm))))``]
    FORALL_AND_THM)));

val th2 = 
TAC_PROOF
(([],
 ``(!(g :('a, 'b) mmForm).
            (fmla_size g = fmla_size (f :('a, 'b) mmForm)) ==>
            !(p :('a, 'b) mmForm) (Z :'b) (V :'b -> 'configuration -> bool).
              INFINITE univ((:'b) :'b itself) ==>
              (setsat
                 (Trans :'a -> 'configuration -> 'configuration -> bool)
                 (Subst p Z g) V =
               setsat Trans g (extend_env Z (setsat Trans p V) V))) ==>
   (INFINITE (UNIV:'b set)) ==>
   (!(g :('a, 'b) mmForm).
            (fmla_size g = fmla_size (f :('a, 'b) mmForm)) ==>
            !(p :('a, 'b) mmForm) (Z :'b) (V :'b -> 'configuration -> bool).
              (setsat
                 (Trans :'a -> 'configuration -> 'configuration -> bool)
                 (Subst p Z g) V =
               setsat Trans g (extend_env Z (setsat Trans p V) V)))``),
PROVE_TAC[]);

val Subst_LEM = 
TAC_PROOF
(([],``!(Trans:'a -> 'configuration -> 'configuration -> bool)
       (Fm:('a,'b)mmForm)(p:('a,'b)mmForm)(Z:'b). 
      !(V:'b -> 'configuration set). 
        INFINITE(UNIV:'b set) ==>
        ((setsat Trans (Subst p Z Fm) V) = (setsat Trans Fm (extend_env Z (setsat Trans p V) V)))``),
(GEN_TAC THEN 
(MATCH_MP_TAC
(BETA_RULE 
 (SPEC 
  ``\(Fm:('a,'b)mmForm).!(p:('a,'b)mmForm)(Z:'b)(V:'b -> 'configuration set). 
    INFINITE(UNIV:'b set) ==>
    ((setsat Trans (Subst p Z Fm) V) = 
     (setsat Trans Fm (extend_env Z (setsat Trans p V) V)))`` 
  fmla_size_induction))) THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
[(* tt DISCH_TAC for INFINITE *)DISCH_TAC THEN REWRITE_TAC [(UNDISCH Subst), setsat_lemma]
,(* ff DISCH_TAC for INFINITE *)DISCH_TAC THEN REWRITE_TAC [(UNDISCH Subst), setsat_lemma]
,(* propmm DISCH_TAC for INFINITE *)DISCH_TAC THEN REWRITE_TAC [(UNDISCH Subst), setsat_lemma, extend_env_def] THEN BETA_TAC
 THEN CONV_TAC (LAND_CONV (REWRITE_CONV [COND_RAND, COND_RATOR]))
 THEN REWRITE_TAC [setsat_lemma]
,(* andmm REPEAT GEN_TAC THEN REPEAT STRIP_TAC for INFINITE *)REPEAT GEN_TAC THEN REPEAT STRIP_TAC 
 THEN RES_TAC THEN ASM_REWRITE_TAC [(UNDISCH Subst), setsat_lemma]
,(* ormm REPEAT GEN_TAC THEN REPEAT STRIP_TAC for INFINITE *)REPEAT GEN_TAC THEN REPEAT STRIP_TAC 
 THEN RES_TAC THEN ASM_REWRITE_TAC [(UNDISCH Subst), setsat_lemma]
,(* Box *)REPEAT STRIP_TAC THEN RES_TAC
 THEN REWRITE_TAC[UNDISCH Subst] THEN REWRITE_TAC[setsat_lemma]
 THEN PAT_ASSUM
      ``!p Z V.setsat Trans (Subst p z f) V = setsat Trans f (extend_env Z (setsat Trans p V) V)``
      (fn th => ASSUME_TAC(REWRITE_RULE[setsat_def] th))
 THEN REWRITE_TAC[setsat_def]
 THEN PAT_ASSUM
      ``!p Z V.P = Q``
      (fn th => 
       ASSUME_TAC
       (REWRITE_RULE
        [EQ_SUBSET_SUBSET,SUBSET_DEF,
         (SET_SPEC_CONV``x IN {E | (E,Trans,V) mmsat Fm}``),th1] th))
 THEN AR
,(* Dia *)REPEAT STRIP_TAC THEN RES_TAC
 THEN REWRITE_TAC[UNDISCH Subst] THEN REWRITE_TAC[setsat_lemma]
 THEN PAT_ASSUM
      ``!p Z V.setsat Trans (Subst p z f) V = setsat Trans f (extend_env Z (setsat Trans p V) V)``
      (fn th => ASSUME_TAC(REWRITE_RULE[setsat_def] th))
 THEN REWRITE_TAC[setsat_def]
 THEN PAT_ASSUM
      ``!p Z V.P = Q``
      (fn th => 
       ASSUME_TAC
       (REWRITE_RULE
        [EQ_SUBSET_SUBSET,SUBSET_DEF,
         (SET_SPEC_CONV``x IN {E | (E,Trans,V) mmsat Fm}``),th1] th))
 THEN AR
,(* nu REPEAT STRIP_TAC for INFINITE *)REPEAT STRIP_TAC THEN Q_TAC ASM_CASES_TAC `(Z:'b) IN frees (nu (s:'b)(f:('a,'b)mmForm))`
 (* remove INFINITE from 0th assumption *) THEN IMP_RES_TAC th2 THENL
 [ASM_REWRITE_TAC [UNDISCH Subst]
  THEN CONV_TAC (ONCE_DEPTH_CONV let_CONV)
  THEN COND_CASES_TAC THENL
  [(SUBGOAL_THEN (Term`FINITE (frees (p:('a,'b)mmForm) UNION frees (f:('a,'b)mmForm))`) ASSUME_TAC
    THEN1 (REWRITE_TAC [FINITE_UNION, frees_finite]))
   THEN (SUBGOAL_THEN (Term`?(Z':'b). Z' = variant (frees (p:('a,'b)mmForm) UNION frees (f:('a,'b)mmForm)) (s:'b)`)
   (fn eq => STRIP_ASSUME_TAC eq 
    THEN IMP_RES_THEN (MP_TAC o SPEC_ALL) (UNDISCH (ISPECL [``s:'b``,``excl:'b set``] variant_not_in))
    THEN SUBST1_TAC (SYM (ASSUME
     (Term`(Z':'b) = variant (frees (p:('a,'b)mmForm) UNION frees (f:('a,'b)mmForm)) (s:'b)`)))
    THEN DISCH_THEN (STRIP_ASSUME_TAC o
           REWRITE_RULE [IN_UNION, DE_MORGAN_THM]))
    THEN1 (Q_TAC EXISTS_TAC `variant (frees (p:('a,'b)mmForm) UNION frees (f:('a,'b)mmForm)) (s:'b)`
           THEN REFL_TAC))
   THEN CONV_TAC (ONCE_DEPTH_CONV let_CONV)
   THEN REWRITE_TAC [setsat_lemma] THEN AP_TERM_TAC
   THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC
   THEN (SUBGOAL_THEN (Term
   `fmla_size (Subst (propmm (Z':'b)) (s:'b) (f:('a,'b)mmForm)) = fmla_size (f:('a,'b)mmForm)`)   
    (ANTE_RES_THEN (REWRITE_TAC o ulist))
    THEN1 MATCH_ACCEPT_TAC (UNDISCH(SPEC_ALL Subst_same_size)))
   THEN IMP_RES_THEN (REWRITE_TAC o ulist) silly_extend
   THEN (SUBGOAL_THEN (Term`~(Z:'b = Z')`)
         (REWRITE_TAC o ulist o MATCH_MP uneq_extensions_commute)
         THEN1 (MATCH_MP_TAC in_not_in_not_eq
                THEN Q_TAC EXISTS_TAC `frees (f:('a,'b)mmForm)`
                THEN Q_TAC UNDISCH_TAC `(Z:'b) IN frees (nu (s:'b) (f:('a,'b)mmForm))`
                THEN ASM_REWRITE_TAC [frees_def, IN_DELETE] THEN TAUT_TAC))
   THEN IMP_RES_THEN (REWRITE_TAC o ulist) (UNDISCH(SPEC_ALL alpha_LEM))
  ,REWRITE_TAC [setsat_lemma] THEN AP_TERM_TAC
   THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC
   THEN (SUBGOAL_THEN (Term`~(s:'b = Z)`)
         (REWRITE_TAC o ulist o MATCH_MP uneq_extensions_commute)
         THEN1 (MATCH_MP_TAC (GSYM in_not_in_not_eq)
                THEN Q_TAC EXISTS_TAC `frees (nu (s:'b) (f:('a,'b)mmForm))`
                THEN ASM_REWRITE_TAC [nuvar_not_free]))
   THEN ANTE_RES_THEN (REWRITE_TAC o ulist) (REFL (Term`fmla_size (f:('a,'b)mmForm)`))
   THEN IMP_RES_THEN (REWRITE_TAC o ulist) silly_extend
  ]
 ,IMP_RES_THEN (REWRITE_TAC o ulist) (UNDISCH(SPEC_ALL Subst_not_free))
  THEN IMP_RES_THEN (REWRITE_TAC o ulist) silly_extend
]
,(* mu REPEAT STRIP_TAC for INFINITE *)REPEAT STRIP_TAC THEN Q_TAC ASM_CASES_TAC `(Z:'b) IN frees (mu (s:'b)(f:('a,'b)mmForm))`
 (* remove INFINITE from 0th assumption *) THEN IMP_RES_TAC th2 THENL
 [ASM_REWRITE_TAC [UNDISCH Subst]
  THEN CONV_TAC (ONCE_DEPTH_CONV let_CONV)
  THEN COND_CASES_TAC THENL
  [(SUBGOAL_THEN (Term`FINITE (frees (p:('a,'b)mmForm) UNION frees (f:('a,'b)mmForm))`) ASSUME_TAC
    THEN1 (REWRITE_TAC [FINITE_UNION, frees_finite]))
   THEN (SUBGOAL_THEN (Term`?(Z':'b). Z' = variant (frees (p:('a,'b)mmForm) UNION frees (f:('a,'b)mmForm)) (s:'b)`)
   (fn eq => STRIP_ASSUME_TAC eq 
    THEN IMP_RES_THEN (MP_TAC o SPEC_ALL) (UNDISCH (ISPECL [``s:'b``,``excl:'b set``] variant_not_in))
    THEN SUBST1_TAC (SYM (ASSUME
     (Term`(Z':'b) = variant (frees (p:('a,'b)mmForm) UNION frees (f:('a,'b)mmForm)) (s:'b)`)))
    THEN DISCH_THEN (STRIP_ASSUME_TAC o
           REWRITE_RULE [IN_UNION, DE_MORGAN_THM]))
    THEN1 (Q_TAC EXISTS_TAC `variant (frees (p:('a,'b)mmForm) UNION frees (f:('a,'b)mmForm)) (s:'b)`
           THEN REFL_TAC))
   THEN CONV_TAC (ONCE_DEPTH_CONV let_CONV)
   THEN REWRITE_TAC [setsat_lemma] THEN AP_TERM_TAC
   THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC
   THEN (SUBGOAL_THEN (Term
   `fmla_size (Subst (propmm (Z':'b)) (s:'b) (f:('a,'b)mmForm)) = fmla_size (f:('a,'b)mmForm)`)   
    (ANTE_RES_THEN (REWRITE_TAC o ulist))
    THEN1 MATCH_ACCEPT_TAC (UNDISCH(SPEC_ALL Subst_same_size)))
   THEN IMP_RES_THEN (REWRITE_TAC o ulist) silly_extend
   THEN (SUBGOAL_THEN (Term`~(Z:'b = Z')`)
         (REWRITE_TAC o ulist o MATCH_MP uneq_extensions_commute)
         THEN1 (MATCH_MP_TAC in_not_in_not_eq
                THEN Q_TAC EXISTS_TAC `frees (f:('a,'b)mmForm)`
                THEN Q_TAC UNDISCH_TAC `(Z:'b) IN frees (mu (s:'b) (f:('a,'b)mmForm))`
                THEN ASM_REWRITE_TAC [frees_def, IN_DELETE] THEN TAUT_TAC))
   THEN IMP_RES_THEN (REWRITE_TAC o ulist) (UNDISCH(SPEC_ALL alpha_LEM))
  ,REWRITE_TAC [setsat_lemma] THEN AP_TERM_TAC
   THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC
   THEN (SUBGOAL_THEN (Term`~(s:'b = Z)`)
         (REWRITE_TAC o ulist o MATCH_MP uneq_extensions_commute)
         THEN1 (MATCH_MP_TAC (GSYM in_not_in_not_eq)
                THEN Q_TAC EXISTS_TAC `frees (mu (s:'b) (f:('a,'b)mmForm))`
                THEN ASM_REWRITE_TAC [muvar_not_free]))
   THEN ANTE_RES_THEN (REWRITE_TAC o ulist) (REFL (Term`fmla_size (f:('a,'b)mmForm)`))
   THEN IMP_RES_THEN (REWRITE_TAC o ulist) silly_extend
  ]
 ,IMP_RES_THEN (REWRITE_TAC o ulist) (UNDISCH(SPEC_ALL Subst_not_free))
  THEN IMP_RES_THEN (REWRITE_TAC o ulist) silly_extend
]]));

val _ = save_thm("Subst_LEM",Subst_LEM);

val lfp_monotone = store_thm ("lfp_monotone", Term
`!G H. (!s:'a set. G s SUBSET H s) ==>
       lfp G SUBSET lfp H`,
REPEAT STRIP_TAC
THEN (SUBGOAL_THEN (Term`!t:'a set. H t SUBSET t ==> G t SUBSET t`)
      ASSUME_TAC
     THEN1 (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS
            THEN Q_TAC EXISTS_TAC `H t` THEN AR))
THEN REWRITE_TAC [lfp_def]
THEN REWRITE_TAC [SUBSET_BIGINTER]
THEN GEN_TAC THEN CONV_TAC (RAND_CONV (REWR_CONV SUBSET_DEF))
THEN REWRITE_TAC [IN_BIGINTER]
THEN CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV)
THEN REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC);

val gfp_monotone =
TAC_PROOF
(([],
 ``!G H. (!s:'a set. G s SUBSET H s) ==> gfp G SUBSET gfp H``),
(REPEAT STRIP_TAC
THEN (SUBGOAL_THEN (Term`!t:'a set. t SUBSET G t ==> t SUBSET H t`)
      ASSUME_TAC
     THEN1 (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS
            THEN Q_TAC EXISTS_TAC `G t` THEN AR))
THEN REWRITE_TAC [gfp_def]
THEN REWRITE_TAC [BIGUNION_SUBSET]
THEN GEN_TAC THEN CONV_TAC (RAND_CONV (REWR_CONV SUBSET_DEF))
THEN REWRITE_TAC [IN_BIGUNION]
THEN CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV)
THEN REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC
THEN EXISTS_TAC ``Y:'a set``
THEN AR));

val _ = save_thm("gfp_monotone",gfp_monotone);

val setsat_EQ_satFun =
TAC_PROOF
(([],
 ``! Trans Fm Z E V.setsat (Trans:'a -> 'configuration -> 'configuration -> bool)
          (Fm:('a,'b)mmForm) (extend_env Z E V) =
   satFun Trans Z V Fm E``),
REWRITE_TAC [IN_UNIV,mmfn_def,satFun_def,setsat_def,extend_env_mmUpdate_EQ]);

val _ = save_thm("setsat_EQ_satFun",setsat_EQ_satFun);

val setsat_monotone = 
TAC_PROOF
(([],
``!(Trans:'a -> 'configuration -> 'configuration -> bool)
   (Fm:('a,'b)mmForm)(Z:'b)(V:'b -> 'configuration set). monotone (\Q. setsat Trans Fm (extend_env Z Q V))``),
REWRITE_TAC[monotone_def] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[setsat_EQ_satFun,satFun_MONOTONIC]);

val _ = save_thm("setsat_monotone",setsat_monotone);

(* Now to put together all of the above to show that (mu Z ...) formulas
  may be unrolled without effect on the meaning: *)

val mu_lemma =
TAC_PROOF
(([],
 ``!(Trans:'a -> 'configuration -> 'configuration -> bool)
    (Z:'b)(Fm:('a,'b)mmForm)(V:'b -> 'configuration set).
    setsat Trans (mu Z Fm) V = lfp (\Q. setsat Trans Fm (extend_env Z Q V))``),
REWRITE_TAC[setsat_lemma]);

val nu_lemma =
TAC_PROOF
(([],
 ``!(Trans:'a -> 'configuration -> 'configuration -> bool)
    (Z:'b)(Fm:('a,'b)mmForm)(V:'b -> 'configuration set).
    setsat Trans (nu Z Fm) V = gfp (\Q. setsat Trans Fm (extend_env Z Q V))``),
REWRITE_TAC[setsat_lemma]);

val ok_to_unroll_mu = 
TAC_PROOF
(([],
``!(Trans:'a -> 'configuration -> 'configuration -> bool)
   (Fm:('a,'b)mmForm)(Z:'b)(V:'b ->'configuration set).
    INFINITE(UNIV:'b set) ==> (setsat Trans (Subst (mu Z Fm) Z Fm) V = setsat Trans (mu Z Fm) V)``),
(REPEAT STRIP_TAC THEN REWRITE_TAC [setsat_lemma]
THEN ASSUME_TAC (SPEC_ALL setsat_monotone)
THEN IMP_RES_TAC lfp_fixedpoint THEN ONCE_ASM_REWRITE_TAC []
THEN BETA_TAC
THEN REWRITE_TAC [GSYM mu_lemma]
THEN MATCH_ACCEPT_TAC (UNDISCH(SPEC_ALL Subst_LEM))));

val _ = save_thm("ok_to_unroll_mu",ok_to_unroll_mu);

val ok_to_unroll_nu = 
TAC_PROOF
(([],
``!(Trans:'a -> 'configuration -> 'configuration -> bool)
   (Fm:('a,'b)mmForm)(Z:'b)(V:'b ->'configuration set).
    INFINITE(UNIV:'b set) ==> (setsat Trans (Subst (nu Z Fm) Z Fm) V = setsat Trans (nu Z Fm) V)``),
(REPEAT STRIP_TAC THEN REWRITE_TAC [setsat_lemma]
THEN ASSUME_TAC (SPEC_ALL setsat_monotone)
THEN IMP_RES_TAC gfp_greatest_fixedpoint THEN ONCE_ASM_REWRITE_TAC []
THEN BETA_TAC
THEN REWRITE_TAC [GSYM nu_lemma]
THEN MATCH_ACCEPT_TAC (UNDISCH(SPEC_ALL Subst_LEM))));

val _ = save_thm("ok_to_unroll_nu",ok_to_unroll_nu);

val mmsat_setsat =
TAC_PROOF
(([],``((E,Trans,V) mmsat f) = (E IN (setsat Trans f V))``),
REWRITE_TAC[setsat_def,(SET_SPEC_CONV``E IN {E | (E,Trans,V) mmsat f}``)]);

val _ = save_thm("mmsat_setsat",mmsat_setsat);

val unfold_nu_LEM =
TAC_PROOF
(([],
``!(Trans:'a -> 'configuration -> 'configuration -> bool)
   (E:'configuration) (V:'b -> 'configuration set)
   (Z:'b)(f:('a,'b)mmForm). INFINITE(UNIV:'b set) ==> 
   (((E,Trans,V) mmsat (nu Z f)) = ((E,Trans,V) mmsat (Subst (nu Z f) Z f)))``),
REPEAT STRIP_TAC THEN REWRITE_TAC[mmsat_setsat,(UNDISCH(SPEC_ALL ok_to_unroll_nu))]);

val _ = save_thm("unfold_nu_LEM",unfold_nu_LEM);

val unfold_mu_LEM =
TAC_PROOF
(([],
``!(Trans:'a -> 'configuration -> 'configuration -> bool)
   (E:'configuration) (V:'b -> 'configuration set)
   (Z:'b)(f:('a,'b)mmForm). INFINITE(UNIV:'b set) ==> 
   (((E,Trans,V) mmsat (mu Z f)) = ((E,Trans,V) mmsat (Subst (mu Z f) Z f)))``),
REPEAT STRIP_TAC THEN REWRITE_TAC[mmsat_setsat,(UNDISCH(SPEC_ALL ok_to_unroll_mu))]);

val _ = save_thm("unfold_mu_LEM",unfold_mu_LEM);

(************************************************)
(* Dealing with infinite sets of variable names *)
(************************************************)

(* (1) Use INFINITE (UNIV:'a) to select types with an infinite number *)
(*     of elements.                                                   *)
(* (2) We do this using the definition of INFINITE                    *)

(* ==== start here ====
val _ = 
Hol_datatype
`ticks = none of 'a | tick of ticks`;

val ticks_11 = TypeBase.one_one_of ``:'a ticks``;
val ticks_DISTINCT = TypeBase.distinct_of ``:'a ticks``;

val list_11 = TypeBase.one_one_of ``:'a list``;
val list_DISTINCT = TypeBase.distinct_of ``:'a list``;

val INFINITE_UNIV_LIST =
TAC_PROOF
(([],``INFINITE(UNIV:('b list)set)``),
(REWRITE_TAC[INFINITE_UNIV] THEN
 EXISTS_TAC ``\xs:'b list.CONS (x:'b) xs`` THEN BETA_TAC THEN CONJ_TAC THENL
 [REWRITE_TAC[list_11],
  EXISTS_TAC ``[]:'b list`` THEN GEN_TAC THEN REWRITE_TAC[GSYM list_DISTINCT]]));
 
val infExists =
set_goal
([],
``?(f :'b -> 'b).
   (!(x :'b) (y :'b). (f x = f y) ==> (x = y)) /\
   ?(y :'b). !(x :'b). f x <> y``),
EXISTS_TAC ``tick:('a ticks) -> ('a ticks)``
MATCH_ACCEPT_TAC(REWRITE_RULE[INFINITE_UNIV]INFINITE_UNIV_LIST)

(* Example using strings *)
val STRING_11 = TypeBase.one_one_of (Type `:string`);

val STRING_DISTINCT = TypeBase.distinct_of (Type `:string`);

val strings_infinite = store_thm ("strings_infinite", Term
`INFINITE (UNIV:string set)`,
REWRITE_TAC [INFINITE_UNIV]
THEN Q_TAC EXISTS_TAC `\s. STRING ARB s` THEN BETA_TAC THEN CONJ_TAC THENL
[REWRITE_TAC [STRING_11]
,Q_TAC EXISTS_TAC `""` THEN GEN_TAC THEN REWRITE_TAC [GSYM STRING_DISTINCT]]);

(* as strings are infinitely long, the INFINITE condition is satisfied *)
REWRITE_RULE[strings_infinite](INST_TYPE [``:'b`` |-> ``:string``] unfold_nu_LEM)
REWRITE_RULE[strings_infinite](INST_TYPE [``:'b`` |-> ``:string``] unfold_mu_LEM)

val list_11 = TypeBase.one_one_of ``:'a list``;
val list_DISTINCT = TypeBase.distinct_of ``:'a list``;
set_goal([],``INFINITE(UNIV:('a list) list)``),


 ==== end here ==== *)


val _ = print_theory "-";
val _ = export_theory();

end;
