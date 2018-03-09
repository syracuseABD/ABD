(* File: ante_allTacs.sml, utility tactics, rules, conversionals. *)
(* Author: F. Lockwood Morris  <lockwood@ecs.syr.edu> *)
(* 5/4/03: merge in all of ante_appTacs, and und_asm *)
(* 8/13/02: adapt to HOL-4 *)
(* 7/27/02: made a structure, with a signature *)
(* 4/12/01: XL_FUN_EQ_CONV *) (* 3/23/01: added lines, asm, with_asm *)
(* 1/29/01: rearrangement in 2 (more and less elementary) parts *)
(* 1/26/01: reconciling with ante_allDesc.tex, for semi-public release *)
(* 11/16.00: added symOfEqn, STRIP_EXISTS_UNIQUE_TAC *)
(* 6/6/00; CONJ_DISCH_TAC will now fail for non-implications. *)
(* 3/15/00: Starting 6-comp. cat. rework. Intro. shorter name GCONJ_LIST*)
(* 3/11/00: added IMP_RES_THENL, IMP_RES_ASM_THENL, GCONJ_TRIP *)
(* 3/1/00: added short-name tactics AR, CRE, CR, CREL, CRL *)
(* 2/16/00: added ASM_MATCH_THEN (superceded 2/17 by PAT_ASSUM), TR_TAC *)
(* 1/22/00: LEMMA_TAC, LEMMA_MP_TAC now based on SUBGOAL_THEN *)
(* 1/8/00: DUP_ARGS_TAC added *) (* 1/5/00: EXISTS_UNIQUE_TAC added *)

structure ante_allTacs :> ante_allTacs =
struct

open HolKernel boolLib;
(* app load ["res_quanLib","Cond_rewrite","pairLib","pred_setTheory"];*)
open res_quanLib res_quanTheory Cond_rewrite pairTheory pairLib
     pred_setTheory Parse;
infix 2 THENSGS THENFIN;

(* ****** FIRST PART: very elementary rules, tactics, conversions ****** *)

(* Embryonic model for isThing_TACs: CUMUL_CONJ_TAC, capturing the idea:
   "To prove C1 /\ C2, it is enough to prove C1 and to prove C1 ==> C2." *)

val cumul_thm = prove (Term`A /\ (A ==> B) ==> A /\ B`,
REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC []);

val CUMUL_CONJ_TAC = MATCH_MP_TAC cumul_thm THEN CONJ_TAC;

(* Tactic: T_TAC, solves only ?-T, use after, e.g., COND_RW_TAC. It is
  hoped to be, if not quite documentation, at least more informative to
  use any of T_TAC, REFL_TAC, and TR_TAC when it is enough to finish
  solving a goal, even though REWRITE_TAC [] will outdo them all; also
  they should be cheaper than REWRITE_TAC [] to use with TRY in building
  other tactics, such as CRE, CR, CREL, CRL below. *)

val T_TAC = ACCEPT_TAC TRUTH;

(* TR_TAC, combines T_TAC, REFL_TAC, and REPEAT CONJ_TAC to sweep up
  after COND_REWRITE1_TAC and COND_RW_TAC have done all the work. *)

val TR_TAC = REPEAT CONJ_TAC THEN (T_TAC ORELSE REFL_TAC);

(* Tactics to drop an antecedent or an asm after it has served its turn.*)

val ANTE_DROP_TAC = DISCH_THEN (fn _ => ALL_TAC);

fun UNASSUME_TAC th = UNDISCH_TAC (concl th) THEN ANTE_DROP_TAC;

fun ulist x = [x]; (* most useful for thm-tactic REWRITE_TAC o ulist *)

(* (thm-tactics -> tactic)s built on ANTE_CONJ_CONV and extracting one half
   the antecedent; used the by tactics below, which may serve as
   documentation, but also, like DISCH_THEN, useful raw. *)

fun HALF_DISCH_THEN ttac = CONV_TAC ANTE_CONJ_CONV THEN DISCH_THEN ttac;

fun SWAP_HALF_DISCH_THEN ttac = DISCH_THEN
    (MP_TAC o CONV_RULE (REWR_CONV CONJ_SYM)) THEN HALF_DISCH_THEN ttac;

(* A tactic to make the characteristic use of ANTE_CONJ_CONV, and another
   just like it, but swaps the two antecedents first, that is:

A ?- u /\ v ==> w                   A ?- u /\ v ==> w
================== HALF_DISCH_TAC   ================== SWAP_HALF_DISCH_TAC
A u {u} ?- v ==> w                  A u {v} ?- u ==> w                  *)

val HALF_DISCH_TAC = HALF_DISCH_THEN ASSUME_TAC;

val SWAP_HALF_DISCH_TAC = SWAP_HALF_DISCH_THEN ASSUME_TAC;

(* Some conversional analogues of Lisp's CAAR, CDAR, CADR, CDDR. *)

val LLAND_CONV = LAND_CONV o LAND_CONV;
val LRAND_CONV = LAND_CONV o RAND_CONV;
val RLAND_CONV = RAND_CONV o LAND_CONV;
val RRAND_CONV = RAND_CONV o RAND_CONV;

(* Tactic to make up for bad planning: reverses an equational assumption *)

fun ASM_SYM_TAC t = UNDISCH_TAC t
                    THEN DISCH_THEN (ASSUME_TAC o GSYM);

(* A pure abbreviation of the rewrite I do most often. *)

val AR = ASM_REWRITE_TAC [];

(* A pair of tactics, LEMMA_TAC, LEMMA_MP_TAC: term -> tactic, for
   explicitly introducing a lemma as a separate subgoal to be proved;
   the original goal can then be tackled with the lemma as an added
   assumption (LEMMA_TAC) or hypothesis (LEMMA_MP_TAC).  These are all
   easy instances of SUBGOAL_THEN, but it took me a long time to
   understand its documentation, at least the first sentence of which
   applies as well to these tactics: "The user proposes a lemma and is
   then invited to prove it under the current assumptions." 

         A ?- G                              A ?- G
  ===================== LEMMA_TAC L   ==================== LEMMA_MP_TAC L
  A ?- L   A u {L} ?- G               A ?- L  A ?- L ==> G             *)

fun LEMMA_MP_TAC L = SUBGOAL_THEN L MP_TAC;
fun LEMMA_TAC L = SUBGOAL_THEN L STRIP_ASSUME_TAC;

(* An abbreviatory rule for drawing an inference from 2 thms by a third. *)

fun MATCH_MP2 T_IMP_IMP T1 T2 = MATCH_MP (MATCH_MP T_IMP_IMP T1) T2;

(* Sometimes one breaks up an equivalence goal with EQ_TAC merely in
 order to infer some easy conclusion from each side and add it to the
 assumptions; one would then wish that the two implicational subgoals
 could be recombined. The following tactic simulates that effect:
   
                         A ?- B = C
        ================================================= EQ_HYP_TAC H
        A ?- (B ==> H) /\ (C ==> H)      A u {H} ?- B = C               *)

val EQ_HYP_TAC_LEM = prove (Term
`!H B C. ((B ==> H) /\ (C ==> H)) /\ (H ==> (B = C)) ==> (B = C)`,
REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC
THEN RES_TAC THEN RES_TAC);

fun EQ_HYP_TAC h = MATCH_MP_TAC (SPEC h EQ_HYP_TAC_LEM)
 THEN (CONJ_TAC THENL [ALL_TAC, STRIP_TAC]);

(* Gordon's line-assumption selection technique, Intro. to HOL p. 55 *)

fun lines tok = let val wt = words2 " " tok in (fn t =>
 let val x = #Name (Rsyntax.dest_var
                    (rator (lhs (#Body (Rsyntax.dest_forall t)))))
 in mem x wt end handle _ => false) end;

(* Similar idea to pick up one assumption, of arbitrary structure, by
 a string containing enough of its variable occurrences, free and bound
 indifferently, in order from the left to identify it uniquely.
 5/4/03: jiggered to observe left-to-right rule even for terms with :: . *)

fun asm vars t =
 let exception MAT and NOMAT;
  fun mat [] t = raise MAT
    | mat (vvl as (v :: vl)) t =
       if is_var t then if #Name (Rsyntax.dest_var t) = v then vl
                                                          else raise NOMAT
       else if is_const t then vvl
       else if is_comb t then
         if is_abs (rand t) andalso
             (is_res_abstract t orelse is_res_forall t
              orelse is_res_exists t orelse is_res_select t
              orelse is_res_exists_unique t)
           then let val (var, P, t') = 
                       if is_res_abstract t then dest_res_abstract t
                       else if is_res_forall t then dest_res_forall t
                       else if is_res_exists t then dest_res_exists t
                       else if is_res_select t then dest_res_select t
                       else dest_res_exists_unique t
                in mat (mat (mat vvl var) P) t' end
         else mat (mat vvl (rator t)) (rand t)
       else mat (mat vvl (#Bvar (Rsyntax.dest_abs t)))
                (#Body (Rsyntax.dest_abs t));
 in mat (words2 " " vars) t = [] handle MAT => true | NOMAT => false end;

(* Function with_asm: string -> thm-tactic -> tactic applies its thm-tactic
  argument to the first assumption accepted by (asm string). *)

fun with_asm s ttac = ASSUM_LIST (ttac o first (asm s o concl));

fun und_asm s = with_asm s (UNDISCH_TAC o concl);

fun drop_asm s = with_asm s UNASSUME_TAC;

(* tty = Toggle show_TYpes [+ meaningless nostalgia for the teletype] *)

fun tty () = (show_types := not (!show_types); !show_types);

(* utility functions  for terms - recognize given unary/binary operator *)

fun is_unap string t =  is_comb t andalso
                        is_const (rator t) andalso
                        #Name (Rsyntax.dest_const (rator t)) = string;

fun is_binap string t = is_comb t andalso is_unap string (rator t);

(* REV_EXISTS_CONV generalizes SWAP_EXISTS_CONV, reverses the order of any
 number of existential quantifiers, and REV_FORALL_CONV does the same for
 universals. Both do nothing if there is one quantifier, fail if none. *)

fun REV_EXISTS_CONV t =
 let fun bury_outer t = (if is_exists (#Body (Rsyntax.dest_exists t))
                         then SWAP_EXISTS_CONV
                              THENC RAND_CONV (ABS_CONV bury_outer)
                         else ALL_CONV) t
 in (if is_exists (#Body (Rsyntax.dest_exists t))
    then RAND_CONV (ABS_CONV REV_EXISTS_CONV)
         THENC bury_outer
    else ALL_CONV) t end;

val REV_FORALL_CONV =
 let fun not_forall_iter t = (* t is a negation *)
    (if is_forall (rand t) then NOT_FORALL_CONV
                                THENC RAND_CONV (ABS_CONV not_forall_iter)
                           else ALL_CONV) t
     and exists_not_iter t = (if is_exists t
                              then RAND_CONV (ABS_CONV exists_not_iter)
                                   THENC EXISTS_NOT_CONV
                              else ALL_CONV) t
 in REWR_CONV (GSYM (CONJUNCT1 NOT_CLAUSES))
    THENC RAND_CONV (not_forall_iter THENC REV_EXISTS_CONV
                     THENC exists_not_iter)
    THENC REWR_CONV (CONJUNCT1 NOT_CLAUSES) end;

(* ***** SECOND PART: less elementary rules, tactics, conversions ****** *)

(* A tactical for replicating a tactic, for use with THENL, and a variant
   which gives one of a pair of arguments to each side. *)

fun DUP_TAC tac = [tac, tac];

fun DUP_ARGS_TAC (p,q) a_tac = [a_tac p, a_tac q];

(* A slight generalization of Dan Zhou's rule, `IMP_CONJ_LIST', intended
   like it to assist in putting theorems into a form acceptable to 
   COND_REWRITE1_TAC and _CONV. The following rule takes as 1st argument
   a rule for producing a list of theorems from a theorem, and produces
   a rule that applies the argument rule at the bottom of any nest of
   universal quantifiers and implications, restoring the quantifiers and
   hypotheses to each element of the resulting list of theorems. *)

fun FORALL_IMP_LIST_RULE lisrul th =
  if is_forall (concl th) 
   then let val (v, th') = SPEC_VAR th
        in map (GEN v) (FORALL_IMP_LIST_RULE lisrul th') end
  else if is_imp (concl th)
   then let val {ant=a, conseq=c} = Rsyntax.dest_imp (concl th)
        in map (DISCH a) (FORALL_IMP_LIST_RULE lisrul (UNDISCH th)) end
   else lisrul th;

(* The next rule reproduces what Dan Zhou's IMP_CONJ_LIST does, but it
   removes and replaces universal quantifiers as well.

   GCONJ_LIST: int -> thm -> thm list
	
	A |- a ==> b ==> !x ... ==> (e1 /\ e2 /\ ... /\ en)
  ------------------------------------------------------ GCONJ_LIST n
	    [A |- a ==> b ==> !x ... ==> e1, 
	     A |- a ==> b ==> !x ... ==> e2, ... ,
	     A |- a ==> b ==> !x ... ==> en]

FAILURE: Fails if the integer argument (n) is less than one, or if the
	 final conclusion of input theorem has less than n conjuncts.   *)

fun GCONJ_LIST n = FORALL_IMP_LIST_RULE (CONJ_LIST n);

(* Rules to turn a Boolean eqn. into lhs ==> rhs, resp. rhs ==> lhs *)

val impOfEqn = hd o FORALL_IMP_LIST_RULE (ulist o fst o EQ_IMP_RULE);

val impByOfEqn = hd o FORALL_IMP_LIST_RULE (ulist o snd o EQ_IMP_RULE);

(* The built-in GSYM occasionally does too much, reversing equations in
 the hypotheses which should be left alone; hence the following: *)

val symOfEqn = hd o FORALL_IMP_LIST_RULE (ulist o SYM);

(* Following conversion, GCONJ_CONV, offers the virtues
   of GCONJ_LIST in a conversion, hence potentially in a tactic
   as well as a rule. AND_IMP_THM or its conversion may exist under
   another name, but I can't find it. Object of GCONJ_CONV
   is to drag conjunctions to the top level, duplicating the antecedents
   and universal quantifiers which had been above them. The two
   subsidiary conversion have an obvious common pattern, and so could
   be written as applications of a conversional, say BINOP_ITER_CONV,
   but the latter seems as if it would be hard to explain. No parameter
   n here; GCONJ_CONV just breaks up all the top-level /\'s it finds,
   by recursion on the right operand, at the bottom of a ! - ==> nest. *)

val AND_IMP_THM = prove (Term`(H ==> B /\ C) = (H ==> B) /\ (H ==> C)`,
EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC);

fun IMP_CONJ_CONV t =
 ((REWR_CONV AND_IMP_THM THENC RAND_CONV IMP_CONJ_CONV)
  ORELSEC ALL_CONV) t;

fun FORALL_CONJ_CONV t =
 ((FORALL_AND_CONV THENC RAND_CONV FORALL_CONJ_CONV)
  ORELSEC ALL_CONV) t;

fun GCONJ_CONV t =
 (if is_imp t then RAND_CONV GCONJ_CONV
                   THENC IMP_CONJ_CONV
  else if is_forall t then RAND_CONV (ABS_CONV GCONJ_CONV)
                           THENC FORALL_CONJ_CONV
  else ALL_CONV) t;

(* Following rule, GCONJUNCTS, can sometimes replace GCONJ_LIST n, when n
 is the number of conjuncts that GCONJ_CONV will find (unlike CONJUNCTS,
 it does not recurse to the left). Only reason to bother with this is that
 it avoids SPEC_VAR, used by GCONJ_LIST, and temporarilly buggy with the
 advent of HOL-4, August '02. *)

val GCONJUNCTS = CONJUNCTS o CONV_RULE GCONJ_CONV;

(* Special rules for 2 and for 3 conjuncts *)

val GCONJ_PAIR = CONJ_PAIR o CONV_RULE GCONJ_CONV;

fun GCONJ_TRIP th = let val cj = CONV_RULE GCONJ_CONV th;
                        val (a, b) = CONJ_PAIR cj; val (c, d) = CONJ_PAIR b
                    in (a, c, d) end;

(* Next rule makes non-equational impl'ns usable by COND_REWRITE1_TAC *)

(* eqeqt = |- t = (t = T) ------- CAUTION, use only with ONCE_rules etc. *)

val eqeqt = SYM (hd (tl (CONJ_LIST 4 (SPEC_ALL EQ_CLAUSES))));

val FORALL_IMP_EQT_RULE = 
 hd o FORALL_IMP_LIST_RULE (ulist o PURE_ONCE_REWRITE_RULE [eqeqt]);

(* Front end, COND_RW_TAC, for COND_REWRITE1_TAC to make it aim at
   rewriting a non-equation (usually) to T. *)

fun COND_RW_TAC th = COND_REWRITE1_TAC (FORALL_IMP_EQT_RULE th);

(* Tacticals THENSGS, THENFIN to be used with a tactic like
   COND_REWRITE1_TAC which spawns an indeterminate number of subsidiary
   goals and finally a transformed main goal; the function then_sgs_fin
   is a bifurcating THEN applying different tactics to the two kinds of
   resulting goal, and the infix THENFIN and THENSGS specialize this. *)

(* If just two subgoals are generated, prefer THEN1 to THENSGS. *)

fun bisect 0 xs = ([], xs)  (* unappend, with given length of 1st piece *)
  | bisect n xxs = let val (l1, l2) = bisect (n-1) (tl xxs)
                         in (hd xxs :: l1, l2) end;

(* mapshape, used in Gordon and Melham to program THEN, is not provided 
   under that name in this system. We imitate G&M pp. 381, 383. *)

fun mapshape [] _ _ = []
  | mapshape mms ffs xs =
     let val (m, ms, f, fs) = (hd mms, tl mms, hd ffs, tl ffs);
         val (ys, zs) = bisect m xs
     in f ys :: mapshape ms fs zs end;

fun then_sgs_fin (T1, Tsgs, Tmg) g =
 let val (gl, p) = T1 g;
 in if null gl then ([], p) else
     let val (sgs, mgl) = bisect (length gl - 1) gl;
         val (gll, pl) = split (map Tsgs sgs);
         val (glm, pm) = Tmg (hd mgl);
         val (gll', pl') = (gll @ [glm], pl @ [pm])
     in (flatten gll', (p o mapshape (map length gll') pl'))
 end end;

fun T1 THENSGS T2 = then_sgs_fin (T1, T2, ALL_TAC);

fun T1 THENFIN T2 = then_sgs_fin (T1, ALL_TAC, T2);

(* Following four definitions are largely to give short names to workhorse
  tactics, but we avoid precise synonyms. CRE, CR are like
  COND_REWRITE1_TAC, COND_RW_TAC respectively (in particular they fail if
  they find no match) but they may solve the final (sub)goal completely if
  it is reduced respectively to a reflexive equation or to T. (Mnemonics:
  CR: "conditional rewriting",  E: "with an equation".)
     CREL, CRL take a list of conditional equations (resp. non-equations)
  and try rewriting once with each, from left to right in the list, working
  always on only the final subgoal produced by what has gone before, and
  at the end optimistically try to polish it off with TR_TAC. Note that
  there is no direct way to mix equational and non-equational theorems in
  one list, but alternating calls of CREL and CRL, joined by THENFIN,
  will do the job.                                                     *)

fun CRE th = COND_REWRITE1_TAC th THENFIN TRY REFL_TAC;
fun CR th = COND_RW_TAC th THENFIN TRY T_TAC;

fun CREL [] = TRY TR_TAC
  | CREL (th :: ths) = TRY (COND_REWRITE1_TAC th) THENFIN CREL ths;

fun CRL [] = TRY TR_TAC
  | CRL (th :: ths) = TRY (COND_RW_TAC th) THENFIN CRL ths;

(* A rule: GEXT, like EXT, but strips all the variables from 
   !x...z. F x ... z = G x ... z. *)

fun GEXT th =
 let fun iter_ext nil thm = thm
       | iter_ext (v :: l) thm = EXT (GEN v (iter_ext l thm));
     val (vars, _) = strip_forall (concl th)
 in iter_ext vars (SPEC_ALL th) end;

(* Iterated version, XL_FUN_EQ_CONV, of X_FUN_EQ_CONV for a sequence of
  specified variables, and corresp. tactic XL_FUN_EQ_TAC, which strips
  off the resulting universal quantifiers. *)

fun XL_FUN_EQ_CONV [] = ALL_CONV
  | XL_FUN_EQ_CONV (v :: vs) = X_FUN_EQ_CONV v THENC
                               QUANT_CONV (XL_FUN_EQ_CONV vs);

fun XL_FUN_EQ_TAC vl = CONV_TAC (XL_FUN_EQ_CONV vl) THEN 
                       MAP_EVERY (fn _ => GEN_TAC) vl;

(* A theorem to support XP_FUN_EQ_CONV *)

val pairFunEq = prove (Term
`!(M:'a#'b->'c) N. (!p:'a#'b. M p = N p) =
                   (!(q:'a) (r:'b). M (q, r) = N (q, r))`,
REPEAT GEN_TAC THEN EQ_TAC THENL
[REPEAT STRIP_TAC THEN AR
,REPEAT STRIP_TAC
 THEN CONV_TAC (BINOP_CONV (RAND_CONV (REWR_CONV (GSYM PAIR)))) THEN AR]);

(* XP_FUN_EQ_CONV (t1, t2) (f = g) =
         |- (f = g) = (!t1 t2. f (t1, t2) = g (t1, t2)) *)

fun XP_FUN_EQ_CONV (t1, t2) =
 FUN_EQ_CONV THENC REWR_CONV pairFunEq
 THENC RAND_CONV (ABS_CONV (GEN_ALPHA_CONV t2))
 THENC GEN_ALPHA_CONV t1;

(* Define X_UNSKOLEM_CONV, a conversion inverse to X_SKOLEM_CONV, for
 pushing an existentially quantified function variable f inside
 universal quantifications over variables x1, ... xn of its (Curried)
 argument types, changing it into an existentially quantified variable,
 y say, (supplied as first argument to X_UNSKOLEM_CONV) of the result
 type of f, and replacing applications f x1 ... xn in the body with
 occurrences of y. Stops pushing when the type of f x1 ... xi
 equals that of y. *)

fun X_UNSKOLEM_CONV y t = 
 let fun is_funtype ty =
       not (is_vartype ty) andalso (#Tyop (Rsyntax.dest_type ty) = "fun");
     fun argtype ty = hd (#Args (Rsyntax.dest_type ty));
     fun unskolemize (ptl_apn, tm) =
         if type_of ptl_apn = type_of y
         then Rsyntax.mk_exists {Bvar= y, Body= subst [ptl_apn |-> y] tm}
         else if is_funtype (type_of ptl_apn) andalso is_forall tm andalso 
                 type_of (bvar (rand tm)) = argtype (type_of ptl_apn)
         then Rsyntax.mk_forall {Bvar= bvar (rand tm),
                 Body= unskolemize
                 (Rsyntax.mk_comb {Rator= ptl_apn, Rand= bvar (rand tm)},
                  body (rand tm))}
         else raise (HOL_ERR {message= "cannot continue to unskolemize",
                                   origin_function= "X_UNSKOLEM_CONV",
                                   origin_structure= "ante_allTacs"});
     val {Bvar= fvar, Body= uterm} = Rsyntax.dest_exists t
 in SYM (X_SKOLEM_CONV fvar (unskolemize (fvar, uterm))) end;

(* Rule, RESQ_INST: thm -> thm -> thm, a variant of RESQ_SPEC.

   |- !x::P.A
----------------- RESQ_INST (|- P t)
   |- A[t/x]                          (INST short for "instantiate") *)

fun RESQ_INST tisP = 
 let val Pt = concl tisP;
     val t = rand Pt
 in fn allxPdotA => MP (DISCH Pt (RESQ_SPEC t allxPdotA)) tisP end;

(* Version of UNDISCH for an antecedent which may be T or a conjunction or
   an instance of REFL: idea is keep the world safe for ASM_REWRITE_TAC.*)

fun CONJ_UNDISCH th = (* now (11/15/99) with beta-conversion *)
 let val thm = CONV_RULE (LAND_CONV (DEPTH_CONV BETA_CONV)) th;
     val {ant=ante, ...} = Rsyntax.dest_imp (concl thm)
 in if ante = --`T`-- orelse (is_eq ante andalso
       (#lhs (Rsyntax.dest_eq ante) = #rhs (Rsyntax.dest_eq ante)))
    then CONV_RULE (LAND_CONV (REWRITE_CONV [])
              THENC REWR_CONV (CONJUNCT1 (SPEC_ALL IMP_CLAUSES))) thm
    else if is_conj ante then
              CONJ_UNDISCH (CONJ_UNDISCH (CONV_RULE ANTE_CONJ_CONV thm))
    else UNDISCH thm
 end;

fun CONJ_ASSUME_TAC th = (* similar; now with better beta-conversion *)
 let val thm = CONV_RULE (DEPTH_CONV BETA_CONV) th
 in if concl thm = --`T`-- orelse (is_eq (concl thm)
       andalso (#lhs (Rsyntax.dest_eq (concl thm)) =
                #rhs (Rsyntax.dest_eq (concl thm))))
    then ALL_TAC
    else if is_conj (concl thm) then
          let val (th1, th2) = CONJ_PAIR thm
          in CONJ_ASSUME_TAC th1 THEN CONJ_ASSUME_TAC th2 end
    else ASSUME_TAC thm end;

(* Note that CONJ_DISCH_TAC may fail, and so is REPEATable; where a never-
 failing version is needed, just use TRY CONJ_DISCH_TAC. *)

val CONJ_DISCH_TAC = DISCH_THEN CONJ_ASSUME_TAC;

val HALF_CONJ_DISCH_TAC = HALF_DISCH_THEN CONJ_ASSUME_TAC;

(* A tactic, EXISTS_UNIQUE_TAC, allowing to provide a witness in order
   to solve a unique existance (?!x. ...) goal. Example (in the presence
   of arithmeticTheory):

g`?!z:num. !w. z <= w`;           Initial goal: ?!z. !w. z <= w
e(EXISTS_UNIQUE_TAC (Term `0`));
 2 subgoals: [!w. 0 <= w] ?- !z. (!w. z <= w) ==> (z = 0)
                             !w. 0 <= w                   *)

fun EXISTS_UNIQUE_TAC u = CONV_TAC EXISTS_UNIQUE_CONV THEN
 (fn (g as (_, exanduq)) =>
  let val {conj1= ex, conj2= _} = Rsyntax.dest_conj exanduq;
      val {Bvar= x, Body= tx} = Rsyntax.dest_exists ex;
  in (CONV_TAC LEFT_AND_EXISTS_CONV
      THEN EXISTS_TAC u
      THEN CUMUL_CONJ_TAC THENL
      [ALL_TAC,
       DISCH_THEN (fn tu =>
        CONJ_ASSUME_TAC tu
        THEN SUBGOAL_THEN (Term`!(^x).(^tx ==> (^x = ^u))`)
        (fn allu => GEN_TAC THEN GEN_TAC
         THEN HALF_DISCH_THEN (fn tyth =>
          DISCH_THEN (fn tzth => ACCEPT_TAC (TRANS
           (MATCH_MP allu tyth) (SYM (MATCH_MP allu tzth)))))))]) g end);

(* An analogue of EXISTS_UNIQUE_TAC that works like STRIP_TAC on a
  unique existence top-level hypothesis.

                  A ?- (?!x. Q[x]) ==> M
           ==================================== STRIP_EXISTS_UNIQUE_TAC
           A, Q[x] ?- (!y. Q[y] ==> (y = x)) ==> M

  Normally STRIP_EXISTS_UNIQUE_TAC will be followed immediately by
  DISCH_TAC, but this step has intentionally not been included in case
  some other disposition of the uniqueness hypothesis is preferred.

  Example: g`(?!z:num. !w. z <= w) ==> M`; e(STRIP_EXISTS_UNIQUE_TAC);
  results in:  (!z'. (!w. z' <= w) ==> (z' = z)) ==> M
               ------------------------------------
                  !w. z <= w                                    *)

val STRIP_EXISTS_UNIQUE_TAC =
 CONV_TAC ((LAND_CONV EXISTS_UNIQUE_CONV) THENC ANTE_CONJ_CONV
           THENC LEFT_IMP_EXISTS_CONV)
 THEN (fn (g as (_, uimp)) =>
       let val {Bvar= x, Body= _} = Rsyntax.dest_forall uimp
       in (GEN_TAC
           THEN DISCH_THEN (fn wit => CONJ_ASSUME_TAC wit THEN
                 DISCH_THEN (fn cimp => MP_TAC (symOfEqn
                  (MATCH_MP (CONV_RULE (ONCE_DEPTH_CONV ANTE_CONJ_CONV)
                             cimp) wit))))) g end);

(* Following two thm-tacticals, IMP_RES_THENL and IMP_RES_ASM_THENL,
   iterate IMP_RES_THEN for a fixed number of stages (so that the 
   theorem argument should have that many iterated hypotheses at least)
   and rewrite the theorem(s) emerging from each stage; like IMP_RES_THEN,
   the disposition of the finally emerging theorem(s) is for the th-tactic
   argument to determine. An additional, first, theorem list list argument
   has a sublist for every stage of IMP_RES_THEN to be applied, and each
   sublist gives theorems to be used in rewriting each conclusion at that
   stage; for IMP_RES_ASM_THENL, the current assumptions are thrown in
   to every stage of rewriting as well. See fstbi_natTh for an example. *)

fun IMP_RES_THENL [] thtac = thtac
  | IMP_RES_THENL (ths :: thss) thtac =
     IMP_RES_THEN (fn th' =>
      IMP_RES_THENL thss thtac (REWRITE_RULE ths th'));

fun IMP_RES_ASM_THENL [] thtac = thtac
  | IMP_RES_ASM_THENL (ths :: thss) thtac =
     IMP_RES_THEN (fn th' => ASSUM_LIST (fn asms =>
       IMP_RES_ASM_THENL thss thtac (REWRITE_RULE (ths @ asms) th')));

(* What would be the specification for RES_ABSTRACT if pred_set's had
 not been put in in place of plain predicates: *)

val RES_ABSTRACT_PRED = REWRITE_RULE [SPECIFICATION] RES_ABSTRACT;

(* RES_ABSTRACT_PRED = |- !p m x. p x ==> (RES_ABSTRACT p m x = m x)  *)

(* The old RESQ_FORALL_CONV, putting in a predication rather than an IN
 in the hypothesis: |- !x::P. M = !x. P x ==> M *)

val RESQ_FORALL_CONV = RES_FORALL_CONV THENC
 RAND_CONV (ABS_CONV (LAND_CONV (REWR_CONV SPECIFICATION)));

(* following will reduce restricted beta-redexes, incurring an assumption;
 RES_BETA_CONV gives new Hurd-style (with IN); RESQ_BETA_CONV gives
 old (with predication) style assumption. *)

fun RESQ_BETA_CONV app =
 let val rab = rator app;
     val (pred, func) = (rand (rator rab), rand rab);
     val imp = ISPECL [pred, func, rand app] RES_ABSTRACT_PRED
 in (REWR_CONV (UNDISCH imp) THENC BETA_CONV) app end;

fun RES_BETA_CONV app =
 let val rab = rator app;
     val (pred, func) = (rand (rator rab), rand rab);
     val imp = ISPECL [pred, func, rand app] RES_ABSTRACT
 in (REWR_CONV (UNDISCH imp) THENC BETA_CONV) app end;

(* abs_remove turns equations to lambda-abstractions into universally
 quantified equations with application to the variables on the left; in
 two versions to use the two flavors of RES(Q)_BETA_CONV. pure_abs_remove
 is for when one wants to see IN's in the hypotheses of the result. *)

fun gen_abs_remove Pure th = 
let fun abs_rem th =
 if is_forall (concl th) 
 then let val (v, th') = SPEC_VAR th
      in GEN v (abs_rem th') end
 else if is_imp (concl th)
 then let val {ant= a, conseq= c} = Rsyntax.dest_imp (concl th)
      in DISCH a (abs_rem (UNDISCH th)) end
 else if is_let (concl th)
 then abs_rem (CONV_RULE let_CONV th)
 else if is_conj (concl th)
 then CONJ (abs_rem (CONJUNCT1 th)) (abs_rem (CONJUNCT2 th))
 else if is_eq (concl th)
 then let val {lhs= header, rhs= defn} = Rsyntax.dest_eq (concl th)
      in if is_abs defn
         then let val v = #Bvar (Rsyntax.dest_abs defn)
              in abs_rem (CONV_RULE
                             (X_FUN_EQ_CONV v THENC
                      RAND_CONV (ABS_CONV (RAND_CONV BETA_CONV))) th) end
         else if is_pabs defn
         then let val th' = abs_rem (CONV_RULE
                           (LAND_CONV (REWR_CONV (GSYM UNCURRY_CURRY_THM))
                            THENC REWR_CONV UNCURRY_ONE_ONE_THM) th);
              in CONV_RULE (ONCE_DEPTH_CONV (REWR_CONV CURRY_DEF)) th' end
         else if is_res_abstract defn
         then
          let val (v, P, _) = dest_res_abstract defn;
              val Pv = if Pure then Term`^v IN ^P`
                       else Rsyntax.mk_comb {Rator= P, Rand= v};
              val th' = SPEC_ALL (CONV_RULE (X_FUN_EQ_CONV v) th);
              val th'' = UNDISCH (DISCH Pv th');
              val th''' = CONV_RULE (RAND_CONV 
                           (if Pure then RES_BETA_CONV
                                    else RESQ_BETA_CONV)) th'';
              val thiv = DISCH Pv (abs_rem th''')
          in GEN v (if is_abs P andalso not Pure
                    then CONV_RULE (LAND_CONV BETA_CONV) thiv else thiv)
 end else th end else th
in abs_rem th end;

val pure_abs_remove = gen_abs_remove true;

val abs_remove = gen_abs_remove false;

val let_remove = CONV_RULE (DEPTH_CONV let_CONV); (* sometimes useful *)

end;