(* File: ante_allTacs.sig, created 7/27/02 *)
(* Author: F. Lockwood Morris  <lockwood@ecs.syr.edu> *)

signature ante_allTacs =
sig

type tactic = Abbrev.tactic;
type thm_tactic = Abbrev.thm_tactic;
type conv = Abbrev.conv;
type thm = Thm.thm;
type term = Term.term

val CUMUL_CONJ_TAC : tactic;
val T_TAC : tactic;
val TR_TAC : tactic;
val ANTE_DROP_TAC : tactic;
val UNASSUME_TAC : thm -> tactic;
val ulist : 'a -> 'a list;
val HALF_DISCH_THEN : thm_tactic -> tactic;
val SWAP_HALF_DISCH_THEN : thm_tactic -> tactic;
val HALF_DISCH_TAC : tactic;
val SWAP_HALF_DISCH_TAC : tactic;
val LLAND_CONV : conv -> conv;
val LRAND_CONV : conv -> conv;
val RLAND_CONV : conv -> conv;
val RRAND_CONV : conv -> conv;
val ASM_SYM_TAC : term -> tactic;
val AR : tactic;
val LEMMA_MP_TAC : term -> tactic;
val LEMMA_TAC : term -> tactic;
val MATCH_MP2 : thm -> thm -> thm -> thm;
val EQ_HYP_TAC : term -> tactic;
val lines : string -> term -> bool;
val asm : string -> term -> bool;
val with_asm : string -> thm_tactic -> tactic;
val drop_asm : string -> tactic;
val und_asm: string -> tactic;
val tty : unit -> bool;
val is_unap : string -> term -> bool;
val is_binap : string -> term -> bool;
val REV_EXISTS_CONV : conv;
val REV_FORALL_CONV : conv;
val DUP_TAC : 'a -> 'a list;
val DUP_ARGS_TAC : 'a * 'a -> ('a -> 'b) -> 'b list;
val FORALL_IMP_LIST_RULE : (thm -> thm list) -> thm -> thm list;
val GCONJ_LIST : int -> thm -> thm list;
val impOfEqn : thm -> thm;
val impByOfEqn : thm -> thm;
val symOfEqn : thm -> thm;
val GCONJ_CONV : term -> thm;
val GCONJUNCTS : thm -> thm list;
val GCONJ_PAIR : thm -> thm * thm;
val GCONJ_TRIP : thm -> thm * thm * thm;
val COND_RW_TAC : thm -> tactic;
val THENSGS : tactic * tactic -> tactic;
val THENFIN : tactic * tactic -> tactic;
val CRE : thm_tactic;
val CR : thm_tactic;
val CREL : thm list -> tactic;
val CRL : thm list -> tactic;
val GEXT : thm -> thm;
val XL_FUN_EQ_CONV : term list -> conv;
val XL_FUN_EQ_TAC : term list -> tactic;
val XP_FUN_EQ_CONV : term * term -> conv;
val X_UNSKOLEM_CONV : term -> conv;
val RESQ_INST : thm -> thm -> thm;
val CONJ_UNDISCH : thm -> thm
val CONJ_ASSUME_TAC : thm -> tactic;
val CONJ_DISCH_TAC : tactic;
val HALF_CONJ_DISCH_TAC : tactic;
val EXISTS_UNIQUE_TAC : term -> tactic;
val STRIP_EXISTS_UNIQUE_TAC : tactic;
val IMP_RES_THENL : thm list list -> thm_tactic -> thm_tactic;
val IMP_RES_ASM_THENL : thm list list -> thm_tactic -> thm_tactic;
val RES_ABSTRACT_PRED : thm;
val RESQ_FORALL_CONV : conv;
val RESQ_BETA_CONV : conv;
val RES_BETA_CONV : conv;
val abs_remove : thm -> thm;
val pure_abs_remove : thm -> thm;
val let_remove : thm -> thm;

end;