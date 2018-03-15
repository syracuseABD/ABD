(* File: SecurityLevels_conv.sig created 3/20/2009 *)

(* Author: Shiu-Kai Chin, skchin@syr.edu *)



signature SecurityLevels_conv =

sig



type tactic = Abbrev.tactic;

type thm_tactic = Abbrev.thm_tactic;

type conv = Abbrev.conv;

type thm = Thm.thm;

type term = Term.term

val OSec_CONV : term -> thm;


end;
