(* File: IntegrityLevels_conv.sig created 3/18/2011 *)

(* Author: Shiu-Kai Chin, skchin@syr.edu *)

signature IntegrityLevels_conv =

sig

type tactic = Abbrev.tactic;

type thm_tactic = Abbrev.thm_tactic;

type conv = Abbrev.conv;

type thm = Thm.thm;

type term = Term.term

val ICOrder_PO_CONV : term -> thm

end;