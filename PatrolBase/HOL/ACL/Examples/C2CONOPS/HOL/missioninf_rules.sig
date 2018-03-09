signature missioninf_rules =

sig



type tactic = Abbrev.tactic;

type thm_tactic = Abbrev.thm_tactic;

type conv = Abbrev.conv;

type thm = Thm.thm;

type term = Term.term

val ImpliedControlsSays : term -> thm -> thm -> thm -> thm
val DualControl : thm -> thm -> thm -> thm
val AltControls1 : thm -> thm -> thm
val AltControls2 : thm -> thm -> thm
val ImpliedControlsDelegation : term -> thm -> thm -> thm -> thm -> thm

end;