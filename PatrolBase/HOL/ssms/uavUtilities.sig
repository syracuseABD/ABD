signature uavUtilities = sig

type tactic = Abbrev.tactic;

type thm_tactic = Abbrev.thm_tactic;

type conv = Abbrev.conv;

type thm = Thm.thm;

type term = Term.term;

type hol_type = Type.hol_type;

val trustedOn : term -> term -> term

val trustedOnList : term -> term list -> term list

val trappedOn : term -> term -> term

val trappedOnList : term -> term list -> term list

val andfTermList : term list -> hol_type -> term

val impfTermList : term list -> hol_type -> term

val condTrap : term list -> hol_type -> term

end