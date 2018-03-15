(* File: aclTermFuns.sig created 8/12/2015 *)

(* Author: Steven Perkins*)



signature aclTermFuns =

sig

type term = Term.term;

val sat : term

val prop : term

val notf : term

val andf : term

val orf : term

val impf : term

val eqf : term

val says : term

val speaks_for : term

val controls : term

val reps : term

val domi : term

val eqi : term

val doms : term

val eqs : term

val eqn : term

val lte : term

val lt : term

val meet : term

val quoting : term

val mk_sat : term * term -> term

val mk_prop : term -> term

val mk_notf : term -> term

val mk_andf : term * term -> term

val mk_orf : term * term -> term

val mk_impf : term * term -> term

val mk_eqf : term * term -> term

val mk_says : term * term -> term

val mk_speaks_for : term * term -> term

val mk_controls : term * term -> term

val mk_reps : term * term * term -> term

val mk_domi : term * term -> term

val mk_eqi : term * term -> term

val mk_doms : term * term -> term

val mk_eqs : term * term -> term

val mk_eqn : term * term -> term

val mk_lte : term * term -> term

val mk_lt : term * term -> term

val mk_meet : term * term -> term

val mk_quoting : term * term -> term

val dest_sat : term -> term * term

val dest_prop : term -> term

val dest_notf : term -> term

val dest_andf : term -> term * term

val dest_orf : term -> term * term

val dest_impf : term -> term * term

val dest_eqf : term -> term * term

val dest_says : term -> term * term

val dest_speaks_for : term -> term * term

val dest_controls : term -> term * term

val dest_reps : term -> term * term * term

val dest_domi : term -> term * term

val dest_eqi : term -> term * term

val dest_doms : term -> term * term

val dest_eqs : term -> term * term

val dest_eqn : term -> term * term

val dest_lte : term -> term * term

val dest_lt : term -> term * term

val dest_meet : term -> term * term

val dest_quoting : term -> term * term

val is_sat : term -> bool

val is_prop : term -> bool

val is_notf : term -> bool

val is_andf : term -> bool

val is_orf : term -> bool

val is_impf : term -> bool

val is_eqf : term -> bool

val is_says : term -> bool

val is_speaks_for : term -> bool

val is_controls : term -> bool

val is_reps : term -> bool

val is_domi : term -> bool

val is_eqi : term -> bool

val is_doms : term -> bool

val is_eqs : term -> bool

val is_eqn : term -> bool

val is_lte : term -> bool

val is_lt : term -> bool

val is_meet : term -> bool

val is_quoting : term -> bool


end;
