(* Mission Validation Appliance example: SKC 15 November 2010 *)

structure mvaRulesScript =
struct

(* paths opened with INCLUDES in Holmakefule set to ../../../ *)
(* ../Cloud ..                                            *)
(* Interactive mode *)
(*
load "acl_infRules";
*)

open HolKernel boolLib Parse bossLib
open acl_infRules;

val _ = new_theory "mvaRules";

(* MVA Out derived inference rule:                        *)
(*                                                    *)
(*       Token says Role says s                          *)
(*  K_Auth says Person reps Role on s                     *)
(*  K_Auth says Token speaksfor Person                    *)
(*  Auth controls Person reps Role on s                    *)
(*  Auth controls Token speaksfor Person                   *)
(*        K_Auth speaksfor Auth                          *)
(*  -----------------------                  *)
(*        K_{Box} says Role says s                        *)

(* Recall the definition of ACL_ASSUM: *)
(* fun ACL_ASSUM f = ASSUME (Term `(M,Oi,Os) sat ^f`)   *)

val MVA_out =
let
	val a1 = ACL_ASSUM ``(Token:'c Princ) says (Role says f:('a,'c,'d,'e)Form)``
    	val a2 = ACL_ASSUM ``(K_Auth:'c Princ) says (reps Person Role (f:('a,'c,'d,'e)Form))``
	val a3 = ACL_ASSUM ``(K_Auth:'c Princ) says (Token speaks_for (Person:'c Princ)):('a,'c,'d,'e)Form``
	val a4 = ACL_ASSUM ``(Auth:'c Princ) controls (reps Person Role (f:('a,'c,'d,'e)Form))``
	val a5 = ACL_ASSUM ``(Auth:'c Princ) controls ((Token speaks_for Person):('a,'c,'d,'e)Form)``
	val a6 = ACL_ASSUM ``(K_Auth speaks_for Auth):('a,'c,'d,'e)Form``
	val th7 = SPEAKS_FOR a6 a2
	val th8 = SPEAKS_FOR a6 a3
	val th9 = CONTROLS a4 th7
	val th10 = CONTROLS a5 th8
	val th11 = SPEAKS_FOR th10 a1
	val th12 = QUOTING_RL th11
	val th13 = REP_SAYS th9 th12
	val th14 = SAYS ``K_Box:'c Princ`` th13
	val th15 =
	GENL [``(M :('a, 'b, 'c, 'd, 'e) Kripke)``,``(Oi :'d po)``,``(Os :'e po)``,
    	 ``(Token:'c Princ)``,``(Role: 'c Princ)``,``(f :('a, 'c, 'd, 'e) Form)``,
	      ``(K_Auth:'c Princ)``,``(Auth: 'c Princ)``,``(Person: 'c Princ)``]
	(DISCH ``(M,Oi,Os) sat (Token says Role says f) ``
	(DISCH ``(M,Oi,Os) sat K_Auth says (reps Person Role f)`` 
	(DISCH ``(M,Oi,Os) sat (K_Auth says (Token speaks_for Person))`` 
	(DISCH ``(M,Oi,Os) sat Auth controls (reps Person Role f)``
	(DISCH ``((M:('a,'b,'c,'d,'e)Kripke),Oi,Os) sat (Auth controls (Token speaks_for Person))``
	(DISCH ``((M :(α, β, γ, δ, ε) Kripke),(Oi :δ po),(Os :ε po)) sat
     	(((K_Auth :γ Princ) speaks_for (Auth :γ Princ)) :(α, γ, δ, ε) Form)`` th14))))))
	in
	save_thm("MVA_out",th15)
end;

val MVA_in =
let
	val a1 = ACL_ASSUM ``(K_Box:'c Princ) says (Role says f:('a,'c,'d,'e)Form)``
    	val a2 = ACL_ASSUM ``(K_Auth:'c Princ) says (reps Box Role (f:('a,'c,'d,'e)Form))``
	val a3 = ACL_ASSUM ``(K_Auth:'c Princ) says (K_Box speaks_for (Box:'c Princ)):('a,'c,'d,'e)Form``
	val a4 = ACL_ASSUM ``(Auth:'c Princ) controls (reps Box Role (f:('a,'c,'d,'e)Form))``
	val a5 = ACL_ASSUM ``(Auth:'c Princ) controls ((K_Box speaks_for Box):('a,'c,'d,'e)Form)``
	val a6 = ACL_ASSUM ``(K_Auth speaks_for Auth):('a,'c,'d,'e)Form``
	val th7 = SPEAKS_FOR a6 a2
	val th8 = SPEAKS_FOR a6 a3
	val th9 = CONTROLS a4 th7
	val th10 = CONTROLS a5 th8
	val th11 = SPEAKS_FOR th10 a1
	val th12 = QUOTING_RL th11
	val th13 = REP_SAYS th9 th12
	val th14 =
	GENL [``(M :('a, 'b, 'c, 'd, 'e) Kripke)``,``(Oi :'d po)``,``(Os :'e po)``,
    	 ``(Token:'c Princ)``,``(Role: 'c Princ)``,``(f :('a, 'c, 'd, 'e) Form)``,
	      ``(K_Auth:'c Princ)``,``(Auth: 'c Princ)``,``(Person: 'c Princ)``]
	(DISCH ``(M,Oi,Os) sat (K_Box says Role says f) ``
	(DISCH ``(M,Oi,Os) sat K_Auth says (reps Box Role f)`` 
	(DISCH ``(M,Oi,Os) sat (K_Auth says (K_Box speaks_for Box))`` 
	(DISCH ``(M,Oi,Os) sat Auth controls (reps Box Role f)``
	(DISCH ``((M:('a,'b,'c,'d,'e)Kripke),Oi,Os) sat (Auth controls (K_Box speaks_for Box))``
	(DISCH ``((M :(α, β, γ, δ, ε) Kripke),(Oi :δ po),(Os :ε po)) sat
     	(((K_Auth :γ Princ) speaks_for (Auth :γ Princ)) :(α, γ, δ, ε) Form)`` th13))))))
	in
	save_thm("MVA_in",th14)
end;



val _ = print_theory "-";
val _ = export_theory ();

end;