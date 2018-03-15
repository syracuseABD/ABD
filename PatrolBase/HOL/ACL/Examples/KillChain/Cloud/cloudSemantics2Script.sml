(************************************************************)
(* Operational semantics for cloud operations               *)
(* Created 28 November 2010 by Shiu-Kai Chin                *)
(* Earlier version created for CSE 691: Art & Practice of   *)
(* Cyber Defense                                            *)
(* Fall 2010 version of ACE                                 *)
(************************************************************)

(* Interactive mode
val aclPath = "/home/skchin/Documents/RESEARCH/HOL/ACL";
val killPath = "/home/skchin/Documents/RESEARCH/HOL/ACL/Examples/KillChain";
loadPath := aclPath::(killPath::(!loadPath));
app load ["IndDefRules","messageTheory","IntegrityLevelsTheory","aclfoundationTheory","aclsemanticsTheory",
 "aclrulesTheory","aclDrulesTheory","cloudOperationsTheory","acl_infRules","stringTheory"];

(* Disable Pretty-Printing *)
set_trace "Unicode" 0;
*)

structure cloudSemantics2Script = struct

open HolKernel boolLib Parse bossLib
open IndDefRules messageTheory IntegrityLevelsTheory aclfoundationTheory aclsemanticsTheory 
 aclrulesTheory cloudOperationsTheory aclDrulesTheory acl_infRules stringTheory;

(***********
* create a new theory
***********)
val _ = new_theory "cloudSemantics2";

(************************
* THE DEFINITIONS START HERE
************************)

(****************************************************************)
(* We rely on the definitions of aclfoundationTheory.           *)
(* The type signature of Kripke structure M is                  *)
(* :(Contents, 'world, 'name, 'il, 'sl) where Contents          *)
(* is the type of the content of messages sent back and         *)
(* forth among JTACs, Controllers, and Pilots.                  *)
(*                                                              *)
(* If we wish to specify the internal structure of M, we have:  *)
(* KS (Intp:(Contents -> ('world set)))                         *)
(* (Jfn:('name -> ('world -> ('world set))))                    *)
(*        (ilmap:('name -> 'il)) (slmap:('name -> 'sl))         *)
(* Hol_reln does not accept any type variables. We use strings  *)
(* for worlds and principal names. For integrity levels we use  *)
(* IClass defined in IntegrityLevelsTheory. As we don't need    *)
(* security we use the unit type.                               *)
(****************************************************************)

(************************************************************)
(* In this concept of operations (CONOPS), the cloud is trusted with          *)
(* credentials. People authenticate themselves to the cloud using a token.      *)
(* This allows messages to be sent to mailboxes labeled by roles instead of    *)
(* public keys.                                                         *)
(*                                                                    *)
(* We wish to update the Controller mailbox under three conditions:           *)
(*  (1) when a legitimate JTAC sends an air strike request to the Controller,  *)
(*  (2) when the Controller sends an air strike order to the pilot, and       *)
(*  (3) when the Controller sends approval of an air strike request to a JTAC.*)
(*                                                                   *)
(* The three clauses in Hol_reln describe the above three conditions in the     *)
(* access-control logic.                                                *)
(*  (1) (M,Oi,Os) sat (Name "JTAC") says (prop (asrM asr)) states that the  *)
(*      air strike request asr came from a JTAC,                         *)
(*  (2) (M,Oi,Os) sat (Name "Controller") says (prop (asoM aso)) states that *)
(*      air strike order aso came from the Controller, and                 *)
(*  (3) (M,Oi,Os) sat (Name "Controller") says (prop (asaM asa)) states that *)
(*      air strike approval asa came from the Controller.                   *)
(************************************************************)

val (EV2_rules,EV2_ind,EV2_cases) =
  Hol_reln
  `(!(M:(Contents, string, string, IClass, one) Kripke)(Oi:IClass po)(Os:one po)
     (Token: string Princ)(asr:ASR).
      ((M,Oi,Os) sat (Name "JTAC") says (prop (asrM asr))  ==>
       (EV2 
	((MSG (From (Token quoting (Name "JTAC")), 
	       To (Name "Controller"), asrM asr)), state:string State) 
	(updateCloudState 
	 (MSG (From (Token quoting (Name "JTAC")), 
	       To (Name "Controller"), asrM asr)) state)))) 
    /\
   (!(M:(Contents, string, string, IClass, one) Kripke)(Oi:IClass po)(Os:one po)
     (Token: string Princ)(aso:ASO).
      ((M,Oi,Os) sat (Name "Controller") says (prop (asoM aso))  ==>
       (EV2 
	((MSG (From (Token quoting (Name "Controller")), 
	       To (Name "Pilot"), asoM aso)), state:string State) 
	(updateCloudState (MSG (From (Token quoting (Name "Controller")), 
			       To (Name "Pilot"), asoM aso)) state)))) 
    /\
   (!(M:(Contents, string, string, IClass, one) Kripke)(Oi:IClass po)(Os:one po)
     (Token: string Princ)(asa:ASA).
       ((M,Oi,Os) sat (Name "Controller") says (prop (asaM asa))  ==>
   (EV2 
    ((MSG (From (Token quoting (Name "Controller")), 
	   To (Name "JTAC"), asaM asa)), state:string State) 
    (updateCloudState (MSG (From (Token quoting (Name "Controller")), 
			  To (Name "JTAC"), asaM asa)) state))))`;

(************************************************************)
(* We can relate the operational semantics of the cloud to reasoning about     *)
(* credentials in the cloud. Consider the following derived inference rule:      *)
(*                                                                   *)
(*       Token | Role says s                                            *)
(*  K_Auth says Person reps Role on s                                    *)
(*  K_Auth says Token speaksfor Person                                   *)
(*  Auth controls Person reps Role on s                                   *)
(*  Auth controls Token speaksfor Person                                  *)
(*     K_Auth speaksfor Auth                                            *)
(* ------------------------                                 *)
(*            Role says s                                               *)
(*                                                                    *)
(* The actual theorem is:                                                *)
(*     |- ∀M Oi Os Token Role s K_Auth Auth Person.                      *)
(*       (M,Oi,Os) sat Token quoting Role says s ⇒                        *)
(*       (M,Oi,Os) sat K_Auth says reps Person Role s ⇒                    *)
(*       (M,Oi,Os) sat K_Auth says Token speaks_for Person ⇒               *)
(*       (M,Oi,Os) sat Auth controls reps Person Role s ⇒                   *)
(*       (M,Oi,Os) sat Auth controls Token speaks_for Person ⇒              *)
(*       (M,Oi,Os) sat K_Auth speaks_for Auth ⇒                           *)
(*       (M,Oi,Os) sat Role says s                                        *)
(************************************************************)

val Cloud_Auth =
let
 val a1 = ACL_ASSUM ``((Token:'c Princ) quoting (Role:'c Princ)) says s:('a,'c,'d,'e)Form``
 val a2 = ACL_ASSUM ``(K_Auth:'c Princ) says reps (Person:'c Princ) (Role) s:('a,'c,'d,'e)Form``
 val a3 = ACL_ASSUM ``(K_Auth:'c Princ) says ((Token:'c Princ) speaks_for (Person:'c Princ)):('a,'c,'d,'e)Form``
 val a4 = ACL_ASSUM ``Auth:'c Princ controls reps (Person:'c Princ) (Role:'c Princ) s:('a,'c,'d,'e)Form``
 val a5 = ACL_ASSUM ``Auth:'c Princ controls (Token speaks_for Person):('a,'c,'d,'e)Form``
 val a6 = ACL_ASSUM ``(K_Auth:'c Princ speaks_for Auth):('a,'c,'d,'e)Form``
 val th7 = QUOTING_LR a1
 val th8 = SPEAKS_FOR a6 a3
 val th9 = CONTROLS a5 th8
 val th10 = SPEAKS_FOR th9 th7
 val th11 = QUOTING_RL th10
 val th12 = SPEAKS_FOR a6 a2
 val th13 = CONTROLS a4 th12
 val th14 = REP_SAYS th13 th11
 val th15 = GENL [``(M :('a, 'b, 'c, 'd, 'e) Kripke)``,``(Oi :'d po)``,``(Os :'e po)``,
    	        ``(Token:'c Princ)``,``(Role: 'c Princ)``,``(s :('a, 'c, 'd, 'e) Form)``,
	   	``(K_Auth:'c Princ)``,``(Auth: 'c Princ)``,``(Person: 'c Princ)``]
	   (DISCH ``(M:('a,'b,'c,'d,'e)Kripke,Oi,Os) sat ((Token quoting Role) says s)``
	   (DISCH ``(M:('a,'b,'c,'d,'e)Kripke,Oi,Os) sat (K_Auth says (reps Person Role s))``
	   (DISCH ``(M:('a,'b,'c,'d,'e)Kripke,Oi,Os) sat (K_Auth says (Token speaks_for Person))``
	   (DISCH ``(M:('a,'b,'c,'d,'e)Kripke,Oi,Os) sat (Auth controls reps Person Role s)``
	   (DISCH ``(M:('a,'b,'c,'d,'e)Kripke,Oi,Os) sat (Auth controls (Token speaks_for Person))``
	   (DISCH ``(M:('a,'b,'c,'d,'e)Kripke,Oi,Os) sat (K_Auth speaks_for Auth)`` th14))))))
	   in
	   save_thm("Cloud_Auth",th15)
end;

val [asrEV2_rule, asoEV2_rule, asaEV2_rule] = CONJUNCTS EV2_rules;
val asrEV2_rule = save_thm("asrEV2_rule",asrEV2_rule);
val asoEV2_rule = save_thm("asoEV2_rule",asoEV2_rule);
val asaEV2_rule = save_thm("asaEV2_rule",asaEV2_rule);

val asrUpdate_rule =
let
 val th1 = 
    UNDISCH_ALL(ISPECL 
    [``(M :(Contents, string, string, IClass, unit) Kripke)``,
     ``Oi:IClass po``,``Os:unit po``,``Token:string Princ``,``Name "JTAC"``,
     ``prop (asrM asr):(Contents,string,IClass,unit)Form``,``K_Auth:string Princ``,
     ``Auth:string Princ``,``Person:string Princ``] Cloud_Auth)
 val th2 = SPEC_ALL asrEV2_rule
 val th3 = MP th2 th1
 val th4 = 
 GENL [``(M :(Contents, string, string, IClass, unit) Kripke)``,
       ``(Oi :IClass po)``,``(Os :unit po)``,``(Token:string Princ)``,
       ``(K_Auth:string Princ)``,``(Auth: string Princ)``,
       ``(Person: string Princ)``,``asr:ASR``,``state:string State``]
      (DISCH 
       ``(M:(Contents,string,string,IClass,unit)Kripke,Oi,Os) sat 
         ((Token quoting (Name "JTAC")) says (prop (asrM asr)))``
       (DISCH 
        ``(M:(Contents,string,string,IClass,unit)Kripke,Oi,Os) sat 
	  (K_Auth says (reps Person (Name "JTAC") (prop (asrM asr))))``
	(DISCH 
	 ``(M:(Contents,string,string,IClass,unit)Kripke,Oi,Os) sat 
	   (K_Auth says (Token speaks_for Person))``
	 (DISCH 
	  ``(M:(Contents,string,string,IClass,unit)Kripke,Oi,Os) sat 
	    (Auth controls reps Person (Name "JTAC") (prop (asrM asr)))``
	  (DISCH 
	   ``(M:(Contents,string,string,IClass,unit)Kripke,Oi,Os) sat 
	     (Auth controls (Token speaks_for Person))``
	   (DISCH 
	   ``(M:(Contents,string,string,IClass,unit)Kripke,Oi,Os) sat 
	     (K_Auth speaks_for Auth)`` th3))))))
	     in
	     save_thm("asrUpdate_rule",th4)
end;


val asoUpdate_rule =
let
 val th1 = 
    UNDISCH_ALL(ISPECL 
    [``(M :(Contents, string, string, IClass, unit) Kripke)``,
     ``Oi:IClass po``,``Os:unit po``,``Token:string Princ``,``Name "Controller"``,
     ``prop (asoM aso):(Contents,string,IClass,unit)Form``,``K_Auth:string Princ``,
     ``Auth:string Princ``,``Person:string Princ``] Cloud_Auth)
 val th2 = SPEC_ALL asoEV2_rule
 val th3 = MP th2 th1
 val th4 = 
 GENL [``(M :(Contents, string, string, IClass, unit) Kripke)``,
       ``(Oi :IClass po)``,``(Os :unit po)``,``(Token:string Princ)``,
       ``(K_Auth:string Princ)``,``(Auth: string Princ)``,
       ``(Person: string Princ)``,``aso:ASO``,``state:string State``]
      (DISCH 
       ``(M:(Contents,string,string,IClass,unit)Kripke,Oi,Os) sat 
         ((Token quoting (Name "Controller")) says (prop (asoM aso)))``
       (DISCH 
        ``(M:(Contents,string,string,IClass,unit)Kripke,Oi,Os) sat 
	  (K_Auth says (reps Person (Name "Controller") (prop (asoM aso))))``
	(DISCH 
	 ``(M:(Contents,string,string,IClass,unit)Kripke,Oi,Os) sat 
	   (K_Auth says (Token speaks_for Person))``
	 (DISCH 
	  ``(M:(Contents,string,string,IClass,unit)Kripke,Oi,Os) sat 
	    (Auth controls reps Person (Name "Controller") (prop (asoM aso)))``
	  (DISCH 
	   ``(M:(Contents,string,string,IClass,unit)Kripke,Oi,Os) sat 
	     (Auth controls (Token speaks_for Person))``
	   (DISCH 
	   ``(M:(Contents,string,string,IClass,unit)Kripke,Oi,Os) sat 
	     (K_Auth speaks_for Auth)`` th3))))))
	     in
	     save_thm("asoUpdate_rule",th4)
end;

val asaUpdate_rule =
let
 val th1 = 
    UNDISCH_ALL(ISPECL 
    [``(M :(Contents, string, string, IClass, unit) Kripke)``,
     ``Oi:IClass po``,``Os:unit po``,``Token:string Princ``,``Name "Controller"``,
     ``prop (asaM asa):(Contents,string,IClass,unit)Form``,``K_Auth:string Princ``,
     ``Auth:string Princ``,``Person:string Princ``] Cloud_Auth)
 val th2 = SPEC_ALL asaEV2_rule
 val th3 = MP th2 th1
 val th4 = 
 GENL [``(M :(Contents, string, string, IClass, unit) Kripke)``,
       ``(Oi :IClass po)``,``(Os :unit po)``,``(Token:string Princ)``,
       ``(K_Auth:string Princ)``,``(Auth: string Princ)``,
       ``(Person: string Princ)``,``asa:ASA``,``state:string State``]
      (DISCH 
       ``(M:(Contents,string,string,IClass,unit)Kripke,Oi,Os) sat 
         ((Token quoting (Name "Controller")) says (prop (asaM asa)))``
       (DISCH 
        ``(M:(Contents,string,string,IClass,unit)Kripke,Oi,Os) sat 
	  (K_Auth says (reps Person (Name "Controller") (prop (asaM asa))))``
	(DISCH 
	 ``(M:(Contents,string,string,IClass,unit)Kripke,Oi,Os) sat 
	   (K_Auth says (Token speaks_for Person))``
	 (DISCH 
	  ``(M:(Contents,string,string,IClass,unit)Kripke,Oi,Os) sat 
	    (Auth controls reps Person (Name "Controller") (prop (asaM asa)))``
	  (DISCH 
	   ``(M:(Contents,string,string,IClass,unit)Kripke,Oi,Os) sat 
	     (Auth controls (Token speaks_for Person))``
	   (DISCH 
	   ``(M:(Contents,string,string,IClass,unit)Kripke,Oi,Os) sat 
	     (K_Auth speaks_for Auth)`` th3))))))
	     in
	     save_thm("asaUpdate_rule",th4)
end;


val _ = export_theory();

end;