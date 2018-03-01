(******************************************************************************)
(* Solutions for Exercises 17.3.1, 17.3.2, and 17.3.3                         *)
(* Author: Shiu-Kai Chin                                                      *)
(* Date: 1 April 2017                                                         *)
(******************************************************************************)

structure SM0Solutions = struct

(* ====== start interactive ==========
app load ["ssmTheory","SM0Theory","acl_infRules","aclrulesTheory",
          "aclDrulesTheory","satListTheory","listTheory","SM0SolutionsTheory"];

open ssmTheory SM0Theory acl_infRules aclrulesTheory
     aclDrulesTheory satListTheory listTheory SM0SolutionsTheory;
 ======== end interactive ======== *)

open HolKernel Parse boolLib bossLib;
open ssmTheory SM0Theory acl_infRules aclrulesTheory
     aclDrulesTheory satListTheory listTheory

val _ = new_theory "SM0Solutions";


(* -------------------------------------------------------------------------- *)
(* Exercise 17.3.1                                                            *)
(* Alice's non-privileged commands are executed and justified                 *)
(* -------------------------------------------------------------------------- *)
val Alice_npriv_lemma =
let
 val th1 =
 ISPECL
 [``inputOK:(command option, staff,'d,'e)Form -> bool``,
  ``(certs cmd npriv privcmd):(command option, staff,'d,'e)Form list``,
  ``SM0StateInterp:state->(command option, staff,'d,'e)Form``,
  ``[((Name Alice) says (prop (SOME (NP (npriv:npriv))))):
     (command option, staff, 'd, 'e)Form]``,
  ``ins:(command option,staff,'d,'e)Form list list``,
  ``s:state``,``outs:output list``]
 TR_exec_cmd_rule
in
 TAC_PROOF(([],fst(dest_imp(concl th1))),
 REWRITE_TAC[CFGInterpret_def,certs_def,SM0StateInterp_def,satList_CONS,
  	     propCommandList_def,MAP,extractPropCommand_def,
	     satList_nil,sat_TT] THEN
 PROVE_TAC[Controls])
end

val _ = save_thm("Alice_npriv_lemma",Alice_npriv_lemma)

 
val Alice_npriv_lemma2 =
TAC_PROOF(([],
``CFGInterpret ((M:(command option,'b,staff,'d,'e)Kripke),Oi,Os)
  (CFG inputOK SM0StateInterp (certs cmd npriv privcmd)
   ([((Name Alice) says (prop (SOME (NP (npriv:npriv)))))]::ins)
   s (outs:output list)) ==>
  ((M,Oi,Os) sat (prop (SOME(NP npriv))))``),
REWRITE_TAC[CFGInterpret_def,certs_def,SM0StateInterp_def,satList_CONS,
	    satList_nil,sat_TT] THEN
PROVE_TAC[Controls])

val _ = save_thm("Alice_npriv_lemma2",Alice_npriv_lemma2)

val Alice_exec_npriv_justified_thm =
let
 val th1 =
 ISPECL
 [``inputOK:(command option, staff,'d,'e)Form -> bool``,
  ``(certs cmd npriv privcmd):(command option, staff,'d,'e)Form list``,
  ``SM0StateInterp:state->(command option, staff,'d,'e)Form``,
  ``[((Name Alice) says (prop (SOME (NP (npriv:npriv))))):
     (command option, staff, 'd, 'e)Form]``,
  ``ins:(command option,staff,'d,'e)Form list list``,
  ``s:state``,``outs:output list``]
 TR_exec_cmd_rule
 val th2 =
  TAC_PROOF(([],snd(dest_imp(concl th1))),
  PROVE_TAC[th1,Alice_npriv_lemma])
in
 REWRITE_RULE[propCommandList_def,commandList_def,extractPropCommand_def,
	      extractCommand_def,MAP,satList_CONS,satList_nil] th2
end

val _ = save_thm("Alice_exec_npriv_justified_thm",Alice_exec_npriv_justified_thm)

val Alice_npriv_verified_thm =
let
 val (varList,scope) = (strip_forall(concl Alice_exec_npriv_justified_thm))
 val (antecedent,conclusion) = dest_eq scope
 val goal = list_mk_forall
 (varList,(mk_imp(antecedent,snd(dest_conj(snd (dest_conj conclusion))))))
in
TAC_PROOF(([],goal),
 PROVE_TAC[Alice_exec_npriv_justified_thm])
end

val _ = save_thm("Alice_npriv_verified_thm",Alice_npriv_verified_thm)

val Alice_justified_npriv_exec_thm =
let
 val (varList,scope) = strip_forall(concl Alice_exec_npriv_justified_thm)
 val (term1,term2) = dest_eq scope
 val (term3,term4) = dest_conj term2
 val (term5,_) = dest_conj term4
 val term6 = mk_conj(term3,term5)
 val goal = list_mk_forall(varList,mk_imp(term6,term1))
in
 TAC_PROOF(([],goal),
  REWRITE_TAC[Alice_exec_npriv_justified_thm] THEN
  PROVE_TAC[Alice_npriv_lemma2])
end

val _ = save_thm("Alice_justified_npriv_exec_thm",Alice_justified_npriv_exec_thm)



(* -------------------------------------------------------------------------- *)
(* Exercise 17.3.2                                                            *)
(* Bob's privileged commands are trapped                                      *)
(* -------------------------------------------------------------------------- *)
val Bob_privcmd_trap_lemma =
let
 val th1 =
 ISPECL
 [``inputOK:(command option, staff,'d,'e)Form -> bool``,
  ``(certs cmd npriv privcmd):(command option, staff,'d,'e)Form list``,
  ``SM0StateInterp:state->(command option, staff,'d,'e)Form``,
  ``[((Name Bob) says (prop (SOME (PR (privcmd:privcmd))))):
     (command option, staff, 'd, 'e)Form]``,
  ``ins:(command option,staff,'d,'e)Form list list``,
  ``s:state``,``outs:output list``]
 TR_trap_cmd_rule
in
 TAC_PROOF(([],fst(dest_imp(concl th1))),
 REWRITE_TAC[CFGInterpret_def,certs_def,SM0StateInterp_def,satList_CONS,
  	     propCommandList_def,MAP,extractPropCommand_def,
	     satList_nil,sat_TT] THEN
 PROVE_TAC[Modus_Ponens])
end

val _ = save_thm("Bob_privcmd_trap_lemma",Bob_privcmd_trap_lemma)

val Bob_privcmd_trap_lemma2 =
REWRITE_RULE
[satList_CONS,satList_nil, propCommandList_def,MAP,extractPropCommand_def]
Bob_privcmd_trap_lemma

val _ = save_thm("Bob_privcmd_trap_lemma2", Bob_privcmd_trap_lemma2)

val Bob_trap_privcmd_justified_thm =
let
val th1 =
 ISPECL
 [``inputOK:(command option, staff,'d,'e)Form -> bool``,
  ``(certs cmd npriv privcmd):(command option, staff,'d,'e)Form list``,
  ``SM0StateInterp:state->(command option, staff,'d,'e)Form``,
  ``[((Name Bob) says (prop (SOME (PR (privcmd:privcmd))))):
     (command option, staff, 'd, 'e)Form]``,
  ``ins:(command option,staff,'d,'e)Form list list``,
  ``s:state``,``outs:output list``]
 TR_trap_cmd_rule
 val th2 =
 TAC_PROOF(([],snd(dest_imp(concl th1))),
 PROVE_TAC[th1,Bob_privcmd_trap_lemma])
in
 REWRITE_RULE[propCommandList_def,commandList_def,extractPropCommand_def,
	      extractCommand_def,MAP,satList_CONS,satList_nil] th2
end

val _ = save_thm("Bob_trap_privcmd_justified_thm",Bob_trap_privcmd_justified_thm)

val Bob_privcmd_trapped_thm =
let
 val (varList,scope) = (strip_forall(concl Bob_trap_privcmd_justified_thm))
 val (antecedent,conclusion) = dest_eq scope
 val goal = list_mk_forall
 (varList,(mk_imp(antecedent,snd(dest_conj(snd (dest_conj conclusion))))))
in
TAC_PROOF(([],goal),
 PROVE_TAC[Bob_trap_privcmd_justified_thm])
end

val _ = save_thm("Bob_privcmd_trapped_thm",Bob_privcmd_trapped_thm)

val Bob_justified_privcmd_trap_thm =
let
 val (varList,scope) = strip_forall(concl Bob_trap_privcmd_justified_thm)
 val (term1,term2) = dest_eq scope
 val (term3,term4) = dest_conj term2
 val (term5,_) = dest_conj term4
 val term6 = mk_conj(term3,term5)
 val goal = list_mk_forall(varList,mk_imp(term6,term1))
in
 TAC_PROOF(([],goal),
  REWRITE_TAC[Bob_trap_privcmd_justified_thm] THEN
  PROVE_TAC[Bob_privcmd_trap_lemma2])
end

val _ = save_thm("Bob_justified_privcmd_trap_thm",Bob_justified_privcmd_trap_thm)

(* -------------------------------------------------------------------------- *)
(* Exercise 17.3.3A                                                           *)
(* inputOK2 and certs2 defined to authenticate Carol only. Carol is           *)
(* authorized solely on npriv commands, and trapped on privcmd.               *)
(* -------------------------------------------------------------------------- *)
val inputOK2_def =
Define
`(inputOK2
  (((Name Carol) says
   (prop (SOME (cmd:command)))):(command option,staff,'d,'e)Form) = T) /\
 (inputOK2 _ = F)`

val certs2_def =
Define
`certs2(cmd:command)(npriv:npriv)(privcmd:privcmd) =
 [Name Carol controls prop (SOME (NP npriv));
  ((Name Carol) says (prop (SOME (PR privcmd)))) impf (prop NONE)]`

(* -------------------------------------------------------------------------- *)
(* Exercise 17.3.3 B                                                          *)
(* Carol can execute non-privileged commands using inputOK2 and certs2        *)
(* -------------------------------------------------------------------------- *)
val Carol_npriv_lemma =
let
 val th1 =
 ISPECL
 [``inputOK2:(command option, staff,'d,'e)Form -> bool``,
  ``(certs2 cmd npriv privcmd):(command option, staff,'d,'e)Form list``,
  ``SM0StateInterp:state->(command option, staff,'d,'e)Form``,
  ``[((Name Carol) says (prop (SOME (NP (npriv:npriv))))):
     (command option, staff, 'd, 'e)Form]``,
  ``ins:(command option,staff,'d,'e)Form list list``,
  ``s:state``,``outs:output list``]
 TR_exec_cmd_rule
in
 TAC_PROOF(([],fst(dest_imp(concl th1))),
 REWRITE_TAC[CFGInterpret_def,certs2_def,SM0StateInterp_def,satList_CONS,
  	     propCommandList_def,MAP,extractPropCommand_def,
	     satList_nil,sat_TT] THEN
 PROVE_TAC[Controls])
end

val _ = save_thm("Carol_npriv_lemma",Carol_npriv_lemma)

val Carol_npriv_lemma2 =
REWRITE_RULE
[satList_CONS,satList_nil, propCommandList_def,MAP,extractPropCommand_def]
Carol_npriv_lemma

val _ = save_thm("Carol_npriv_lemma2",Carol_npriv_lemma2)

val Carol_exec_npriv_justified_thm =
let
 val th1 =
 ISPECL
 [``inputOK2:(command option, staff,'d,'e)Form -> bool``,
  ``(certs2 cmd npriv privcmd):(command option, staff,'d,'e)Form list``,
  ``SM0StateInterp:state->(command option, staff,'d,'e)Form``,
  ``[((Name Carol) says (prop (SOME (NP (npriv:npriv))))):
     (command option, staff, 'd, 'e)Form]``,
  ``ins:(command option,staff,'d,'e)Form list list``,
  ``s:state``,``outs:output list``]
 TR_exec_cmd_rule
 val th2 =
  TAC_PROOF(([],snd(dest_imp(concl th1))),
  PROVE_TAC[th1,Carol_npriv_lemma])
in
 REWRITE_RULE[propCommandList_def,commandList_def,extractPropCommand_def,
	      extractCommand_def,MAP,satList_CONS,satList_nil] th2
end

val _ = save_thm("Carol_exec_npriv_justified_thm",Carol_exec_npriv_justified_thm)

val Carol_npriv_verified_thm =
let
 val (varList,scope) = (strip_forall(concl Carol_exec_npriv_justified_thm))
 val (antecedent,conclusion) = dest_eq scope
 val goal = list_mk_forall
 (varList,(mk_imp(antecedent,snd(dest_conj(snd (dest_conj conclusion))))))
in
TAC_PROOF(([],goal),
 PROVE_TAC[Carol_exec_npriv_justified_thm])
end

val _ = save_thm("Carol_npriv_verified_thm",Carol_npriv_verified_thm)

val Carol_justified_npriv_exec_thm =
let
 val (varList,scope) = strip_forall(concl Carol_exec_npriv_justified_thm)
 val (term1,term2) = dest_eq scope
 val (term3,term4) = dest_conj term2
 val (term5,_) = dest_conj term4
 val term6 = mk_conj(term3,term5)
 val goal = list_mk_forall(varList,mk_imp(term6,term1))
in
 TAC_PROOF(([],goal),
  REWRITE_TAC[Carol_exec_npriv_justified_thm] THEN
  PROVE_TAC[Carol_npriv_lemma2])
end

val _ = save_thm("Carol_justified_npriv_exec_thm",Carol_justified_npriv_exec_thm)


(* -------------------------------------------------------------------------- *)
(* Exercise 17.3.3 C                                                          *)
(* Carol's request to execute a privileged command is trapped                 *)
(* -------------------------------------------------------------------------- *)
val Carol_privcmd_trap_lemma =
let
 val th1 =
 ISPECL
 [``inputOK2:(command option, staff,'d,'e)Form -> bool``,
  ``(certs2 cmd npriv privcmd):(command option, staff,'d,'e)Form list``,
  ``SM0StateInterp:state->(command option, staff,'d,'e)Form``,
  ``[((Name Carol) says (prop (SOME (PR (privcmd:privcmd))))):
     (command option, staff, 'd, 'e)Form]``,
  ``ins:(command option,staff,'d,'e)Form list list``,
  ``s:state``,``outs:output list``]
 TR_trap_cmd_rule
in
 TAC_PROOF(([],fst(dest_imp(concl th1))),
 REWRITE_TAC[CFGInterpret_def,certs2_def,SM0StateInterp_def,satList_CONS,
  	     propCommandList_def,MAP,extractPropCommand_def,
	     satList_nil,sat_TT] THEN
 PROVE_TAC[Modus_Ponens])
end

val _ = save_thm("Carol_privcmd_trap_lemma",Carol_privcmd_trap_lemma)

val Carol_privcmd_trap_lemma2 =
REWRITE_RULE
[satList_CONS,satList_nil, propCommandList_def,MAP,extractPropCommand_def]
Carol_privcmd_trap_lemma

val _ = save_thm("Carol_privcmd_trap_lemma2", Carol_privcmd_trap_lemma2)

val Carol_trap_privcmd_justified_thm =
let
val th1 =
 ISPECL
 [``inputOK2:(command option, staff,'d,'e)Form -> bool``,
  ``(certs2 cmd npriv privcmd):(command option, staff,'d,'e)Form list``,
  ``SM0StateInterp:state->(command option, staff,'d,'e)Form``,
  ``[((Name Carol) says (prop (SOME (PR (privcmd:privcmd))))):
     (command option, staff, 'd, 'e)Form]``,
  ``ins:(command option,staff,'d,'e)Form list list``,
  ``s:state``,``outs:output list``]
 TR_trap_cmd_rule
 val th2 =
 TAC_PROOF(([],snd(dest_imp(concl th1))),
 PROVE_TAC[th1,Carol_privcmd_trap_lemma])
in
 REWRITE_RULE[propCommandList_def,commandList_def,extractPropCommand_def,
	      extractCommand_def,MAP,satList_CONS,satList_nil] th2
end

val _ = save_thm("Carol_trap_privcmd_justified_thm",Carol_trap_privcmd_justified_thm)

val Carol_privcmd_trapped_thm =
let
 val (varList,scope) = (strip_forall(concl Carol_trap_privcmd_justified_thm))
 val (antecedent,conclusion) = dest_eq scope
 val goal = list_mk_forall
 (varList,(mk_imp(antecedent,snd(dest_conj(snd (dest_conj conclusion))))))
in
TAC_PROOF(([],goal),
 PROVE_TAC[Carol_trap_privcmd_justified_thm])
end

val _ = save_thm("Carol_privcmd_trapped_thm",Carol_privcmd_trapped_thm)

val Carol_justified_privcmd_trap_thm =
let
 val (varList,scope) = strip_forall(concl Carol_trap_privcmd_justified_thm)
 val (term1,term2) = dest_eq scope
 val (term3,term4) = dest_conj term2
 val (term5,_) = dest_conj term4
 val term6 = mk_conj(term3,term5)
 val goal = list_mk_forall(varList,mk_imp(term6,term1))
in
 TAC_PROOF(([],goal),
  REWRITE_TAC[Carol_trap_privcmd_justified_thm] THEN
  PROVE_TAC[Carol_privcmd_trap_lemma2])
end

val _ = save_thm("Carol_justified_privcmd_trap_thm",Carol_justified_privcmd_trap_thm)


(* ==== start solutions ====

 ==== end solutions ==== *)

val _ = export_theory();



end (* structure *)