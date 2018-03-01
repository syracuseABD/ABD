(******************************************************************************)
(* Machine SM0 example                                                        *)
(* Author: Shiu-Kai Chin                                                      *)
(* Date: 30 November 2015                                                     *)
(******************************************************************************)

structure SM0Script = struct


(* interactive mode
app load ["TypeBase","ssmTheory","SM0Theory","acl_infRules","aclrulesTheory",
      	  "aclDrulesTheory","listTheory","SM0Theory"];
open TypeBase ssmTheory acl_infRules aclrulesTheory
     aclDrulesTheory satListTheory listTheory SM0Theory
*)

open HolKernel boolLib Parse bossLib
open TypeBase ssmTheory acl_infRules aclrulesTheory aclDrulesTheory
     satListTheory listTheory

(***********
* create a new theory
***********)

val _ = new_theory "SM0"

(* -------------------------------------------------------------------------- *)
(* Define datatypes for commands and their properties                         *)
(* -------------------------------------------------------------------------- *)
val _ =
Datatype `privcmd = launch | reset`

val privcmd_distinct_clauses = distinct_of``:privcmd``
val _ = save_thm("privcmd_distinct_clauses",privcmd_distinct_clauses)

val _ =
Datatype `npriv = status`

val _ =
Datatype `command = NP npriv | PR privcmd`

val command_distinct_clauses = distinct_of``:command``
val _ = save_thm("command_distinct_clauses",command_distinct_clauses)

val command_one_one = one_one_of``:command``
val _ = save_thm("command_one_one",command_one_one)

(* -------------------------------------------------------------------------- *)
(* Define the states                                                          *)
(* -------------------------------------------------------------------------- *)
val _ =
Datatype`state = STBY | ACTIVE`

val state_distinct_clauses = distinct_of``:state``
val _ = save_thm("state_distinct_clauses",state_distinct_clauses)


(* -------------------------------------------------------------------------- *)
(* Define the outputs                                                         *)
(* -------------------------------------------------------------------------- *)
val _ =
Datatype`output = on | off`

val output_distinct_clauses = distinct_of``:output``
val _ = save_thm("output_distinct_clauses",output_distinct_clauses)

(* -------------------------------------------------------------------------- *)
(* Define next-state function for machine M0                                  *)
(* -------------------------------------------------------------------------- *)
val SM0ns_def =
Define
`(SM0ns STBY (exec [(PR reset)]) = STBY) /\
 (SM0ns STBY (exec [(PR launch)]) = ACTIVE) /\
 (SM0ns STBY (exec [(NP status)]) = STBY) /\
 (SM0ns ACTIVE (exec [(PR reset)]) = STBY) /\
 (SM0ns ACTIVE (exec [(PR launch)]) = ACTIVE) /\
 (SM0ns ACTIVE (exec [(NP status)]) = ACTIVE) /\
 (SM0ns STBY (trap [(PR reset)]) = STBY) /\
 (SM0ns STBY (trap [(PR launch)]) = STBY) /\
 (SM0ns STBY (trap [(NP status)]) = STBY) /\
 (SM0ns ACTIVE (trap [(PR reset)]) = ACTIVE) /\
 (SM0ns ACTIVE (trap [(PR launch)]) = ACTIVE) /\
 (SM0ns ACTIVE (trap [(NP status)]) = ACTIVE) /\
 (SM0ns (s:state) (discard [(cmd:command)]) = s)`

(* -------------------------------------------------------------------------- *)
(* Define next-output function for machine M0                                 *)
(* -------------------------------------------------------------------------- *)
val SM0out_def =
Define
`(SM0out STBY (exec [(PR reset)]) = off) /\
 (SM0out STBY (exec [(PR launch)]) = on) /\
 (SM0out STBY (exec [(NP status)]) = off) /\
 (SM0out ACTIVE (exec [(PR reset)]) = off) /\
 (SM0out ACTIVE (exec [(PR launch)]) = on) /\
 (SM0out ACTIVE (exec [(NP status)]) = on) /\
 (SM0out STBY (trap [(PR reset)]) = off) /\
 (SM0out STBY (trap [(PR launch)]) = off) /\
 (SM0out STBY (trap [(NP status)]) = off) /\
 (SM0out ACTIVE (trap [(PR reset)]) = on) /\
 (SM0out ACTIVE (trap [(PR launch)]) = on) /\
 (SM0out STBY (discard[cmd:command]) = off) /\
 (SM0out ACTIVE (discard[cmd:command]) = on)`
(* -------------------------------------------------------------------------- *)
(* Define datatypes for principles and their properties                       *)
(* -------------------------------------------------------------------------- *)
val _ =
Datatype `staff = Alice | Bob | Carol`

val staff_distinct_clauses = distinct_of``:staff``
val _ = save_thm("staff_distinct_clauses",staff_distinct_clauses)

(* -------------------------------------------------------------------------- *)
(* Input Authentication                                                       *)
(* -------------------------------------------------------------------------- *)
val inputOK_def =
Define
`(inputOK
  (((Name Alice) says
   (prop (SOME (cmd:command)))):(command option,staff,'d,'e)Form) = T) /\
 (inputOK
  (((Name Bob) says
   (prop (SOME (cmd:command)))):(command option,staff,'d,'e)Form) = T) /\
 (inputOK _ = F)`
 

(* -------------------------------------------------------------------------- *)
(* SM0StateInterp                                                             *)
(* -------------------------------------------------------------------------- *)
val SM0StateInterp_def =
Define
`SM0StateInterp (state:state) = (TT:(command option,staff,'d,'e)Form)`

(* -------------------------------------------------------------------------- *)
(* certs definition                                                           *)
(* -------------------------------------------------------------------------- *)
val certs_def =
Define
`certs (cmd:command)(npriv:npriv)(privcmd:privcmd) =
 [(Name Alice controls ((prop (SOME (NP npriv))):(command option, staff,'d,'e)Form));
  Name Alice controls (prop (SOME (PR privcmd)));
  Name Bob controls prop (SOME (NP npriv));
  ((Name Bob) says (prop (SOME (PR privcmd)))) impf (prop NONE)]`

(* -------------------------------------------------------------------------- *)
(* Some theorems showing any message from Carol is rejected                   *)
(* -------------------------------------------------------------------------- *)
val Carol_rejected_lemma =
TAC_PROOF(([],
``~inputOK
   (((Name Carol) says (prop (SOME (cmd:command)))):(command option,staff,'d,'e)Form)``),
PROVE_TAC[inputOK_def])

val _ = save_thm("Carol_rejected_lemma",Carol_rejected_lemma)

val Carol_discard_lemma =
TAC_PROOF(([],
``TR ((M:(command option,'b,staff,'d,'e)Kripke),Oi,Os)
     (discard (commandList [((Name Carol) says (prop (SOME cmd))):
     	       (command option, staff, 'd, 'e)Form]))
  (CFG inputOK SM0StateInterp (certs cmd npriv privcmd)
   ([((Name Carol) says (prop (SOME cmd))):
     	       (command option, staff, 'd, 'e)Form]::ins)
   s (outs:output list))
  (CFG inputOK SM0StateInterp (certs cmd npriv privcmd) ins
  (SM0ns s
   (discard
    (commandList
     [((Name Carol) says (prop (SOME cmd))):
      (command option, staff, 'd, 'e)Form])))
  ((SM0out s (discard (commandList [((Name Carol) says (prop (SOME cmd))):
     	       (command option, staff, 'd, 'e)Form])))::outs))``),
REWRITE_TAC[Carol_rejected_lemma,TR_discard_cmd_rule,authenticationTest_def,
	    MAP,inputOK_def,FOLDR] THEN
CONV_TAC(DEPTH_CONV BETA_CONV) THEN
REWRITE_TAC[])

val _ = save_thm("Carol_discard_lemma",Carol_discard_lemma)


(* -------------------------------------------------------------------------- *)
(* Alice authorized on any privileged command                                 *)
(* -------------------------------------------------------------------------- *)
val Alice_privcmd_lemma =
let
 val th1 =
 ISPECL
 [``inputOK:(command option, staff,'d,'e)Form -> bool``,
  ``(certs cmd npriv privcmd):(command option, staff,'d,'e)Form list``,
  ``SM0StateInterp:state->(command option, staff,'d,'e)Form``,
  ``[((Name Alice) says (prop (SOME (PR (privcmd:privcmd))))):
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

val _ = save_thm("Alice_privcmd_lemma",Alice_privcmd_lemma)

val Alice_privcmd_lemma2 =
REWRITE_RULE
[satList_CONS,satList_nil, propCommandList_def,MAP,extractPropCommand_def]
Alice_privcmd_lemma

val _ = save_thm("Alice_privcmd_lemma2",Alice_privcmd_lemma2)
(* -------------------------------------------------------------------------- *)
(* exec privcmd occurs if and only if Alice's command is authenticated and    *)
(* authorized                                                                 *)
(* -------------------------------------------------------------------------- *)
val Alice_exec_privcmd_justified_thm =
let
 val th1 =
 ISPECL
 [``inputOK:(command option, staff,'d,'e)Form -> bool``,
  ``(certs cmd npriv privcmd):(command option, staff,'d,'e)Form list``,
  ``SM0StateInterp:state->(command option, staff,'d,'e)Form``,
  ``[((Name Alice) says (prop (SOME (PR (privcmd:privcmd))))):
     (command option, staff, 'd, 'e)Form]``,
  ``ins:(command option,staff,'d,'e)Form list list``,
  ``s:state``,``outs:output list``]
 TR_exec_cmd_rule
 val th2 =
  TAC_PROOF(([],snd(dest_imp(concl th1))),
  PROVE_TAC[th1,Alice_privcmd_lemma])
in
 REWRITE_RULE[propCommandList_def,commandList_def,extractPropCommand_def,
	      extractCommand_def,MAP,satList_CONS,satList_nil] th2
end

val _ = save_thm("Alice_exec_privcmd_justified_thm",Alice_exec_privcmd_justified_thm)


(* -------------------------------------------------------------------------- *)
(* If Alice's privileged command was executed, then the request was verified. *)
(* -------------------------------------------------------------------------- *)
val Alice_privcmd_verified_thm =
let
 val (varList,scope) = (strip_forall(concl Alice_exec_privcmd_justified_thm))
 val (antecedent,conclusion) = dest_eq scope
 val goal = list_mk_forall
 (varList,(mk_imp(antecedent,snd(dest_conj(snd (dest_conj conclusion))))))
in
TAC_PROOF(([],goal),
 PROVE_TAC[Alice_exec_privcmd_justified_thm])
end

val _ = save_thm("Alice_privcmd_verified_thm",Alice_privcmd_verified_thm)

(* -------------------------------------------------------------------------- *)
(* If Alice's privileged command was authorized, then the command is executed *)
(* -------------------------------------------------------------------------- *)
val Alice_justified_privcmd_exec_thm =
let
 val (varList,scope) = strip_forall(concl Alice_exec_privcmd_justified_thm)
 val (term1,term2) = dest_eq scope
 val (term3,term4) = dest_conj term2
 val (term5,_) = dest_conj term4
 val term6 = mk_conj(term3,term5)
 val goal = list_mk_forall(varList,mk_imp(term6,term1))
in
 TAC_PROOF(([],goal),
  REWRITE_TAC[Alice_exec_privcmd_justified_thm] THEN
  PROVE_TAC[Alice_privcmd_lemma2])
end

val _ = save_thm("Alice_justified_privcmd_exec_thm",Alice_justified_privcmd_exec_thm)

(* ==== start here ====

 ==== end here ==== *)

val _ = export_theory ()
val _ = print_theory "-"

end (* structure *)