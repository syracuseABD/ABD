(******************************************************************************)
(* Secure State Machine Theory: authentication, authorization, and state      *)
(* interpretation.                                                            *)
(* Author: Shiu-Kai Chin                                                      *)
(* Date: 27 November 2015                                                     *)
(******************************************************************************)


structure ssmScript = struct

(* ==== Interactive mode ====
app load ["TypeBase", "ssminfRules","listTheory","optionTheory","acl_infRules",
    	  "satListTheory","ssmTheory"];
open TypeBase listTheory ssminfRules optionTheory acl_infRules satListTheory ssmTheory

app load ["TypeBase", "ssminfRules","listTheory","optionTheory","acl_infRules",
    	  "satListTheory"];
open TypeBase listTheory ssminfRules optionTheory acl_infRules satListTheory
     ssmTheory
 ==== end interactive mode ==== *)

open HolKernel boolLib Parse bossLib
open TypeBase listTheory optionTheory ssminfRules acl_infRules satListTheory
(***********************)
(* create a new theory *)
(***********************)
val _ = new_theory "ssm";

(* -------------------------------------------------------------------------- *)
(* Define the type of transition: discard, execute, or trap. We discard from  *)
(* the input stream those inputs that are not of the form P says command. We  *)
(* execute commands that users and supervisors are authorized for. We trap    *)
(* commands that users are not authorized to execute.                         *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* In keeping with virtual machine design principles as described by Popek    *)
(* and Goldberg, we add a TRAP instruction to the commands by users.          *)
(* In effect, we are LIFTING the commands available to users to include the   *)
(* TRAP instruction used by the state machine to handle authorization errors. *)
(* -------------------------------------------------------------------------- *)

val _ =
Datatype 
`trType = 
  discard 'cmdlist | trap 'cmdlist | exec 'cmdlist`

val trType_distinct_clauses = distinct_of``:'cmdlist trType``
val _ = save_thm("trType_distinct_clauses",trType_distinct_clauses)

val trType_one_one = one_one_of``:'cmdlist trType``
val _ = save_thm("trType_one_one",trType_one_one)

(* -------------------------------------------------------------------------- *)
(* Define configuration to include the security context within which the      *)
(* inputs are evaluated. The components are as follows: (1) the authentication*)
(* function, (2) the intepretation of the state, (3) the security context,    *)
(* (4) the input stream, (5) the state, and (6) the output stream.            *)
(* -------------------------------------------------------------------------- *)
val _ =
Datatype 
`configuration = 
 CFG
  (('command option,'principal,'d,'e)Form -> bool)
  (('state -> ('command option,'principal,'d,'e)Form list ->
   ('command option,'principal,'d,'e)Form list))
  ((('command option,'principal,'d,'e)Form list) ->
   (('command option,'principal,'d,'e)Form list))
  (((('command option,'principal,'d,'e)Form) list) list)
  ('state)
  ('output list)`

(* -------------------------------------------------------------------------- *)
(* Prove one-to-one properties of configuration                               *)
(* -------------------------------------------------------------------------- *)
val configuration_one_one = 
    one_one_of``:('command option,'d,'e,'output,'principal,'state)configuration``

val _ = save_thm("configuration_one_one",configuration_one_one)

(* -------------------------------------------------------------------------- *)
(* The interpretation of configuration is the conjunction of the formulas in  *)
(* the context and the first element of a non-empty input stream.             *)
(* -------------------------------------------------------------------------- *)
val CFGInterpret_def =
Define
`CFGInterpret
 ((M:('command option,'b,'principal,'d,'e)Kripke),Oi:'d po,Os:'e po)
 (CFG 
  (elementTest:('command option,'principal,'d,'e)Form -> bool)
  (stateInterp:'state -> (('command option,'principal,'d,'e)Form list) ->
   (('command option,'principal,'d,'e)Form list))
  (context:(('command option,'principal,'d,'e)Form list) ->
   (('command option,'principal,'d,'e)Form list))
  ((x:('command option,'principal,'d,'e)Form list)::ins)
  (state:'state)
  (outStream:'output list))
 =
  ((M,Oi,Os) satList (context x)) /\
  ((M,Oi,Os) satList x) /\
  ((M,Oi,Os) satList (stateInterp state x))`

(******************************************************************************)
(* In the following definitions of authenticationTest, extractCommand, and    *)
(* commandList, we implicitly assume that the only authenticated inputs are   *)
(* of the form P says phi, i.e., we know who is making statement phi.         *)
(******************************************************************************)

val authenticationTest_def =
Define
`authenticationTest
 (elementTest:('command option,'principal,'d,'e)Form -> bool)
 (x:('command option,'principal,'d,'e)Form list) =
 FOLDR (\p q.p /\ q) T (MAP elementTest x)`;

val extractCommand_def =
Define
`extractCommand (P says (prop (SOME cmd)):('command option,'principal,'d,'e)Form) =
   cmd`;

val commandList_def =
Define
`commandList (x:('command option,'principal,'d,'e)Form list) =
 MAP extractCommand x`;

val extractPropCommand_def =
Define
`(extractPropCommand (P says (prop (SOME cmd)):('command option,'principal,'d,'e)Form) =
   ((prop (SOME cmd)):('command option,'principal,'d,'e)Form))`;

val propCommandList_def =
Define
`propCommandList (x:('command option,'principal,'d,'e)Form list) =
 MAP extractPropCommand x`;

val extractInput_def =
Define
`extractInput (P says (prop x):('command option,'principal,'d,'e)Form) = x`;

val inputList_def =
Define
`inputList (xs:('command option,'principal,'d,'e)Form list) =
 MAP extractInput xs`;

(* -------------------------------------------------------------------------- *)
(* Define transition relation among configurations. This definition is        *)
(* parameterized in terms of next-state transition function and output        *)
(* function.                                                                  *)
(* -------------------------------------------------------------------------- *)
val (TR_rules, TR_ind, TR_cases) =
Hol_reln
`(!(elementTest:('command option,'principal,'d,'e)Form -> bool)
    (NS: 'state -> ('command option list) trType -> 'state) M Oi Os Out (s:'state)
    (context:(('command option,'principal,'d,'e)Form list) ->
   (('command option,'principal,'d,'e)Form list))
    (stateInterp:'state -> ('command option,'principal,'d,'e)Form list ->
     ('command option,'principal,'d,'e)Form list)
    (x:('command option,'principal,'d,'e)Form list)
    (ins:('command option,'principal,'d,'e)Form list list) 
    (outs:'output list).
 (authenticationTest elementTest x) /\
 (CFGInterpret (M,Oi,Os)
  (CFG elementTest stateInterp context (x::ins) s outs)) ==>
 (TR 
  ((M:('command option,'b,'principal,'d,'e)Kripke),Oi:'d po,Os:'e po)
  (exec (inputList x))
  (CFG elementTest stateInterp context (x::ins) s outs)
  (CFG elementTest stateInterp context ins
       (NS s (exec (inputList x)))
       ((Out s (exec (inputList x)))::outs)))) /\
 (!(elementTest:('command option,'principal,'d,'e)Form -> bool)
    (NS: 'state -> ('command option list) trType -> 'state) M Oi Os Out (s:'state)
    (context:(('command option,'principal,'d,'e)Form list) ->
   (('command option,'principal,'d,'e)Form list))
    (stateInterp:'state -> ('command option,'principal,'d,'e)Form list ->
     ('command option,'principal,'d,'e)Form list)
    (x:('command option,'principal,'d,'e)Form list)
    (ins:('command option,'principal,'d,'e)Form list list) 
    (outs:'output list).
 (authenticationTest elementTest x)  /\
 (CFGInterpret (M,Oi,Os)
  (CFG elementTest stateInterp context (x::ins) s outs)) ==>
 (TR 
  ((M:('command option,'b,'principal,'d,'e)Kripke),Oi:'d po,Os:'e po)
  (trap (inputList x))
 (CFG elementTest stateInterp context (x::ins) s outs)
 (CFG elementTest stateInterp context ins
      (NS s (trap (inputList x)))
      ((Out s (trap (inputList x)))::outs)))) /\
 (!(elementTest:('command option,'principal,'d,'e)Form -> bool)
    (NS: 'state -> ('command option list) trType -> 'state) M Oi Os Out (s:'state)
    (context:(('command option,'principal,'d,'e)Form list) ->
   (('command option,'principal,'d,'e)Form list))
    (stateInterp:'state -> ('command option,'principal,'d,'e)Form list ->
     ('command option,'principal,'d,'e)Form list)
    (x:('command option,'principal,'d,'e)Form list)
    (ins:('command option,'principal,'d,'e)Form list list) 
    (outs:'output list).
 ~(authenticationTest elementTest x) ==>
 (TR 
  ((M:('command option,'b,'principal,'d,'e)Kripke),Oi:'d po,Os:'e po)
  (discard (inputList x))
 (CFG elementTest stateInterp context (x::ins) s outs)
 (CFG elementTest stateInterp context ins
      (NS s (discard (inputList x)))
      ((Out s (discard (inputList x)))::outs))))`


(* -------------------------------------------------------------------------- *)
(* Split up TR_rules into individual clauses                                  *)
(* -------------------------------------------------------------------------- *)
val [rule0,rule1,rule2] = CONJUNCTS TR_rules

(******************************************************************************)
(* Prove the converse of rule0, rule1, and rule2                              *)
(******************************************************************************)
val TR_lemma0 =
TAC_PROOF(([],flip_TR_rules rule0),
DISCH_TAC THEN
IMP_RES_TAC TR_cases THEN
PAT_ASSUM
 ``exec cmd = y``
 (fn th => ASSUME_TAC(REWRITE_RULE[trType_one_one,trType_distinct_clauses]th)) THEN
PROVE_TAC[configuration_one_one,list_11,trType_distinct_clauses])


val TR_lemma1 =
TAC_PROOF(([],flip_TR_rules rule1),
DISCH_TAC THEN
IMP_RES_TAC TR_cases THEN
PAT_ASSUM
 ``trap cmd = y``
 (fn th => ASSUME_TAC(REWRITE_RULE[trType_one_one,trType_distinct_clauses]th)) THEN
 PROVE_TAC[configuration_one_one,list_11,trType_distinct_clauses])

val TR_lemma2 =
TAC_PROOF(([],flip_TR_rules rule2),
DISCH_TAC THEN
IMP_RES_TAC TR_cases THEN
PAT_ASSUM
 ``discard (inputList x)= y``
 (fn th => ASSUME_TAC(REWRITE_RULE[trType_one_one,trType_distinct_clauses]th)) THEN
PROVE_TAC[configuration_one_one,list_11,trType_distinct_clauses])

val TR_rules_converse =
TAC_PROOF(([],flip_TR_rules TR_rules),
REWRITE_TAC[TR_lemma0, TR_lemma1, TR_lemma2])

val TR_EQ_rules_thm = TR_EQ_rules TR_rules TR_rules_converse 

val _ = save_thm("TR_EQ_rules_thm",TR_EQ_rules_thm)

val [TRrule0,TRrule1,TR_discard_cmd_rule] = CONJUNCTS TR_EQ_rules_thm

val _ = save_thm("TRrule0",TRrule0)
val _ = save_thm("TRrule1",TRrule1)
val _ = save_thm("TR_discard_cmd_rule",TR_discard_cmd_rule)

(* -------------------------------------------------------------------------- *)
(* If (CFGInterpret                                                           *)
(*     (M,Oi,Os)                                                              *)
(*     (CFG elementTest stateInterpret certList                               *)
(*          ((P says (prop (CMD cmd)))::ins) s outs) ==>                      *)
(*    ((M,Oi,Os) sat (prop (CMD cmd))))                                       *)
(* is a valid inference rule, then executing cmd the exec(CMD cmd) transition *)
(* occurs if and only if prop (CMD cmd), elementTest, and                     *)
(* CFGInterpret (M,Oi,Os)                                                     *)
(*  (CFG elementTest stateInterpret certList (P says prop (CMD cmd)::ins) s outs)  *)
(* are true.                                                                  *)
(* -------------------------------------------------------------------------- *)
val TR_exec_cmd_rule =
TAC_PROOF(([],
``!elementTest context stateInterp (x:('command option,'principal,'d,'e)Form list)
   ins s outs.
 (!M Oi Os. 
 (CFGInterpret
  ((M :('command option, 'b, 'principal, 'd, 'e) Kripke),(Oi :'d po), (Os :'e po))
  (CFG elementTest
       (stateInterp:'state -> ('command option,'principal,'d,'e)Form list ->
        ('command option,'principal,'d,'e)Form list) context
       (x::ins)
       (s:'state) (outs:'output list))) ==>
  (M,Oi,Os) satList (propCommandList (x:('command option, 'principal, 'd, 'e)Form list))) ==>
(!NS Out M Oi Os. 
 TR
  ((M :('command option, 'b, 'principal, 'd, 'e) Kripke),(Oi :'d po),
   (Os :'e po)) (exec (inputList x))
  (CFG (elementTest :('command option, 'principal, 'd, 'e) Form -> bool)
	   (stateInterp:'state -> ('command option,'principal,'d,'e)Form list ->
	    ('command option,'principal,'d,'e)Form list)
           (context :('command option, 'principal, 'd, 'e) Form list ->
	    ('command option, 'principal, 'd, 'e) Form list)
           (x::ins)
           (s :'state) (outs :'output list))
   (CFG elementTest stateInterp context ins
           ((NS :'state -> 'command option list trType -> 'state) s (exec (inputList x)))
           (Out s (exec (inputList x))::outs)) <=>
  (authenticationTest elementTest x) /\
  (CFGInterpret (M,Oi,Os)
   (CFG elementTest stateInterp context (x::ins) s outs)) /\
   (M,Oi,Os) satList (propCommandList x))``),
REWRITE_TAC[TRrule0] THEN
REPEAT STRIP_TAC THEN
EQ_TAC THEN
REPEAT STRIP_TAC THEN
PROVE_TAC[])

val _ = save_thm("TR_exec_cmd_rule",TR_exec_cmd_rule)

(* -------------------------------------------------------------------------- *)
(* If (CFGInterpret                                                           *)
(*     (M,Oi,Os)                                                              *)
(*     (CFG elementTest stateInterpret certList                               *)
(*          ((P says (prop (CMD cmd)))::ins) s outs) ==>                      *)
(*    ((M,Oi,Os) sat (prop TRAP)))                                            *)
(* is a valid inference rule, then executing cmd the trap(CMD cmd) transition *)
(* occurs if and only if prop TRAP, elementTest, and                          *)
(* CFGInterpret (M,Oi,Os)                                                     *)
(*  (CFG elementTest stateInterpret certList (P says prop (CMD cmd)::ins)     *)
(*       s outs) are true.                                                    *)
(* -------------------------------------------------------------------------- *)
val TR_trap_cmd_rule =
TAC_PROOF(
([],``!elementTest context stateInterp (x:('command option,'principal,'d,'e)Form list)
   ins s outs.
 (!M Oi Os. 
 (CFGInterpret
  ((M :('command option, 'b, 'principal, 'd, 'e) Kripke),(Oi :'d po), (Os :'e po))
  (CFG elementTest
       (stateInterp:'state -> ('command option,'principal,'d,'e)Form list ->
        ('command option,'principal,'d,'e)Form list) context
       (x::ins)
       (s:'state) (outs:'output list))) ==>
  (M,Oi,Os) sat (prop NONE)) ==>
(!NS Out M Oi Os. 
 TR
  ((M :('command option, 'b, 'principal, 'd, 'e) Kripke),(Oi :'d po),
   (Os :'e po)) (trap (inputList x))
  (CFG (elementTest :('command option, 'principal, 'd, 'e) Form -> bool)
	   (stateInterp:'state -> ('command option,'principal,'d,'e)Form list ->
	    ('command option,'principal,'d,'e)Form list)
           (context :('command option, 'principal, 'd, 'e) Form list ->
	    ('command option, 'principal, 'd, 'e) Form list)
           (x::ins)
           (s :'state) (outs :'output list))
   (CFG elementTest stateInterp context ins
           ((NS :'state -> 'command option list trType -> 'state) s (trap (inputList x)))
           (Out s (trap (inputList x))::outs)) <=>
  (authenticationTest elementTest x) /\
  (CFGInterpret (M,Oi,Os)
   (CFG elementTest stateInterp context (x::ins) s outs)) /\
   (M,Oi,Os) sat (prop NONE))``),
REWRITE_TAC[TRrule1] THEN
REPEAT STRIP_TAC THEN
EQ_TAC THEN
REPEAT STRIP_TAC THEN
PROVE_TAC[])

val _ = save_thm("TR_trap_cmd_rule",TR_trap_cmd_rule)

(* ==== start here ====
==== end here ==== *)

val _ = export_theory ();
val _ = print_theory "-";

end (* structure *)