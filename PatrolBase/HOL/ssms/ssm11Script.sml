(******************************************************************************)
(* ssm11 defines the parameterizable state machine for the entire Patrol      *)
(* Base project.  This is a modified form of ssm1 written by Professor        *)
(* Shiu-Kai Chin.                                                             *)
(* Contributors:                                                              *)
(*   Prof. Shiu-Kai Chin (Principal Investigator and original author of ssm1),*)
(*   Lori Pickering (HOL Implementation, modified this to ssm11).             *)
(* Date modified: 16 June 2017                                                *)
(******************************************************************************)
structure ssm11Script = struct

(* ==== Interactive mode ====
app load ["TypeBase", "ssminfRules","listTheory","optionTheory","acl_infRules",
    	  "satListTheory"];
open TypeBase listTheory ssminfRules optionTheory acl_infRules satListTheory
     ssm11Theory
 ==== end interactive mode ==== *)

open HolKernel boolLib Parse bossLib
open TypeBase listTheory optionTheory ssminfRules acl_infRules satListTheory
(***********************)
(* create a new theory *)
(***********************)
val _ = new_theory "ssm11";

(* Define datatypes *)
val _ = 
Datatype
`order = SOME 'command | NONE` (* Specific commands *)
 
val order_distinct_clauses = distinct_of``:'command order``
val _ = save_thm("order_distinct_clauses",order_distinct_clauses)

val order_one_one = one_one_of``:'command order``
val _ = save_thm("order_one_one",order_one_one)

val _ =
Datatype 
`trType = 
  discard 'command | trap 'command | exec 'command` (* Transition commands *)

val trType_distinct_clauses = distinct_of``:'command trType``
val _ = save_thm("trType_distinct_clauses",trType_distinct_clauses)

val trType_one_one = one_one_of``:'command trType``
val _ = save_thm("trType_one_one",trType_one_one)


(* -------------------------------------------------------------------------- *)
(* Define configuration to include the security context within which the      *)
(* inputs are evaluated. The components are as follows: (1) the authentication*)
(* function, (2) the intepretation of the state, (3) the security context,    *)
(* (4) the input stream, (5) the state, and (6) the output stream.            *)
(* Copied from Prof. Chin's ssm1Script.sml                                    *)
(* -------------------------------------------------------------------------- *)
val _ =
Datatype 
`configuration = 
 CFG
  (('command order,'principal,'d,'e)Form -> bool)
  (('state -> ('command order,'principal,'d,'e)Form))
  (('command order,'principal,'d,'e)Form list)
  (('command order,'principal,'d,'e)Form list)
  ('state)
  ('output list)`

val configuration_one_one = 
    one_one_of``:('command order,'d,'e,'output,'principal,'state)configuration``

val _ = save_thm("configuration_one_one",configuration_one_one)

(* -------------------------------------------------------------------------- *)
(* The interpretation of configuration is the conjunction of the formulas in  *)
(* the context and the first element of a non-empty input stream.             *)
(* -------------------------------------------------------------------------- *)
val CFGInterpret_def =
Define
`CFGInterpret
 ((M:('command order,'b,'principal,'d,'e)Kripke),Oi:'d po,Os:'e po)
 (CFG 
  (authenticationTest:('command order,'principal,'d,'e)Form -> bool)
  (stateInterp:'state -> ('command order,'principal,'d,'e)Form)
  (securityContext:('command order,'principal,'d,'e)Form list)
  ((input:('command order,'principal,'d,'e)Form)::ins)
  (state:'state)
  (outputStream:'output list))
 =
  ((M,Oi,Os) satList securityContext) /\
  ((M,Oi,Os) sat input) /\
  ((M,Oi,Os) sat (stateInterp state))`


(* -------------------------------------------------------------------------- *)
(* Define transition relation among configurations. This definition is        *)
(* parameterized in terms of next-state transition function and output        *)
(* function.                                                                  *)
(* The first rule is set up with the expectation it is some principal P       *)
(* ordering a command cmd be executed.                                        *)
(* -------------------------------------------------------------------------- *)
(* This was cut-n-paste from ssm1Script.sml because the code above was not    *)
(* compiling.  This compiles with the appropriate substitutions.              *)
(* -------------------------------------------------------------------------- *)

val (TR_rules, TR_ind, TR_cases) =
Hol_reln
`(!(authenticationTest:('command order,'principal,'d,'e)Form -> bool) (P:'principal Princ)
    (NS: 'state -> 'command trType -> 'state) M Oi Os Out (s:'state)
    (securityContext:('command order,'principal,'d,'e)Form list)
    (stateInterp:'state -> ('command order,'principal,'d,'e)Form)
    (cmd:'command)(ins:('command order,'principal,'d,'e)Form list) 
    (outs:'output list).
 (authenticationTest ((P says (prop (SOME cmd))):('command order,'principal,'d,'e)Form) /\
 (CFGInterpret (M,Oi,Os)
  (CFG authenticationTest stateInterp securityContext
       (((P says (prop (SOME cmd))):('command order,'principal,'d,'e)Form)::ins)
       s outs))) ==>
 (TR 
  ((M:('command order,'b,'principal,'d,'e)Kripke),Oi:'d po,Os:'e po) (exec cmd)
  (CFG authenticationTest stateInterp securityContext
       (((P says (prop (SOME cmd))):('command order,'principal,'d,'e)Form)::ins)
      s outs)
  (CFG authenticationTest stateInterp securityContext ins (NS s (exec cmd))
       ((Out s (exec cmd))::outs)))) /\
 (!(authenticationTest:('command order,'principal,'d,'e)Form -> bool) (P:'principal Princ)
   (NS:'state -> 'command trType -> 'state) M Oi Os Out (s:'state)
   (securityContext:('command order,'principal,'d,'e)Form list)
   (stateInterp:'state -> ('command order,'principal,'d,'e)Form)
   (cmd:'command)(ins:('command order,'principal,'d,'e)Form list) 
   (outs:'output list).
 (authenticationTest ((P says (prop (SOME cmd))):('command order,'principal,'d,'e)Form) /\
 (CFGInterpret (M,Oi,Os)
  (CFG authenticationTest stateInterp securityContext
       (((P says (prop (SOME cmd))):('command order,'principal,'d,'e)Form)::ins)
       s outs))) ==>
 (TR 
  ((M:('command order,'b,'principal,'d,'e)Kripke),Oi:'d po,Os:'e po) (trap cmd)
 (CFG authenticationTest stateInterp securityContext
      (((P says (prop (SOME cmd))):('command order,'principal,'d,'e)Form)::ins)
      s outs)
 (CFG authenticationTest stateInterp securityContext ins (NS s (trap cmd))
      ((Out s (trap cmd))::outs)))) /\
 (!(authenticationTest:('command order,'principal,'d,'e)Form -> bool)
   (NS:'state -> 'command trType -> 'state)
   M Oi Os (Out: 'state -> 'command trType -> 'output) (s:'state)
   (securityContext:('command order,'principal,'d,'e)Form list)
   (stateInterp:'state -> ('command order,'principal,'d,'e)Form)
   (cmd:'command)(x:('command order,'principal,'d,'e)Form)
   (ins:('command order,'principal,'d,'e)Form list) 
   (outs:'output list).
 ~authenticationTest x ==>
 (TR 
  ((M:('command order,'b,'principal,'d,'e)Kripke),Oi:'d po,Os:'e po)
  (discard cmd)
 (CFG authenticationTest stateInterp securityContext
      ((x:('command order,'principal,'d,'e)Form)::ins) s outs)
 (CFG authenticationTest stateInterp securityContext ins (NS s (discard cmd))
      ((Out s (discard cmd))::outs))))`


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
 ``discard cmd = y``
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

(* ---------------------------------------------------------------------------- *)
(* If (CFGInterpret                                                             *)
(*     (M,Oi,Os)                                                                *)
(*     (CFG authenticationTest stateInterpret securityContext                   *)
(*          ((P says (prop (SOME cmd)))::ins) s outs) ==>                       *)
(*    ((M,Oi,Os) sat (prop (SOME cmd))))                                        *)
(* is a valid inference rule, then executing cmd the exec(SOME cmd) transition  *)
(* occurs if and only if prop (SOME cmd), authenticationTest, and               *)
(* CFGInterpret (M,Oi,Os)                                                       *)
(*  (CFG authenticationTest stateInterpret securityContext                      *)
(*                 (P says prop (SOME cmd)::ins) s outs)                        *)
(* are true.                                                                    *)
(* -----------------------------------------------------------------------------*)
val TR_exec_cmd_rule =
TAC_PROOF(([],
``!authenticationTest securityContext stateInterp P cmd ins s outs.
 (!M Oi Os. 
 (CFGInterpret
  ((M :('command order, 'b, 'principal, 'd, 'e) Kripke),(Oi :'d po), (Os :'e po))
  (CFG authenticationTest
       (stateInterp:'state -> ('command order,'principal,'d,'e)Form) securityContext
       (P says (prop (SOME cmd) :('command order, 'principal, 'd, 'e) Form)::ins)
       (s:'state) (outs:'output list)) ==>
  (M,Oi,Os) sat (prop (SOME cmd) :('command order, 'principal, 'd, 'e) Form))) ==>
(!NS Out M Oi Os. 
 TR
  ((M :('command order, 'b, 'principal, 'd, 'e) Kripke),(Oi :'d po),
   (Os :'e po)) (exec (cmd :'command))
  (CFG (authenticationTest :('command order, 'principal, 'd, 'e) Form -> bool)
	   (stateInterp:'state -> ('command order,'principal,'d,'e)Form)
           (securityContext :('command order, 'principal, 'd, 'e) Form list)
           ((P :'principal Princ) says
            (prop (SOME cmd) :('command order, 'principal, 'd, 'e) Form)::
                (ins :('command order, 'principal, 'd, 'e) Form list))
           (s :'state) (outs :'output list))
   (CFG authenticationTest stateInterp securityContext ins
           ((NS :'state -> 'command trType -> 'state) s (exec cmd))
           ((Out :'state -> 'command trType -> 'output) s (exec cmd)::
                outs)) <=>
   authenticationTest
    (P says (prop (SOME cmd) :('command order, 'principal, 'd, 'e) Form)) /\
   (CFGInterpret (M,Oi,Os)
    (CFG
      authenticationTest stateInterp securityContext
      (P says (prop (SOME cmd):('command order, 'principal, 'd, 'e) Form)::ins)
      s outs)) /\
   (M,Oi,Os) sat (prop (SOME cmd) :('command order, 'principal, 'd, 'e) Form))``),
REWRITE_TAC[TRrule0] THEN
REPEAT STRIP_TAC THEN
EQ_TAC THEN
REPEAT STRIP_TAC THEN
PROVE_TAC[])

(* -------------------------------------------------------------------------- *)
(* If (CFGInterpret                                                           *)
(*     (M,Oi,Os)                                                              *)
(*     (CFG authenticationTest stateInterpret securityContext                 *)
(*          ((P says (prop (SOME cmd)))::ins) s outs) ==>                     *)
(*    ((M,Oi,Os) sat (prop TRAP)))                                            *)
(* is a valid inference rule, then executing cmd the exec(SOME cmd) transition*)
(* occurs if and only if prop TRAP, authenticationTest, and                   *)
(* CFGInterpret (M,Oi,Os)                                                     *)
(*  (CFG authenticationTest stateInterpret securityContext                    *)
(*          (P says prop (SOME cmd)::ins) s outs)                             *)
(*  are true.                                                                 *)
(* -------------------------------------------------------------------------- *)
val TR_trap_cmd_rule =
TAC_PROOF(
([],
``!authenticationTest (stateInterp:'state -> ('command order,'principal,'d,'e)Form)
   securityContext P cmd ins (s:'state) (outs:'output list).
  (!M Oi Os.
  CFGInterpret
   ((M :('command order, 'b, 'principal, 'd, 'e) Kripke),(Oi :'d po), (Os :'e po))
   (CFG authenticationTest stateInterp securityContext
        (P says (prop (SOME cmd) :('command order, 'principal, 'd, 'e) Form)::ins)
           s outs) ==>
  (M,Oi,Os) sat (prop NONE :('command order, 'principal, 'd, 'e) Form)) ==>
(!NS Out M Oi Os.
TR
  ((M :('command order, 'b, 'principal, 'd, 'e) Kripke),(Oi :'d po),
   (Os :'e po)) (trap (cmd :'command))
  (CFG (authenticationTest :('command order, 'principal, 'd, 'e) Form -> bool)
     (stateInterp:'state -> ('command order,'principal,'d,'e)Form)
     (securityContext :('command order, 'principal, 'd, 'e) Form list)
     ((P :'principal Princ) says
      (prop (SOME cmd) :('command order, 'principal, 'd, 'e) Form)::
          (ins :('command order, 'principal, 'd, 'e) Form list))
     (s :'state) outs)
  (CFG authenticationTest (stateInterp:'state -> ('command order,'principal,'d,'e)Form)
       securityContext ins
     ((NS :'state -> 'command trType -> 'state) s (trap cmd))
     ((Out :'state -> 'command trType -> 'output) s
        (trap cmd)::outs)) <=>
authenticationTest
  (P says
   (prop (SOME cmd) :('command order, 'principal, 'd, 'e) Form)) /\
CFGInterpret (M,Oi,Os)
  (CFG authenticationTest (stateInterp:'state -> ('command order,'principal,'d,'e)Form)
       securityContext
     (P says
      (prop (SOME cmd) :('command order, 'principal, 'd, 'e) Form)::ins)
     s outs) /\
(M,Oi,Os) sat (prop NONE))``),
REWRITE_TAC[TRrule1] THEN
REPEAT STRIP_TAC THEN
EQ_TAC THEN
REPEAT STRIP_TAC THEN
PROVE_TAC[])


val _ = save_thm("TR_exec_cmd_rule",TR_exec_cmd_rule)

val _ = save_thm("TR_trap_cmd_rule",TR_trap_cmd_rule)


val _ = export_theory ();
val _ = print_theory "-";

end (* structure *)