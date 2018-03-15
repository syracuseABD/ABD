(**********************************************)
(* Simplified instruction set architecture    *)
(* Author: S-K Chin                           *)
(* Date: 15 January 2013                      *)
(**********************************************)

structure isa1Script = struct

(*  interactive mode
app load ["TypeBase","arithmeticTheory","isainfRules"];
*)
open HolKernel boolLib Parse bossLib
open TypeBase arithmeticTheory isainfRules
(***********
* create a new theory
***********)
val _ = new_theory "isa1";

(********************************************)
(* Memory Address from the user's viewpoint *)
(* Later these will be virtual addresses.   *)
(********************************************)
(*
val _ = Hol_datatype `memAddress = ma of num`;
val memAddress_one_one = one_one_of``:memAddress``
val _ = save_thm("memAddress_one_one",memAddress_one_one)
*)

(*
val _ = type_abbrev("memAddress",``:num``)
*)
(********************************************)
(* Classify instructions based on their use *)
(* of memory                                *)
(********************************************)

(******************)
(* no memory used *)
(******************)
val _ =
Hol_datatype
`inst0 = CLA | SKZ | HLT`
val inst0_distinct_clauses = distinct_clauses``:inst0``
val _ = save_thm("inst0_distinct_clauses",inst0_distinct_clauses)


(**************************)
(* 1 memory location used *)
(**************************)
val _ = 
Hol_datatype
`inst1 = LDA of num | STO of num | ADD of num | JMP of num`
val inst1_one_one = one_one_of``:inst1``
val _ = save_thm("inst1_one_one",inst1_one_one)
val inst1_distinct_clauses = distinct_clauses``:inst1``
val _ = save_thm("inst1_distinct_clauses",inst1_distinct_clauses)

(* No need to do this
(**********************************)
(* Combine into a single datatype *)
(**********************************)
val _ = 
Hol_datatype 
`inst = Inst0 of inst0 | Inst1 of inst1`
val inst_one_one = one_one_of``:inst``
val _ = save_thm("inst_one_one",inst_one_one)
val inst_distinct_clauses = distinct_clauses``:inst``
val _ = save_thm("inst_distinct_clauses",inst_distinct_clauses)
*)


(* FOR NOW WE IGNORE LABELS *)
(**************************************************************)
(* We have operation labels corresponding to each instruction *)
(* These labels are used as part of the transition rules and  *)
(* support the biconditional relation between configurations  *)
(* and instructions.                                          *)
(**************************************************************)
(*
val _ = 
Hol_datatype `oplabel = cla | hlt | lda | sto | add | jmp`;

val oplabel_distinct_clauses = distinct_clauses``:oplabel``

val _ = save_thm("oplabel_distinct_clauses",oplabel_distinct_clauses)
*)

(****************************************)
(* Memory Values                        *)
(* the kinds of values stored in memory *)
(* all from the user's perspective      *)
(****************************************)
val _ = 
 Hol_datatype
 `memVal = 
  Data of num | Inst0 of inst0 | Inst1 of inst1 | MA of num | unknown`
val memVal_one_one = one_one_of``:memVal``
val _ = save_thm("memVal_one_one",memVal_one_one)
val memVal_distinct_clauses = distinct_clauses``:memVal``
val _ = save_thm("memVal_distinct_clauses",memVal_distinct_clauses)

(****************************************************)
(* User memory is an abstraction of physical memory *)
(* with no physical limit. User memory is a store   *)
(* or environment mapping numes to memVals   *)
(****************************************************)
(*
val _ = Hol_datatype`uMem = UMem of (num -> memVal)`;
val uMem_one_one = one_one_of``:uMem``
val _ = save_thm("uMem_one_one",uMem_one_one)
*)

val _ = type_abbrev("store",``:num -> memVal``)

(**************************************)
(* We model memory using environments *)
(* where f:physicalAddress -> memval  *)
(**************************************)
val unknownStore_def = 
Define`unknownStore = \(addr:num).unknown`;

(* a polymorphic version of update             *)
(* to support different kinds of memory values *)
val update_def = 
Define
`update address value (f:num -> 'memValue) 
 = (\addr. if addr = address then value else f addr)`;

(********************************************)
(* Virtual Machine registers are ACC and PC *)
(********************************************)
val _ = Hol_datatype`procStatusWord = psw of num => num`;
val procStatusWord_one_one = one_one_of``:procStatusWord``
val _ = save_thm("procStatusWord_one_one",procStatusWord_one_one)


(*************************************************************)
(* Processor configuration is the vm status with user memory *)
(*************************************************************)
val _ = Hol_datatype`config1 = CFG1 of procStatusWord => store`
val config1_one_one = one_one_of``:config1``
val _ = save_thm("config1_one_one",config1_one_one)


(*********************************************************)
(* The transition rule defining the semantics of the isa *)
(*********************************************************)
val (ISA_rules, ISA_ind, ISA_cases) =
Hol_reln
`(******************************)
 (* cla: clear the accumulator *)
 (******************************)
 (((userMem (pc:num)) = (Inst0 CLA)) ==> (ISA ((Inst0 CLA)) (CFG1(psw acc pc)(userMem:store)) (CFG1(psw 0 (pc + 1))(userMem:store)))) /\
 (*****************************************)
 (* skz: skip next instruction of acc = 0 *)
 (*****************************************)
 (((userMem (pc:num)) = (Inst0 SKZ)) ==> (ISA ((Inst0 SKZ)) 
                                            (CFG1(psw acc pc)(userMem:store)) 
                                            (CFG1(psw acc (if acc = 0 then (pc + 2) else (pc + 1)))(userMem:store)))) /\
 (***********************)
 (* hlt: halt execution *)
 (***********************)
 (((userMem (pc:num)) = (Inst0 HLT)) ==> (ISA ((Inst0 HLT)) (CFG1(psw acc pc)(userMem:store)) (CFG1(psw acc pc)(userMem:store)))) /\
 (*************************************)
 (* lda: load accumulator from memory *)
 (*************************************)
 ((((userMem (pc:num)) = (Inst1 (LDA (address:num)))) /\ (userMem(address:num) = Data data)) ==> 
  (ISA ((Inst1 (LDA (address:num)))) (CFG1(psw acc pc)(userMem:store)) (CFG1(psw data (pc + 1))(userMem:store)))) /\
 (************************************)
 (* sto: store accumulator to memory *)
 (************************************)
 (((userMem (pc:num)) = (Inst1 (STO (address:num)))) ==> 
  (ISA ((Inst1 (STO (address:num)))) (CFG1(psw acc pc)(userMem:store)) (CFG1(psw acc (pc + 1))(update(address:num)(Data acc)(userMem:store))))) /\
 (*********************************************)
 (* add: add accumulator with value in memory *)
 (*********************************************)
 ((((userMem (pc:num)) = (Inst1 (ADD (address:num)))) /\ (userMem(address:num) = Data data)) ==> 
  (ISA ((Inst1 (ADD (address:num)))) (CFG1(psw acc pc)(userMem:store)) (CFG1(psw (acc + data) (pc + 1))(userMem:store)))) /\
 (*****************************************)
 (* jmp: set pc to value stored in memory *)
 (*****************************************)
 (((userMem (pc:num)) = (Inst1 (JMP (address:num)))) ==> 
  (ISA ((Inst1 (JMP (address:num)))) (CFG1(psw acc pc)(userMem:store)) (CFG1(psw acc address)(userMem:store))))`

val config1_one_one_clauses =
TAC_PROOF
(([],
 ``(CFG1(psw acc pc) store = CFG1(psw acc' pc') store') ==> 
   ((acc = acc') /\ (pc = pc') /\ (store = store'))``),
PROVE_TAC[config1_one_one,procStatusWord_one_one])

val _ = save_thm("config1_one_one_clauses",config1_one_one_clauses)

val add_lemma =
TAC_PROOF(
([],
 ``!x x' y y'.(x = x') ==> (x + y = x' + y') ==> (y = y')``),
PROVE_TAC[EQ_ADD_LCANCEL])

val ISA_rules_converse_lemma =
TAC_PROOF(
([],flip_TR_rules ISA_rules),
REPEAT STRIP_TAC THEN
IMP_RES_TAC ISA_cases THEN
IMP_RES_TAC config1_one_one_clauses THEN
(* remove all instances of x = x in assumptions *)
REPEAT (PAT_ASSUM``x=x``(fn th => ALL_TAC)) THEN
(* eliminate most of the subgoals *)
ASM_REWRITE_TAC [] THEN
(* use memVal_one_one to set up distinctiveness clauses *)
IMP_RES_TAC memVal_one_one THEN
(* utilize Inst0 <> Inst1 *)
IMP_RES_TAC memVal_distinct_clauses THEN
(* use inst1_distinctiveness_clauses to eliminate inequalities *)
IMP_RES_TAC inst1_distinct_clauses THEN
(* use inst1_one_one to set up memory address equality *)
IMP_RES_TAC inst1_one_one THEN
(* finish off add by using one to one property of add *)
PROVE_TAC [add_lemma])

val ISA_EQ_rules =
TR_EQ_rules ISA_rules ISA_rules_converse_lemma
val _ = save_thm("ISA_EQ_rules",ISA_EQ_rules)

val _ = export_theory ();
val _ = print_theory "-";

end (* structure *)