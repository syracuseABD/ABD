(**********************************************)
(* Simplified reference monitor for isa1      *)
(* Author: S-K Chin                           *)
(* Date: 20 January 2013                      *)
(**********************************************)

structure rm1Script = struct

(*  interactive mode
app load ["TypeBase","arithmeticTheory","stringTheory","isa1Theory","isainfRules"];
*)
open HolKernel boolLib Parse bossLib
open TypeBase arithmeticTheory stringTheory isa1Theory isainfRules
(***********
* create a new theory
***********)
val _ = new_theory "rm1";

(*******************************)
(* We have two operating modes *)
(*******************************)
val _ = Hol_datatype `mode = User | Supervisor`

val mode_distinct_clauses = distinct_clauses``:mode``

val _ = save_thm("mode_distinct_clauses",mode_distinct_clauses)

(**************)
(* addressing *)
(**************)
(**************************************************************)
(* The addressing scheme used is that of MULTICS (MULTiplexed *)
(* Information and Computing Service. See Daley and Dennis,   *)
(* Virtual Memory, Processes, and Sharing in MULTICS, CACM,   *)
(* Vol. 11, No. 5, May 1968, pp. 306-312.                     *)
(**************************************************************)
(************************************************************)
(* General addresses consist of a segment number and a word *)
(* number.  In isa1Theory, num is the word number.          *)
(************************************************************)
(***************************************************************)
(* Process isolation is achieved by assigning each process its *)
(* own memory segment Si. For simplicity, we assume infinite   *)
(* memory address locations.                                   *)
(***************************************************************)

(***********************************************************)
(* Conceptually, addresses have two parts: a segment index *)
(* identifying which segment to address, and a memory      *)
(* address within the memory segment.                      *)
(* User processes are unaware of which memory segment they *)
(* are using.                                              *)
(***********************************************************)

(***********************************************************)
(* Labels for each instruction we will use for instruction *)
(* traps                                                   *)
(***********************************************************)
val _ = 
Hol_datatype
`oplabel = cla | skz | hlt | lda | sto | add | jmp | trap | sum | ssm | ldpbr | stpbr`
val oplabel_distinct_clauses = distinct_clauses``:oplabel``
val _ = save_thm("oplabel_distinct_clauses",oplabel_distinct_clauses)

(***********************)
(* Segment designators *)
(***********************)
val _ =
Hol_datatype
`segment = segNum of string | Trap of oplabel => num`
val segment_one_one = one_one_of``:segment``
val _ = save_thm("segment_one_one",segment_one_one)
val segment_distinct_clauses = distinct_clauses``:segment``
val _ = save_thm("segment_distinct_clauses",segment_distinct_clauses)

(****************)
(* Instructions *)
(****************)
(****************************************)
(* We have privileged instructions      *)
(* which affect the state and registers *)
(* of the virtual machine reference     *)
(* monitor. We classify them based on   *)
(* their use of memory addresses.       *)
(****************************************)
val _ = Hol_datatype `pinst0 = TRAP | SUM | SSM`
val pinst0_distinct_clauses = distinct_clauses``:pinst0``
val _ = save_thm("pinst0_distinct_clauses",pinst0_distinct_clauses)

(***************************************************************)
(* Note: PBR below refers to procedure base register, the name *)
(* of the register holding the segment number in MULTICS       *)
(***************************************************************)
val _ = Hol_datatype `pinst1 = LDPBR of segment => num | STPBR of segment => num`
val pinst1_one_one = one_one_of``:pinst1``
val _ = save_thm("pinst1_one_one",pinst1_one_one)

val pinst1_distinct_clauses = distinct_clauses``:pinst1``
val _ = save_thm("pinst1_distinct_clauses",pinst1_distinct_clauses)

(*************************************************************)
(* We gather all instructions together so we can include the *)
(* instruction being executed as part of the virtual machine *)
(* configuration.                                            *)
(*************************************************************)
val _ = 
Hol_datatype
`instructions = IN0 of inst0 | IN1 of inst1 | IP0 of pinst0 | IP1 of pinst1`
val instructions_one_one = one_one_of``:instructions``
val _ = save_thm("instructions_one_one",instructions_one_one)
val instructions_distinct_clauses = distinct_clauses``:instructions``
val _ = save_thm("instructions_distinct_clauses",instructions_distinct_clauses)

(********************************************************************)
(* The virtual machine consists of a processor - as seen by users - *)
(* augmented with its operating mode and segment number.            *)
(********************************************************************)
val _ = Hol_datatype`vmStatusWord = vmsw of mode => segment => procStatusWord`
val vmStatusWord_one_one = one_one_of``:vmStatusWord``
val _ = save_thm("vmStatusWord_one_one",vmStatusWord_one_one)

(*************************************************************)
(* Memory for the virtual machine is segmented memory, i.e., *)
(* a collection of memory segments                           *)
(*************************************************************)
(****************************************************)
(* figure out memory values for segmented memory    *)
(* Preserve user view and augment with other values *)
(****************************************************)
val _ = 
Hol_datatype
`segMemVal = 
 Num of num | NP0 of inst0 | NP1 of inst1 | WI of num | PI0 of pinst0 | 
 PI1 of pinst1 | VMSW of vmStatusWord | SEG of segment | dontknow`
val segMemVal_one_one = one_one_of``:segMemVal``
val _ = save_thm("segMemVal_one_one",segMemVal_one_one)
val segMemVal_distinct_clauses = distinct_clauses``:segMemVal``
val _ = save_thm("segMemVal_distinct_clauses",segMemVal_distinct_clauses)

(* virtual machine memories store segMemVals, so we need *)
(* the appropriate type signature for memory segments    *)
val _ = type_abbrev("vmstore",``:num -> segMemVal``)

(* Getting from genAddress to segMemVals *)
(* Done using descriptor segments which  *)
(* return a store given a segment number *)
(* We introduce a type abbreviation for  *)
(* segment maps.                         *)

(* segMaps take a segment number and return a *)
(* store                                      *)
val _ = type_abbrev("segMap",``:segment -> vmstore``)

(***********************************)
(* Updating the descriptor segment *)
(***********************************)
val updateGM_def =
Define
`updateGM segment address value (genMem:segMap)
 = (\seg addr. if (seg = segment) /\ (addr = address) then value else (genMem seg addr))`

val updateDS_def =
Define
`updateDS segment VMStore segmentMap
 = (\seg.if seg = (segment:segment) then (VMStore:vmstore) else ((segmentMap:segMap)seg))`

(* Virtual machine and virtual machine monitor configuration *)
val _ =
Hol_datatype
`config2 = CFG2 of instructions => vmStatusWord => segMap`
val config2_one_one = one_one_of``:config2``
val _ = save_thm("config2_one_one",config2_one_one)

(* Proof of config2_one_one_clauses *)
val config2_one_one_clauses =
TAC_PROOF(
([],
 ``(CFG2 inst (vmsw mode segNumber (psw acc pc)) genMem = CFG2 inst' (vmsw mode' segNumber' (psw acc' pc')) genMem') ==>
   ((inst = inst') /\ (mode = mode') /\ (segNumber = segNumber') /\ (acc = acc') /\ (pc = pc') /\ (genMem = genMem'))``),
PROVE_TAC[config2_one_one,vmStatusWord_one_one,procStatusWord_one_one])

val _ = save_thm("config2_one_one_clauses",config2_one_one_clauses)

(* Transition rules *)
val (RM1_rules, RM1_ind, RM1_cases) =
Hol_reln
`(******************************)
 (* cla: clear the accumulator *)
 (******************************)
 (((((genMem:segMap) (seg:segment))(pc:num)) = (NP0 CLA)) ==> (RM1 ((IN0 CLA)) (CFG2 inst (vmsw mode seg (psw acc pc))(genMem:segMap)) (CFG2(IN0 CLA)(vmsw mode seg (psw 0 (pc + 1)))(genMem:segMap)))) /\
 (*****************************************)
 (* skz: skip next instruction of acc = 0 *)
 (*****************************************)
 ((((genMem:segMap) seg (pc:num)) = (NP0 SKZ)) ==> 
 (RM1 (IN0 SKZ) 
  (CFG2 inst (vmsw mode seg (psw acc pc))(genMem:segMap))
  (CFG2(IN0 SKZ)(vmsw mode seg (psw acc (if acc = 0 then (pc + 2) else (pc + 1))))(genMem:segMap))))  /\
 (***********************)
 (* hlt: halt execution *)
 (***********************)
 ((((genMem:segMap) seg (pc:num)) = (NP0 HLT)) ==> (RM1 ((IN0 HLT)) (CFG2 inst (vmsw mode seg (psw acc pc))(genMem:segMap)) (CFG2(IN0 HLT)(vmsw mode seg (psw acc pc))(genMem:segMap))))  /\
 (*************************************)
 (* lda: load accumulator from memory *)
 (*************************************)
 (((((genMem:segMap) seg (pc:num)) = (NP1 (LDA (address:num)))) /\ (genMem seg (address:num) = Num data)) ==> 
  (RM1 ((IN1 (LDA (address:num)))) (CFG2 inst (vmsw mode seg (psw acc pc))(genMem:segMap)) (CFG2(IN1 (LDA address))(vmsw mode seg (psw data (pc + 1)))(genMem:segMap)))) /\
 (************************************)
 (* sto: store accumulator to memory *)
 (************************************)
 ((((genMem:segMap) seg (pc:num)) = (NP1 (STO (address:num)))) ==> 
  (RM1 ((IN1 (STO (address:num)))) (CFG2 inst (vmsw mode seg(psw acc pc))(genMem:segMap)) (CFG2 (IN1 (STO address)) (vmsw mode seg (psw acc (pc + 1)))(updateGM seg address (Num acc)(genMem:segMap))))) /\
 (*********************************************)
 (* add: add accumulator with value in memory *)
 (*********************************************)
 (((((genMem:segMap) seg (pc:num)) = (NP1 (ADD (address:num)))) /\ (genMem seg address = Num data)) ==> 
  (RM1 ((IN1 (ADD (address:num)))) (CFG2 inst (vmsw mode seg (psw acc pc))(genMem:segMap)) (CFG2(IN1 (ADD address))(vmsw  mode seg (psw (acc + data) (pc + 1)))(genMem:segMap)))) /\
 (*****************************************)
 (* jmp: set pc to value stored in memory *)
 (*****************************************)
 ((((genMem:segMap) seg (pc:num)) = (NP1 (JMP (address:num)))) ==> 
  (RM1 ((IN1 (JMP (address:num)))) (CFG2 inst (vmsw mode seg (psw acc pc))(genMem:segMap)) (CFG2(IN1 (JMP address))(vmsw mode seg (psw acc address))(genMem:segMap)))) /\
(*********************************************)
 (* trap: assume segment 0 is the supervisory *)
 (* segment, the vmStatusWord is stored in    *)
 (* general address (0,0), and the new        *)
 (* vmStatusWord is fetched from (0,1).       *)
 (*********************************************)
 (((((genMem:segMap) seg (pc:num)) = (PI0 TRAP)) /\
   ((genMem (Trap trap 0) 1) = (VMSW (vmsw trapMode (Trap trap 1) (psw trapACC trapPC)))))
   	    ==> 
  (RM1 (IP0 TRAP) (CFG2 inst (vmsw mode seg(psw acc pc))(genMem:segMap)) (CFG2(IP0 TRAP)(vmsw trapMode (Trap trap 1) (psw trapACC trapPC))(updateGM (Trap trap 0) 0 (VMSW (vmsw mode seg(psw acc pc)))(genMem:segMap))))) /\
 (*******************************************************)
 (* sum: if in Supervisor mode, execute, otherwise trap *)
 (*******************************************************)
 (* sum in user mode: trap *)
 (**************************)
 (((((genMem:segMap) seg (pc:num)) = (PI0 SUM)) /\
   ((genMem (Trap sum 0) 1) = (VMSW (vmsw trapMode (Trap sum 1) (psw trapACC trapPC)))))
   	    ==> 
  (RM1 (IP0 SUM) (CFG2 inst (vmsw User seg(psw acc pc))(genMem:segMap)) (CFG2(IP0 SUM)(vmsw trapMode (Trap sum 0) (psw trapACC trapPC))(updateGM (Trap sum 0) 0 (VMSW (vmsw User seg(psw acc pc)))(genMem:segMap))))) /\ 
 (***********************************)
 (* sum in supervisor mode: execute *)
 (***********************************)
 ((((genMem:segMap) seg (pc:num)) = (PI0 SUM))
   	    ==> 
  (RM1 (IP0 SUM) (CFG2 inst (vmsw Supervisor seg(psw acc pc))(genMem:segMap)) (CFG2(IP0 SUM)(vmsw User seg (psw acc (pc + 1)))(genMem:segMap)))) /\
 (*******************************************************)
 (* ssm: if in Supervisor mode, execute, otherwise trap *)
 (*******************************************************)
 (* ssm in user mode: trap *)
 (**************************)
 (((((genMem:segMap) seg (pc:num)) = (PI0 SSM)) /\
   ((genMem (Trap ssm 0) 1) = (VMSW (vmsw trapMode (Trap ssm 1) (psw trapACC trapPC)))))
   	    ==> 
  (RM1 (IP0 SSM) (CFG2 inst (vmsw User seg(psw acc pc))(genMem:segMap)) (CFG2(IP0 SSM)(vmsw trapMode (Trap ssm 1) (psw trapACC trapPC))(updateGM (Trap ssm 0) 0 (VMSW (vmsw User seg(psw acc pc)))(genMem:segMap))))) /\
 (***********************************)
 (* ssm in supervisor mode: execute *)
 (***********************************)
 ((((genMem:segMap) seg (pc:num)) = (PI0 SSM))
   	    ==> 
  (RM1 (IP0 SSM) (CFG2 inst (vmsw Supervisor seg(psw acc pc))(genMem:segMap)) (CFG2(IP0 SSM)(vmsw Supervisor seg (psw acc (pc + 1)))(genMem:segMap)))) /\
 (****************************)
 (* ldpbr in user mode: trap *)
 (****************************)
 (((((genMem1:segMap) seg1 (pc1:num)) = (PI1 (LDPBR segID1 index1))) /\
   ((genMem1 (Trap ldpbr 0) 1) = (VMSW (vmsw trapMode1 (Trap ldpbr 1) (psw trapACC1 trapPC1)))))
   	    ==> 
  (RM1 (IP1 (LDPBR segID1 index1)) (CFG2 inst (vmsw User seg1(psw acc1 pc1))(genMem1:segMap)) (CFG2(IP1 (LDPBR segID1 index1))(vmsw trapMode1 (Trap ldpbr 1) (psw trapACC1 trapPC1))(updateGM (Trap ldpbr 0) 0 (VMSW (vmsw User seg1(psw acc1 pc1)))(genMem1:segMap))))) /\
 (****************************)
 (* ldpbr in supervisor mode *)
 (* if address contains a    *)
 (* segment number execute   *)
 (****************************)
 (((((genMem2:segMap) seg2 (pc2:num)) = (PI1 (LDPBR segID2 index2))) /\
   (genMem2 segID2 index2 = SEG newSegID2))
   	    ==> 
  (RM1 (IP1 (LDPBR segID2 index2)) (CFG2 inst (vmsw Supervisor seg2(psw acc2 pc2))(genMem2:segMap)) (CFG2(IP1 (LDPBR segID2 index2))(vmsw Supervisor newSegID2 (psw acc2 (pc2 + 1)))(genMem2:segMap)))) /\

 (****************************)
 (* ldpbr in supervisor mode *)
 (* if address does not have *)
 (* a segment number trap    *)
 (****************************)
 (((((genMem3:segMap) seg3 (pc3:num)) = (PI1 (LDPBR segID3 index3))) /\
   (!newSegID3.~(genMem3 segID3 index3 = SEG newSegID3)) /\
   ((genMem3 (Trap ldpbr 1) 1) = (VMSW (vmsw trapMode3 (Trap ldpbr 2) (psw trapACC3 trapPC3)))))
   	    ==> 
  (RM1 (IP1 (LDPBR segID3 index3)) (CFG2 inst (vmsw Supervisor seg3(psw acc3 pc3))(genMem3:segMap)) (CFG2(IP1 (LDPBR segID3 index3))(vmsw trapMode3 (Trap ldpbr 2) (psw trapACC3 trapPC3))(updateGM (Trap ldpbr 1) 0 (VMSW (vmsw  Supervisor seg3(psw acc3 pc3)))(genMem3:segMap))))) /\
(* === start here === *)
 (****************************)
 (* stpbr in user mode: trap *)
 (****************************)
 (((((genMem:segMap) seg (pc:num)) = (PI1 (STPBR segID index))) /\
   ((genMem (Trap stpbr 0) 1) = (VMSW (vmsw trapMode (Trap stpbr 1) (psw trapACC trapPC)))))
   	    ==> 
  (RM1 (IP1 (STPBR segID index)) (CFG2 inst (vmsw User seg (psw acc pc))(genMem:segMap)) (CFG2(IP1 (STPBR segID index))(vmsw trapMode (Trap stpbr 1) (psw trapACC trapPC))(updateGM (Trap stpbr 1) 0 (VMSW (vmsw User seg (psw acc pc)))(genMem:segMap))))) /\
 (****************************)
 (* stpbr in supervisor mode *)
 (****************************)
 ((((genMem:segMap) seg (pc:num)) = (PI1 (STPBR segID index)))
   	    ==> 
  (RM1 (IP1 (STPBR  segID index)) (CFG2 inst (vmsw Supervisor seg (psw acc pc))(genMem:segMap)) (CFG2(IP1 (STPBR segID index))(vmsw Supervisor seg (psw acc (pc + 1)))(updateGM segID index (SEG seg)(genMem:segMap)))))`


(* Proof of converse of RM1_rules *)
(* 

val add_lemma =
TAC_PROOF(
([],
 ``!x x' y y'.(x = x') ==> (x + y = x' + y') ==> (y = y')``),
PROVE_TAC[EQ_ADD_LCANCEL])

(* goal proved for RM1 defined without address trapping LDPBR *)

set_goal([],flip_TR_rules RM1_rules)
REPEAT STRIP_TAC THEN
IMP_RES_TAC RM1_cases THEN
IMP_RES_TAC config2_one_one_clauses THEN
(* remove all instances of x = x in assumptions *)
REPEAT (PAT_ASSUM``x=x``(fn th => ALL_TAC)) THEN
(* eliminate most of the subgoals *)
ASM_REWRITE_TAC [] THEN
(* use instructions_one_one to set up distinctiveness clauses *)
IMP_RES_TAC instructions_one_one THEN
(* utilize instructions_distinct_clauses *)
IMP_RES_TAC instructions_distinct_clauses THEN
(* use segMemVal_one_one to set up distinctiveness clauses *)
IMP_RES_TAC segMemVal_one_one THEN
(* utilize Inst0 <> Inst1 *)
IMP_RES_TAC segMemVal_distinct_clauses THEN
(* use inst1_distinctiveness_clauses to eliminate inequalities *)
IMP_RES_TAC inst1_distinct_clauses THEN
(* use inst1_one_one to set up memory address equality *)
IMP_RES_TAC inst1_one_one THEN
IMP_RES_TAC mode_distinct_clauses THEN
IMP_RES_TAC pinst1_one_one THEN
IMP_RES_TAC pinst1_distinct_clauses THEN
IMP_RES_TAC pinst0_distinct_clauses THEN
ASM_REWRITE_TAC[] THENL
(* finish off add by using one to one property of add *)
[PROVE_TAC [add_lemma],ALL_TAC,ALL_TAC,ALL_TAC,ALL_TAC] THEN

REPEAT (PAT_ASSUM``STPBR a b = STPBR c d``(fn th => ALL_TAC)) THEN
REPEAT (PAT_ASSUM``LDPBR a b = LDPBR c d``(fn th => ALL_TAC)) THEN
REPEAT (PAT_ASSUM``JMP a = JMP b``(fn th => ALL_TAC)) THEN
REPEAT (PAT_ASSUM``ADD a = ADD b``(fn th => ALL_TAC)) THEN
REPEAT (PAT_ASSUM``STO a = STO b``(fn th => ALL_TAC)) THEN
REPEAT (PAT_ASSUM``LDA a = LDA b``(fn th => ALL_TAC)) THEN
REPEAT (PAT_ASSUM``SN a = SN b``(fn th => ALL_TAC)) THEN
REPEAT (PAT_ASSUM``WI a = WI b``(fn th => ALL_TAC)) THEN
REPEAT (PAT_ASSUM``PI1 a = PI1 b``(fn th => ALL_TAC)) THEN
REPEAT (PAT_ASSUM``NUM a = NUM b``(fn th => ALL_TAC)) 



*)

val _ = export_theory ();
val _ = print_theory "-";

end (* structure *)