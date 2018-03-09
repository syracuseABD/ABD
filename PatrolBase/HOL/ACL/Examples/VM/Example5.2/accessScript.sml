(*=======================================*)
(* Example 5.2: SKC 4/10/2011            *)
(*=======================================*)

(* Interactive mode
Assumes the presence of Holmakefile to supply path to the access-control
logic theories
*)

(***********
* Load necessary theories
* Note: if this file is located in a different subdirectory than the
* following files.
***********)
(* Interactive mode
set_trace "Unicode" 0;
app load ["pred_setTheory", "PFset_conv", "relationTheory", "aclfoundationTheory",
          "aclsemanticsTheory", "aclrulesTheory", "aclDrulesTheory","pairTheory", 
	  "oneTheory","acl_infRules"];
*)

structure accessScript = struct

open HolKernel boolLib Parse bossLib;
open pred_setTheory PFset_conv pred_setLib relationTheory;
open aclfoundationTheory aclsemanticsTheory aclrulesTheory aclDrulesTheory;
open acl_infRules;


(***********
* create a new theory
***********)
val _ = new_theory "access";

(************************
* THE DEFINITIONS START HERE
************************)

(************************
* Types of values in registers, which are principals of type
* 'pName.  Registers (such as ACC, MAR, and RR) can have 
* virtual addresses, physical addresses, and segement addresses.
* Registers such as IR can have operations.
*************************)
val _ = Hol_datatype `Addr = VA of num | PA of num | SA of num#num`;

val _ = Hol_datatype `Op = LDA of Addr | STO of Addr | trap`;

val _ = Hol_datatype `RVal = Opval of Op | Adval of Addr`;

(*********************
* Accessor functions for the above datatypes
*********************)
val getOp_def = Define `getOp(Opval op) = op`;
val getAdval_def = Define `getAdval(Adval addr) = addr`;
val getOpAddr_def = Define `(getOpAddr(LDA addr) = addr) /\ (getOpAddr(STO addr) = addr)`;
val getVAddr_def = Define `(getVAddr(VA addr) = addr)`;
val getPAddr_def = Define `(getPAddr(PA addr) = addr)`;
val getSAddr_def = Define `(getSAddr(SA (base,bound)) = (base,bound))`;

(*********************
* Proof when LDA can execute.
**********************)

val LDA_authorized =
 let
  val a1 = 
    ACL_ASSUM
    ``((Name IR) says (prop (Opval (LDA (VA vaddr))))):(RVal, 'pName,'Int,'Sec)Form``
  val a2 =
    ACL_ASSUM
    ``((Name RR) says (prop (Adval (SA (base,bound))))):(RVal, 'pName,'Int,'Sec)Form``
  val a3 =
    ACL_ASSUM
    ``(((Name RR) says (prop (Adval (SA (base,bound))))) impf
        ((base + vaddr) lt q) impf (vaddr lt bound) impf 
         ((Name IR) controls (prop (Opval (LDA (VA vaddr)))))):(RVal, 'pName,'Int,'Sec)Form``
  val a4 =
    ACL_ASSUM
    ``((base + vaddr) lt q):(RVal, 'pName,'Int,'Sec)Form``
  val a5 =
    ACL_ASSUM
    ``(vaddr lt bound):(RVal, 'pName,'Int,'Sec)Form``
  val th6 = ACL_MP a2 a3
  val th7 = ACL_MP a4 th6
  val th8 = ACL_MP a5 th7
  val th9 = CONTROLS th8 a1
  val th10 = DISCH_ALL th9
in
  save_thm("LDA_authorized",th10)
end;

(***************************
* Example with specific values
***************************)

(**
val a1 =
    ACL_ASSUM2
    ``((Name IR) says (prop (Opval (LDA (VA 5))))):(RVal, 'pName,'Int,'Sec)Form``
    ``Oi:('Int po)`` ``Os:('Sec po)``
val a2 =
    ACL_ASSUM2
    ``((Name RR) says (prop (Adval (SA (8,128))))):(RVal, 'pName,'Int,'Sec)Form``
    ``Oi:('Int po)`` ``Os:('Sec po)``
**)

val _ = print_theory "-";
val _ = export_theory();

end; (*structure*)
