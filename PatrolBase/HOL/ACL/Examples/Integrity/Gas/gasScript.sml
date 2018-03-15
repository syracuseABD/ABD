(*************************************************)
(* Gas pump example                              *)
(* Created 19 January 2011 by Shiu-Kai Chin      *)
(*************************************************)

(* Interactive mode
val aclPath = "../..";
loadPath := aclPath::(!loadPath);
app load 
    ["IntegrityLevelsTheory","aclfoundationTheory","aclsemanticsTheory",
     "aclrulesTheory","aclDrulesTheory","acl_infRules","stringTheory","pred_setTheory"];

(* Disable Pretty-Printing *)
set_trace "Unicode" 0;
*)

structure gasScript = struct

open HolKernel boolLib Parse bossLib
open IntegrityLevelsTheory aclfoundationTheory aclsemanticsTheory 
 aclrulesTheory aclDrulesTheory acl_infRules stringTheory pred_setTheory;

(***********
* create a new theory
***********)
val _ = new_theory "gas";

(************************
* THE DEFINITIONS START HERE
************************)

(************************
* We will use strings for principal names 
* and actions will be put and take applied
* to principals
*************************)

val _ = Hol_datatype `Op = Put | Take`;

val _ = Hol_datatype `Action = Act of (Op # 'apn Princ)`;

(****Justification for Pump1 putting gas into PGC****)
val Pump1_to_PGC =
 let
  val a1 =
    ACL_ASSUM 
    ``((Name Pump1) says (prop (Act (Put, Name PGC))))
      :('pName Action,'pName,IClass,'Sec)Form``
  val a2 = 
    ACL_ASSUM
    ``(((il Pump1) domi (il PGC)) impf
      ((Name Pump1) controls (prop (Act (Put,Name PGC)))))
      :('pName Action,'pName,IClass,'Sec)Form``
  val a3 = 
    ACL_ASSUM
    ``((il PGC) eqi (iLab Prem)):('pName Action,'pName,IClass,'Sec)Form``
  val a4 =
    ACL_ASSUM
    ``((il Pump1) eqi (iLab Prem)):('pName Action, 'pName, IClass, 'Sec) Form``
  val th5 =
   ISPECL 
   [``(iLab Prem):('pName,IClass)IntLevel``,
    ``M:('pName Action,'b,'pName,IClass,'Sec)Kripke``,
    ``Oi:(IClass po)``,``Os:('Sec po)``] IClass_PO_reflexive
  val th6 = 
    IL_DOMI a3 a4 th5
  val th7 = ACL_MP th6 a2
  val th8 = CONTROLS th7 a1
  val th9 = DISCH_ALL th8
in
  save_thm("Pump1_to_PGC",th9)
end;

(****Justification for Pump1 putting gas into RGC****)
val Pump1_to_RGC =
 let
  val a1 =
    ACL_ASSUM2 
    ``((Name Pump1) says (prop (Act (Put, Name RGC))))
      :('pName Action,'pName,IClass,'Sec)Form``
    ``ICOrder_PO`` ``Os:('Sec po)``
  val a2 = 
    ACL_ASSUM2
    ``(((il Pump1) domi (il RGC)) impf
      ((Name Pump1) controls (prop (Act (Put,Name RGC)))))
      :('pName Action,'pName,IClass,'Sec)Form``
    ``ICOrder_PO`` ``Os:('Sec po)``
  val a3 = 
    ACL_ASSUM2
    ``((il RGC) eqi (iLab Reg)):('pName Action,'pName,IClass,'Sec)Form``
    ``ICOrder_PO`` ``Os:('Sec po)``
  val a4 =
    ACL_ASSUM2
    ``((il Pump1) eqi (iLab Prem)):('pName Action, 'pName, IClass, 'Sec) Form``
    ``ICOrder_PO`` ``Os:('Sec po)``
  val th5 = 
    IL_DOMI a3 a4 
    (INST_TYPE
     [``:'Worlds`` |-> ``:'b``, ``:'propVar`` |-> ``:'pName Action``] 
     Prem_domi_Reg)
  val th6 = ACL_MP th5 a2
  val th7 = CONTROLS th6 a1
  val th8 = DISCH_ALL th7
in
  save_thm("Pump1_to_RGC",th8)
end;

val _ = print_theory "-";
val _ = export_theory ();
end;