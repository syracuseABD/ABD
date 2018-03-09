(*=======================================*)
(* Example 13.4: SKC 4/9/2011            *)
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
	  "oneTheory","acl_infRules","SecurityLevelsTheory","SecurityLevels_conv"];
*)

structure accessScript = struct

open HolKernel boolLib Parse bossLib;
open pred_setTheory PFset_conv pred_setLib relationTheory;
open aclfoundationTheory aclsemanticsTheory aclrulesTheory aclDrulesTheory;
open acl_infRules;
open SecurityLevelsTheory SecurityLevels_conv;

(***********
* create a new theory
***********)
val _ = new_theory "access";

(************************
* THE DEFINITIONS START HERE
************************)

val _ = Hol_datatype `Op = rd | wrt`;

val _ = Hol_datatype `Action = Act of (Op # 'apn Princ)`;

(**********************
Subject or Object | Confidentiality Level
------------------+----------------------
 Carol            | (Hi,{Bin1,Bin2})
 Kate             | (Lo,{Bin2})
 O1               | (Hi,{Bin1,Bin2})
 O2               | (Lo,{Bin2})
 O3               | (Lo,{Bin1})
 O4               | (Lo,{})
**********************)

(*********************
* Proof that (Hi,{Bin1;Bin2}) doms (Lo,{Bin1})
* We do this by using the appropriate clearance levels
* in the Hasse diagram and transitivity.
**********************)

val l2_doms_l1 =
let
  val term1 = 
  ``(M:('pName Action,'b,'pName,'Int,SClass#Categories set)Kripke,Oi:'Int po,OSec)
     sat 
    ((sLab (Hi,{Bin1;Bin2})) doms (sLab (Hi,{Bin1}))):
    ('pName Action,'pName,'Int,SClass#Categories set)Form``
  val term2 =
  ``(M:('pName Action,'b,'pName,'Int,SClass#Categories set)Kripke,Oi:'Int po,OSec)
     sat 
    ((sLab (Hi,{Bin1})) doms (sLab (Lo,{Bin1}))):
    ('pName Action,'pName,'Int,SClass#Categories set)Form``
  val [th1,th2] = 
    map ((REWRITE_RULE []) o OSec_CONV) [term1,term2]
  val th3 = DOMS_TRANS th1 th2
in
  DOMS_TRANS th1 th2
end;

(*********************
* Proof that Carol can read O3 and Kate can write O1.
**********************)

val Carol_read_O3_authorized =
 let
  val a1 = 
    ACL_ASSUM2
    ``((Name Carol) says (prop (Act (rd, Name O3))))
      :('pName Action, 'pName,'Int,SClass#(Categories set))Form``
    ``Oi:('Int po)`` ``OSec``
  val a2 =
    ACL_ASSUM2
    ``((sl (O3:'pName)) eqs (sLab (Lo,{Bin1})))
      :('pName Action, 'pName,'Int,SClass#(Categories set))Form``
    ``Oi:('Int po)`` ``OSec``
  val a3 =
    ACL_ASSUM2
    ``((sl Carol) eqs (sLab (Hi,{Bin1;Bin2})))
      :('pName Action, 'pName,'Int,SClass#(Categories set))Form``
    ``Oi:('Int po)`` ``OSec``
  val a4 =
    ACL_ASSUM2
    ``(((sl Carol) doms (sl O3)) impf
      ((Name Carol) controls (prop (Act (rd,(Name O3))))))
      :('pName Action, 'pName,'Int,SClass#(Categories set))Form``
    ``Oi:('Int po)`` ``OSec``
  val th5 = 
    SL_DOMS a2 a3 l2_doms_l1
  val th6 = ACL_MP th5 a4
  val th7 = CONTROLS th6 a1
  val th8 = DISCH_ALL th7
in
  save_thm("Carol_read_O3_authorized",th8)
end;


val _ = print_theory "-";
val _ = export_theory();

end; (*structure*)
