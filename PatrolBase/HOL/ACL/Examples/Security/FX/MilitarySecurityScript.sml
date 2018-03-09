(*=======================================*)
(* Military security example: SKC 3/22/2011 *)
(*=======================================*)

(* This example illustrates the application of Bell and LaPadula's
   multi-level security policies, specifically, the simple security
   condition - no read up- and the *-property - no write down.  These
   examples are built on top of a partial ordering of confidentiality
   labels (TopSecret, Secret, Confidential, and Unclassified) paired
   with subsets of categories FX1 and FX2 (the two experimental
   fighter projects).  Subjects are principals who make requests, in
   this case read or write requests on files. Objects are principals
   that are accessed, i.e., principals subjected to being read from or
   written to. *)

(* The examples here are taken from section 5.4 Expressing Military
   Security Policies, in "Access Control, Security, and Trust: A Logical
   Approach," by S-K Chin and Susan Older. This example is a solution of
   Exercise 13.2.2 *)

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

structure MilitarySecurityScript = struct

open HolKernel boolLib Parse bossLib;
open pred_setTheory PFset_conv pred_setLib relationTheory;
open aclfoundationTheory aclsemanticsTheory aclrulesTheory aclDrulesTheory;
open acl_infRules;
open SecurityLevelsTheory SecurityLevels_conv;

(***********
* create a new theory
***********)
val _ = new_theory "MilitarySecurity";

(************************
* THE DEFINITIONS START HERE
************************)

(************************
* We will use strings for principal names 
* and actions will be put and take applied
* to principals
*************************)

val _ = Hol_datatype `Op = rd | wrt`;

val _ = Hol_datatype `Action = Act of (Op # 'apn Princ)`;

(**********************
* As per Example 5.4.3, the following objects exist for both 
* FX-1 and FX-2 projects:
* threat scenario (TS), status report (TS), requirements (S), 
* design (S), artist renderings (C), and press releases (UC).
*
* As per Exercise 13.2.2, our security levels will be a pair
* of partial orders based on clearance levels (UC, C, S, TS)
* and sets of categories {{},{FX1},{FX2},{FX1,FX2}}.
*
* As per Exercise 13.2.2, General Jane has jurisdiction over
* the FX-1 and FX-2 projects. The access matrices for FX-1
* and FX-2 objects are as shown.
*
* FX-1 Document | Jane  Amy  Biao  Sonja   Jude
* --------------+--------------------------------
* threat        |  r,w   r
* report        |  r     r,w   w      w      w
* requirements  |  r     r     r
* design        |  r     r     r,w
* renderings    |  r     r     r      r,w
* pr            |  r     r     r      r      r,w
* Note: pr able to be read by anyone, but written
* only by Jude.
*
* FX-2 Document | Jane  Arlen Burt   Suresh Jodi
* --------------+--------------------------------
* threat        |  r,w   r
* report        |  r     r,w   w      w      w
* requirements  |  r     r     r
* design        |  r     r     r,w
* renderings    |  r     r     r      r,w
* pr            |  r     r     r      r      r,w
* Note: pr able to be read by anyone, but written
* only by Jodi.
*
* Clearance levels of objects
*
* Object      | Clearance
* ------------+----------
* FX-1 threat | (TS,{FX1})
* FX-1 report | (TS,{FX1})
* FX-1 reqs   | (S,{FX1})
* FX-1 design | (S,{FX1})
* FX-1 rends  | (C,{FX1})
* FX-1 pr     | (UC,{})
*
* Object      | Clearance
* ------------+----------
* FX-2 threat | (TS,{FX2})
* FX-2 report | (TS,{FX2})
* FX-2 reqs   | (S,{FX2})
* FX-2 design | (S,{FX2})
* FX-2 rends  | (C,{FX2})
* FX-2 pr     | (UC,{})
*
* Subject | Clearance
* --------+---------------
* Jane    | (TS,{FX1,FX2})
* Amy     | (TS,{FX1})
* Biao    | (S,{FX1})
* Sonja   | (C,{FX1})
* Jude    | (UC,{})
* Arlen   | (TS,{FX2})
* Burt    | (S,{FX2})
* Suresh  | (C,{FX2})
* Jodi    | (UC,{})
**********************)

(*********************
* Proof that (TopSecret,{FX1}) doms (Unclassified,{})
* We do this by using the appropriate clearance levels
* in the Hasse diagram and transitivity.
**********************)
val l2_doms_l1 =
let
  val term1 = 
  ``(M:('pName Action,'b,'pName,'Int,SClass#Categories set)Kripke,Oi:'Int po,OSec)
     sat 
    ((sLab (TopSecret,{FX1})) doms (sLab (TopSecret,{}))):
    ('pName Action,'pName,'Int,SClass#Categories set)Form``
  val term2 =
  ``(M:('pName Action,'b,'pName,'Int,SClass#Categories set)Kripke,Oi:'Int po,OSec)
     sat 
    ((sLab (TopSecret,{})) doms (sLab (Secret,{}))):
    ('pName Action,'pName,'Int,SClass#Categories set)Form``
  val term3 =
  ``(M:('pName Action,'b,'pName,'Int,SClass#Categories set)Kripke,Oi:'Int po,OSec)
     sat 
    ((sLab (Secret,{})) doms (sLab (Confidential,{}))):
     ('pName Action,'pName,'Int,SClass#Categories set)Form``
  val term4 =
  ``(M:('pName Action,'b,'pName,'Int,SClass#Categories set)Kripke,Oi:'Int po,OSec)
     sat 
    ((sLab (Confidential,{})) doms (sLab (Unclassified,{}))):
     ('pName Action,'pName,'Int,SClass#Categories set)Form``
  val [th1,th2,th3,th4] = 
    map ((REWRITE_RULE []) o OSec_CONV) [term1,term2,term3,term4]
  val th5 = DOMS_TRANS th1 th2
  val th6 = DOMS_TRANS th5 th3
in
  DOMS_TRANS th6 th4
end;

(*********************
* Proof that Jude can write to FX-1 report
**********************)

val Jude_write_FX1report_authorized =
 let
  val a1 = 
    ACL_ASSUM2
    ``((Name Jude) says (prop (Act (wrt, Name FX1report))))
      :('pName Action, 'pName,'Int,SClass#(Categories set))Form``
    ``Oi:('Int po)`` ``OSec``
  val a2 =
    ACL_ASSUM2
    ``((sl (FX1report:'pName)) eqs (sLab (TopSecret,{FX1})))
      :('pName Action, 'pName,'Int,SClass#(Categories set))Form``
    ``Oi:('Int po)`` ``OSec``
  val a3 =
    ACL_ASSUM2
    ``((sl Jude) eqs (sLab (Unclassified,{})))
      :('pName Action, 'pName,'Int,SClass#(Categories set))Form``
    ``Oi:('Int po)`` ``OSec``
  val a4 =
    ACL_ASSUM2
    ``(((sl FX1report) doms (sl Jude)) impf
      ((Name Jude) controls (prop (Act (wrt,(Name FX1report))))))
      :('pName Action, 'pName,'Int,SClass#(Categories set))Form``
    ``Oi:('Int po)`` ``OSec``
  val th5 = 
    SL_DOMS a3 a2 l2_doms_l1
  val th6 = ACL_MP th5 a4
  val th7 = CONTROLS th6 a1
  val th8 = DISCH_ALL th7
in
  save_thm("Jude_write_FX1report_authorized",th8)
end;

val _ = print_theory "-";
val _ = export_theory();

end; (*structure*)
