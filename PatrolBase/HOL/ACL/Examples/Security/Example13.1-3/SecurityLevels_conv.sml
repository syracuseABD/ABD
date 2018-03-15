(* Created by S-K Chin 3/19/2011. *)
(* These HOL/ml functions support the forward inference rule style of *)
(* reasoning in the access-control logic (see Access Control, Security,*)
(* and Trust: A Logical Approach, Shiu-Kai Chin and Susan Older, *)
(* CRC Press.*)

(***********
* Load necessary theories
***********)
(* Interactive mode
set_trace "Unicode" 0;
app load ["pred_setTheory", "PFset_conv", "relationTheory", "aclfoundationTheory",
          "aclsemanticsTheory", "aclrulesTheory", "aclDrulesTheory","pairTheory", 
	  "oneTheory","acl_infRules","SecurityLevelsTheory"];
*)
structure SecurityLevels_conv :> SecurityLevels_conv =
struct

(*********Load the theories on which the inference rules are based******)
open HolKernel boolLib Parse;
open pred_setTheory PFset_conv relationTheory aclfoundationTheory;
open aclsemanticsTheory aclrulesTheory aclDrulesTheory pairTheory oneTheory acl_infRules;
open SecurityLevelsTheory;

(**** This is a conversion for OSec ************************)
(* Terms must be of the form (M,Oi,OSec) sat (l1 doms l2)  *)
(***********************************************************)
(*** THE FOLLOWING 4 TERMS ARE FOR TESTING **************
 * term3 shows that ordering of elements in sets does matter
 * for now
val term1 = 
``(M:('propVar,'b,'pName,'Int,SClass#Categories set)Kripke,Oi:'Int po,OSec) sat 
   ((sLab (TopSecret,{FX1;FX2})) doms (sLab (TopSecret,{FX1}))):
    ('propVar,'pName,'Int,SClass#Categories set)Form``;

val term2 = 
``(M:('propVar,'b,'pName,'Int,SClass#Categories set)Kripke,Oi:'Int po,OSec) sat 
   ((sLab (TopSecret,{FX1;FX2})) doms (sLab (TopSecret,{FX1;FX2}))):
    ('propVar,'pName,'Int,SClass#Categories set)Form``;

val term3 = 
``(M:('propVar,'b,'pName,'Int,SClass#Categories set)Kripke,Oi:'Int po,OSec) sat 
   ((sLab (TopSecret,{FX1;FX2})) doms (sLab (TopSecret,{FX2;FX1}))):
    ('propVar,'pName,'Int,SClass#Categories set)Form``;

val term4 = 
``(M:('propVar,'b,'pName,'Int,SClass#Categories set)Kripke,Oi:'Int po,OSec) sat 
   ((sLab (TopSecret,{FX1;FX2})) doms (sLab (TopSecret,{}))):
    ('propVar,'pName,'Int,SClass#Categories set)Form``;
***************************)

fun OSec_CONV term =
  REWRITE_CONV
  [sat_def,doms_def,Lsfn_def,SCOrder_simp,GSYM(UNIV_NOT_EMPTY),repPO_OSec,
   getSClass_def,getSCat_def, Categories_SUBSET, SUBSET_REFL, EMPTY_SUBSET] term;

end; (* structure *)