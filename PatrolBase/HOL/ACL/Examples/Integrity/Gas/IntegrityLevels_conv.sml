(* Created by S-K Chin 3/18/2011. *)
(* These HOL/ml functions support the forward inference rule style of *)
(* reasoning in the access-control logic (see Access Control, Security,*)
(* and Trust: A Logical Approach, Shiu-Kai Chin and Susan Older, *)
(* CRC Press.*)

structure IntegrityLevels_conv :> IntegrityLevels_conv =
struct

(*********Load the theories on which the inference rules are based******)
open HolKernel boolLib Parse;
open pred_setTheory relationTheory aclfoundationTheory;
open aclsemanticsTheory aclrulesTheory pairTheory oneTheory acl_infRules;
open IntegrityLevelsTheory;

(**** This is a conversion for ICOrder_PO ****************)
(* Terms must be of the form (M,Oi,Os) sat (l1 domi l2)  *)
(*********************************************************)
fun ICOrder_PO_CONV term =
  REWRITE_CONV
  [sat_def,domi_def,Lifn_def,ICOrder_simp,GSYM(UNIV_NOT_EMPTY)] term;

end; (* structure *)