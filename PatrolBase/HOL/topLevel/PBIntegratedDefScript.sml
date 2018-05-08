(******************************************************************************)
(* PBIntegratedDefTheory                                                      *)
(* Author: Lori Pickering                                                     *)
(* Date: 7 May 2018                                                           *)
(* Definitions for ssmPBIntegratedTheory.                                     *)
(******************************************************************************)
structure PBIntegratedDefScript = struct

(* ===== Interactive Mode ====
app load  ["TypeBase", "listTheory","optionTheory",
           "uavUtilities",
	  "OMNITypeTheory", "PBTypeTheory","PBIntegratedDef"];

open TypeBase listTheory optionTheory
     aclsemanticsTheory aclfoundationTheory
     uavUtilities
     OMNITypeTheory PBTypeTheory PBIntegratedDef
 ==== end Interactive Mode ==== *)

open HolKernel Parse boolLib bossLib;
open TypeBase listTheory optionTheory
open  uavUtilities
open OMNITypeTheory PBTypeTheory

val _ = new_theory "PBIntegratedDef";



val _= export_theory();
end