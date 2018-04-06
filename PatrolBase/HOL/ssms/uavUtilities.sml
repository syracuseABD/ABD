(******************************************************************************)
(* Utility functions for UAV                                                  *)
(* Author: Shiu-Kai Chin                                                      *)
(* Date: 21 December 2017                                                     *)
(******************************************************************************)

structure uavUtilities :> uavUtilities = struct

(* ==== interactive =====
app load ["TypeBase","listSyntax","aclfoundationTheory","optionTheory"]
 ==== end interactive ==== *)
open HolKernel boolLib Parse bossLib
open TypeBase listSyntax aclfoundationTheory optionTheory

fun trustedOn P x =
 Term`^P controls ^x`

fun trustedOnList P xlist = map (trustedOn P) xlist

fun trappedOn P x =
 Term`(^P says ^x) impf (prop NONE)`

fun trappedOnList P xlist = map (trappedOn P) xlist

fun andfTermList [] termType  =``TT : ^(ty_antiq termType)``
  | andfTermList [x] termType = ``^x``
  | andfTermList (x::xs) termType = ``^x andf ^(andfTermList xs termType)``

fun impfTermList [] termType = ``TT : ^(ty_antiq termType)``
  | impfTermList [x] termType = ``^x``
  | impfTermList (x::xs) termType = ``^x impf ^(impfTermList xs termType)``

fun condTrap clist termType =
Term`^(andfTermList clist termType) impf ((prop NONE):^(ty_antiq termType))`


(* ==== start here ====
 ==== end here ==== *)
end (* structure *)