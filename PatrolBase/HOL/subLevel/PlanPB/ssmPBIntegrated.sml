

(******************************************************************************)
(* ssmPBIntegratedTheory                                                      *)
(* Author: Lori Pickering                                                     *)
(* Date: 7 May 2018                                                           *)
(* This theory aims to integrate the topLevel ssm with the sublevel ssms.  It *)
(* does this by adding a condition to the security context.  In particular,   *)
(* it requires that the "COMPLETE" state in the subLevel ssm must preceede    *)
(* transition to the next state at the topLeve.  I.e.,                        *)
(*   planPBComplete ==>                                                       *)
(*   PlatoonLeader controls crossLD.                                          *)
(* In the ssmPlanPB ssm, the last state is COMPLETE.  This is reached when the*)
(* the appropriate authority says complete and the transition is made.        *)
(* Note that following the ACL, if P says x and P controls x, then x.         *)
(* Therefore, it is not necessary for anyone to say x at the topLevel, because*)
(* it is already proved at the lower level.                                   *)
(* However, indicating that at the topLevel remains something to workout.     *)
(******************************************************************************)


structure ssmPBIntegratedScript = struct

open HolKernel Parse boolLib bossLib;

val _ = new_theory  "ssmPBIntegrated";




val _ = export_theory();

end