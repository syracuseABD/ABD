(************************************************************)
(* Operational semantics for cloud operations                               *)
(* Created 28 November 2010 by Shiu-Kai Chin                             *)
(* Earlier version created for CSE 691: Art & Practice of Cyber Defense        *)
(* Fall 2010 version of ACE                                              *)
(************************************************************)

(* Interactive mode
val aclPath = "/home/skchin/Documents/RESEARCH/HOL/ACL";
val killPath = "/home/skchin/Documents/RESEARCH/HOL/ACL/Examples/KillChain";
loadPath := aclPath::(killPath::(!loadPath));
app load ["IndDefRules","messageTheory","cloudOperationsTheory"];

(* Disable Pretty-Printing *)
set_trace "Unicode" 0;
*)

structure cloudSemantics1Script = struct

open HolKernel boolLib Parse bossLib
open IndDefRules messageTheory cloudOperationsTheory;

(***********
* create a new theory
***********)
val _ = new_theory "cloudSemantics1";

(************************
* THE DEFINITIONS START HERE
************************)

(************************************************************)
(* In this case clouds do not have (nor are trusted) with any credentials.  The *)
(* only operations in the cloud are to forward and store messages. Clouds are  *)
(* modeled as lists of mailboxes, where each mailbox is named or owned by a   *)
(* principal. For this case, messages are sent directly to mailboxes, perhaps     *)
(* named by public keys.                                                 *)
(*                                                                    *)
(* When a message is received, its destination is compared to mailbox IDs.     *)
(* I there is a match, then the message is pushed onto the mailbox's list      *)
(* of messages.                                                        *)
(*                                                                    *)
(* Semantics for clouds                                                  *)
(*                                                                    *)
(*         ----------------------------                   *)
(*         (msg, state) ===> updateCloudState msg state                    *)
(************************************************************)

val (EV1_rules,EV1_ind,EV1_cases) =
  Hol_reln
    `!(msg:'name Message) (state:'name State). EV1 (msg, state) (updateCloudState msg state)`;

val _ = export_theory();

end;