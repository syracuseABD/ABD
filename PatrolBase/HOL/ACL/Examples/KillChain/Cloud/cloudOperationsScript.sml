(************************************************************)
(* Update functions for cloud operations                                  *)
(* Created 28 November 2010: Shiu-Kai Chin                               *)
(* Preliminary version created partially for CSE 691: Art & Practice of Cyber    *)
(* Defense, fall 2010                                                   *)
(************************************************************)

(* Interactive mode
val aclPath = "/home/skchin/Documents/RESEARCH/HOL/ACL";
val killPath = "/home/skchin/Documents/RESEARCH/HOL/ACL/Examples/KillChain";
loadPath := aclPath::(killPath::(!loadPath));
load "messageTheory";

(* Disable Pretty-Printing *)
set_trace "Unicode" 0;
*)

structure cloudOperationsScript = struct

open HolKernel boolLib Parse bossLib
open messageTheory;

(***********
* create a new theory
***********)
val _ = new_theory "cloudOperations";

(************************
* THE DEFINITIONS START HERE
************************)

(************************************************************)
(* Model of state:                                                     *)
(* We think of the state of the cloud as a list of mailboxes                 *)
(* or lists of pairs, where each pair consists of an                         *)
(* identifier paired with a list.  The identifier will be                       *)
(* a principal; the mailbox is a list of messages                             *)
(************************************************************)

(************************************************************)
(* Introduce the type mailbox                                            *)
(* produces type :'name mailBox                                          *)
(* A mailbox has an owner: 'name Princ and a list of messages:               *)
(*   ('name Message)list                                                *)
(************************************************************)

val _ = Hol_datatype
    `mailBox = MB of (('name)Princ # (('name)Message)list)`;

(************************************************************)
(* Accessor functions for mailboxes                                       *)
(************************************************************)

(************************************************************)
(* Fetching a mailbox's owner and its contents                             *)
(************************************************************)

val mbID_def = 
    Define `mbID(MB ((id:'name Princ),(msgs:(('name)Message)list))) = id`;

val mbMSGS_def =
    Define `mbMSGS(MB ((id:'name Princ),(msgs:(('name)Message)list))) = msgs`;

(************************************************************)
(* Operations on mailboxes                                               *)
(************************************************************)

(************************************************************)
(* Previous versions we had new messages appended to end of message list.    *)
(* This seemed too complicated in the end.                                *)
(* val appMSG_def =                                                    *)
(*    Define `appMSG (msg:'name Message) msgs = APPEND msgs [msg]`;      *)
(* updating a mailbox based on id/owner of mailbox                        *)
(* Old definition based on APPEND.  Newer definition uses CONS.            *)
(*val updateMB_def =                                                   *)
(*    Define                                                          *)
(*    `updateMB (msg:'name Message) (mbox:'name mailBox) =               *)
(*    if ((msgDestination msg) = (mbID mbox))                           *)
(*    then MB ((mbID mbox),(appMSG msg (mbMSGS mbox))) else mbox`;     *)
(************************************************************)

(************************************************************)
(* Newer definition just uses CONS. If the destination matches the owner then  *)
(* the message msg is pushed onto the existing list of messages in mbox.      *)
(************************************************************)
val updateMB_def =
    Define 
    `updateMB (msg:'name Message) (mbox:'name mailBox) = 
    if ((msgDestination msg) = (mbID mbox)) 
    then MB ((mbID mbox),(CONS msg (mbMSGS mbox))) else mbox`;

(************************************************************)
(* Define cloud state as a list of mailboxes                                *)
(************************************************************)

val _ = Hol_datatype
    `State = CS of ('name)mailBox list`;

(************************************************************)
(* Accessor function for cloud state                                      *)
(************************************************************)

val getMBoxes_def =
    Define `getMBoxes(CS (mboxes:(('name)mailBox)list)) = mboxes`;

(************************************************************)
(* Updating cloud state                                                 *)
(************************************************************)

val updateCloudState_def =
    Define 
    `updateCloudState (msg:'name Message) (state:'name State) = 
      CS (MAP (updateMB msg) (getMBoxes state))`;

val _ = export_theory();

end;