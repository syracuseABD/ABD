(************************************************************)
(* Update functions for MVA operations                      *)
(* Created 8 June 2011: Shiu-Kai Chin                       *)
(* Preliminary version created for AFRL IA Internship       *)
(* Summer 2011                                              *)
(************************************************************)

(* Interactive mode

load "messageTheory";

(* Disable Pretty-Printing *)
set_trace "Unicode" 0;
*)

structure mvaOperationsScript = struct

open HolKernel boolLib Parse bossLib
open messageTheory;

(***********
* create a new theory
***********)
val _ = new_theory "mvaOperations";

(************************
* THE DEFINITIONS START HERE
************************)

(************************************************************)
(* MVA state is the content of its registers.               *)
(* The registers we use are as follows:                     *)
(* (1) TX: message received by MVA                          *)
(* (2) RX: message transmitted by MVA                       *)
(* (3) Disp: authenticated received message displayed       *)
(* (4) Kmva: MVA's crypto key                               *)
(************************************************************)

(************************************************************)
(* Message buffers can be empty so we define a type to      *)
(* include this possibility                                 *)
(************************************************************)
val _ = Hol_datatype `mvaMsg = empty | Msg of ('pName)Message`;

(************************************************************)
(* Crypto token state is its crypto key and PIN             *)
(* (1) Key_Token: User's crypto key from crypto token       *)
(* (2) PIN_Token: PIN required by crypto token to use       *)
(*     Key_Token                                            *)
(************************************************************)

(************************************************************)
(* Define cryptographic keys as                             *)
(************************************************************)
val _ = Hol_datatype `cryptoKey = Key of num`;

(************************************************************)
(* Define MVA state as                                      *)
(************************************************************)

val _ = Hol_datatype
    `mvaState = 
      mvaS of ('pName)mvaMsg => ('pName)mvaMsg => ('pName)mvaMsg
               => cryptoKey`;

(************************************************************)
(* Accessor functions for MVA state                         *)
(************************************************************)

val getTXmsg_def =
    Define `getTXMsg(mvaS txMsg rxMsg dispMsg Kmva) = txMsg`;

val getRXmsg_def =
    Define `getTXMsg(mvaS txMsg rxMsg dispMsg Kmva) = rxMsg`;

val getDISPmsg_def =
    Define `getTXMsg(mvaS txMsg rxMsg dispMsg Kmva) = dispMsg`;

val getKmva_def =
    Define `getKmva(mvaS txMsg rxMsg dispMsg Kmva) = Kmva`;

(************************************************************)
(* Update functions for MVA state                           *)
(* We assume Kmva cannot be changed during normal operations*)
(* so there is no update                                    *)
(************************************************************)

val updateTXMsg_def =
    Define 
    `updateTXMsg msg (mvaS txMsg rxMsg dispMsg Kmva) =
     (mvaS msg rxMsg dispMsg Kmva)`;

val updateRXMsg_def =
    Define 
    `updateRXMsg msg (mvaS txMsg rxMsg dispMsg Kmva) =
     (mvaS txMsg msg dispMsg Kmva)`;

val updateDISPMsg_def =
    Define 
    `updateDISPMsg msg (mvaS txMsg rxMsg dispMsg Kmva) =
     (mvaS txMsg rxMsg msg Kmva)`;

(************************************************************)
(* Define Token state as                                    *)
(************************************************************)

val _ = Hol_datatype
    `tokenState = tokS of cryptoKey => num`;

(************************************************************)
(* Accessor functions for Token state                       *)
(************************************************************)

val getKeyToken_def = 
    Define `getKeyToken(tokS KToken pin) = KToken`;

val getPinToken_def =
    Define `getPinToken(tokS KToken pin) = pin`;

(************************************************************)
(* As crypto tokens are read-only devices, there are no     *)
(* update functions for tokenState.                         *)
(************************************************************)

(************************************************************)
(* We will describe the behavior of MVAs as a labeled       *)
(* transition system.  We define the kinds of labels we use *)
(* as part of the transition relation.                      *)
(* (1) PIN number input by user,                            *)
(* (2) message input by user to be transmitted,             *)
(* (3) message received by MVA from the cloud,              *)
(* (4) SEND msg button,                                     *)
(* (5) RD msg button,                                       *)
(* (6) NL for "no label"                                    *)
(************************************************************)

val _ = Hol_datatype
    `msgLabel = RX of cryptoKey => ('pName)Message | PIN of num 
              | TX of cryptoKey => ('pName)Message | RD | SEND | NL`;

(************************************************************)
(* Definition of MVA modes is done in terms of a language.  *)
(* IDLE0: MVA waiting with no received message              *)
(* IDLE1: MVA waiting with a message in RX buffer           *)
(* IN ('pName)Message: MVA user inputs a Message            *)
(* AUTH0 num: MVA user enters PIN send Messge               *)
(* SNDMSG: MVA user transmits authenticated message         *)
(* READ: MVA user wants to read waiting message             *)
(* AUTH1 num: MVA user enters PIN to read waiting message   *)
(************************************************************)

val _ = Hol_datatype
    `mvaMode = IDLE0 | IDLE1 | Input of ('pName)msgLabel | AUTH0 of ('pName)msgLabel
                | AUTH1 of ('pName)msgLabel | SNDMSG | READ `;

(************************************************************)
(* Define MVA configurations                                *)
(************************************************************)

val _ = Hol_datatype
   `mvaConfig = 
    mvaCfg of ('pName)mvaMode => ('pName)mvaState => tokenState`;

(************************************************************)
(* The transition rules                                     *)
(************************************************************)
val (tr_rules, tr_ind, tr_cases) =
  Hol_reln
  `(!dispMsg Kmva KToken PinToken Kmsg msg.
    (tr (mvaCfg IDLE0 (mvaS empty empty dispMsg Kmva)(tokS (Key KToken) PinToken)) (RX (Key Kmsg) msg) 
        (mvaCfg IDLE1 (mvaS empty (Msg msg) dispMsg Kmva)(tokS (Key KToken) PinToken))))
    /\
    (!dispMsg Kmva KToken PinToken inputPIN msg.
    (tr (mvaCfg IDLE1 (mvaS empty (Msg msg) dispMsg Kmva)(tokS (Key KToken) PinToken)) (RD) 
        (mvaCfg (AUTH1 (PIN inputPIN)) (mvaS empty (Msg msg) dispMsg Kmva)(tokS (Key KToken) PinToken))))
    /\
    (!dispMsg Kmva KToken PinToken inputPIN msg.((inputPIN = PinToken) ==>
    (tr (mvaCfg (AUTH1 (PIN inputPIN)) (mvaS empty (Msg msg) dispMsg Kmva)(tokS (Key KToken) PinToken)) (NL) 
        (mvaCfg IDLE0 (mvaS empty empty (Msg msg) Kmva)(tokS (Key KToken) PinToken)))))
    /\
    (!dispMsg Kmva KToken PinToken msg.
    (tr (mvaCfg IDLE0 (mvaS empty empty dispMsg Kmva)(tokS (Key KToken) PinToken)) (TX (Key KToken) msg) 
        (mvaCfg (Input (TX (Key KToken) msg)) (mvaS empty empty dispMsg Kmva)(tokS (Key KToken) PinToken))))
    /\
    (!dispMsg Kmva KToken PinToken inputPIN msg.((inputPIN = PinToken) ==>
    (tr (mvaCfg (Input (TX (Key KToken) msg)) (mvaS empty empty dispMsg Kmva)(tokS (Key KToken) PinToken)) 
        (PIN inputPIN) 
        (mvaCfg (AUTH0 (PIN inputPIN)) (mvaS (Msg msg) empty dispMsg Kmva)(tokS (Key KToken) PinToken)))))
    /\
    (!dispMsg Kmva KToken PinToken inputPIN msg.
    (tr (mvaCfg (AUTH0 (PIN inputPIN)) (mvaS (Msg msg) empty dispMsg Kmva)(tokS (Key KToken) PinToken))
        (SEND) 
        (mvaCfg IDLE0 (mvaS empty empty dispMsg Kmva)(tokS (Key KToken) PinToken))))`;

val _ = export_theory();

end;