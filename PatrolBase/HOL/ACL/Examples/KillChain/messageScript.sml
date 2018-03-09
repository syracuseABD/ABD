(* Kill Chain Messages by SKC 11/6/2010 *)

(***********
* Add the path to where aclfoundationTheory resides.
* Then, add the path to HOL's search path.
***********)
(* Interactive mode
val aclPath = "/home/skchin/Documents/HOL/ACL";
loadPath := aclPath::(!loadPath);
*)

(***********
* Load necessary theories
***********)
(* Interactive mode
load "aclfoundationTheory";
*)

structure messageScript = struct

open HolKernel boolLib Parse bossLib
open aclfoundationTheory;

(***********
* create a new theory
***********)
val _ = new_theory "message";

(************************
* THE DEFINITIONS START HERE
************************)


(* Position is given by (x,y,z) coordinates *)
val _ = Hol_datatype
    `Position = Coord of num # num # num`;

val coordPos_def = 
    Define `coordPos(Coord (x,y,z)) = (x,y,z)`;

(* Air Strike Request *)
val _ = Hol_datatype
    `ASR = ReqS of Position`;

val posASR_def =
    Define `posASR(ReqS pos) = pos`;

(* Air Strike Approval *)
val _ = Hol_datatype
    `ASA = OK of ASR`;

val asrASA_def =
    Define `asrASA(OK asr) = asr`;

(* Air Strike Order *)
val _ = Hol_datatype
    `ASO = Strike of Position`;

val posASO_def =
    Define `posASO(Strike pos) = pos`;

(* Origin *)
val _ = Hol_datatype
    `Origin = From of 'name Princ`;

val princOrigin_def =
    Define `princOrigin(From princ) = princ`;

(* Destination *)
val _ = Hol_datatype
    `Destination = To of 'name Princ`;

val princDestination_def =
    Define `princDestination(To princ) = princ`;

(* Contents *)
val _ = Hol_datatype
    `Contents = asrM of ASR | asaM of ASA | asoM of ASO`;

val asrContents_def =
    Define `asrContents(asrM asr) = asr`;

val asaContents_def =
    Define `asaContents(asaM asa) = asa`;

val asoContents_def =
    Define `asoContents(asoM aso) = aso`;

(* Messages *)
val _ = Hol_datatype 
    `Message = MSG of 'name Origin # 'name Destination # Contents`;

val msgOrigin_def = 
    Define `msgOrigin(MSG(From oprinc, To dprinc, msg)) = oprinc`;

val msgDestination_def =
    Define `msgDestination(MSG(From oprinc, To dprinc, msg)) = dprinc`;

val msgContents_def =
    Define `msgContents(MSG(From oprinc, To dprinc, msg)) = msg`;
    
val _ = export_theory();

end;