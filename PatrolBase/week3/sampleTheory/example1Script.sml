(******************************************************************************)
(* A first example showing how to create a HOL script file to create a        *)
(* HOL theory, which allows us to name and save theorems we prove for later   *)
(* use.                                                                       *)
(* Author: Shiu-Kai Chin                                                      *)
(******************************************************************************)

(******************************************************************************)
(* All HOL script files are ML modules, so we need to declare the file        *)
(* example1Script as an ML structure.  Do this with the "structure: command   *)
(* as the very first executable line.  The very last executable line is "end" *)
(******************************************************************************)

structure example1Script = struct

(******************************************************************************)
(* Note: everything after new_theory must be part of a val assignment, when   *)
(* using Holmake.  Otherwise, there will be compilation errors. If you don't  *)
(* want to assign an expression to a name, just use "val _ = <expression>"    *)
(* The "_" indicates that we don't want to have a name.                       *)
(******************************************************************************)
open HolKernel Parse boolLib bossLib;

val _ = new_theory "example1";



(******************************************************************************)
(* This theorem was proved as part of forwardProofExample.sml                 *)
(******************************************************************************)
val prob1Theorem =
let
  val th1 = ASSUME ``p:bool``
  val th2 = ASSUME ``p ==> q``
  val th3 = MP th2 th1
  val terma = hd (hyp th2)
  val th4 = DISCH terma th3
  val termb = hd (hyp th1)
  val th5 = DISCH termb th4
in
  GENL [``p:bool``,``q:bool``] th5
end


(******************************************************************************)
(* If we want to save prob1Theorem as part of example1Theory, we need to      *)
(* explicitly save it.                                                        *)
(******************************************************************************)
val _ = save_thm("prob1Theorem",prob1Theorem);



(******************************************************************************)
(* Another theorem we proved as part of forwardProofExample.sml               *)
(******************************************************************************)
val demoTheorem = PROVE [] (concl prob1Theorem);
(******************************************************************************)
(* If we want to save prob1Theorem as part of example1Theory, we need to      *)
(* explicitly save it.                                                        *)
(******************************************************************************)
val _ = save_thm("demoTheorem",demoTheorem);

val _ = export_theory();




end (* structure *)