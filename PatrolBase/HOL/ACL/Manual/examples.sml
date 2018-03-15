

(******************************************************************************)
(* Examples developed for ACL-HOL manual                                      *)
(* Shiu-Kai Chin                                                              *)
(* 23 May 2015                                                                *)
(******************************************************************************)
app load ["acl_infRules"];
open acl_infRules;

val EQF_CONTROLS_Test =
let
  val th1 = ACL_ASSUM``(f eqf f'):('a,'c,'d,'e)Form``
  val th2 = ACL_ASSUM``(P controls f):('a,'c,'d,'e)Form``
  val th3 = EQF_CONTROLS th1 th2
  val th4 = DISCH(hd(hyp th2)) th3
in
  DISCH(hd(hyp th1)) th4
end;

val EQF_EQF1_Test =
let
  val th1 = ACL_ASSUM``(f eqf f'):('a,'c,'d,'e)Form``
  val th2 = ACL_ASSUM``(f eqf g):('a,'c,'d,'e)Form``
  val th3 = EQF_EQF1 th1 th2
  val th4 = DISCH(hd(hyp th2)) th3
in
  DISCH(hd(hyp th1)) th4
end;

val EQF_EQF2_Test =
let
  val th1 = ACL_ASSUM``(f eqf f'):('a,'c,'d,'e)Form``
  val th2 = ACL_ASSUM``(g eqf f):('a,'c,'d,'e)Form``
  val th3 = EQF_EQF2 th1 th2
  val th4 = DISCH(hd(hyp th2)) th3
in
  DISCH(hd(hyp th1)) th4
end;

val EQF_IMPF1_Test =
let
  val th1 = ACL_ASSUM``(f eqf f'):('a,'c,'d,'e)Form``
  val th2 = ACL_ASSUM``(f impf g):('a,'c,'d,'e)Form``
  val th3 = EQF_IMPF1 th1 th2
  val th4 = DISCH(hd(hyp th2)) th3
in
  DISCH(hd(hyp th1)) th4
end;

val EQF_IMPF2_Test =
let
  val th1 = ACL_ASSUM``(f eqf f'):('a,'c,'d,'e)Form``
  val th2 = ACL_ASSUM``(g impf f):('a,'c,'d,'e)Form``
  val th3 = EQF_IMPF2 th1 th2
  val th4 = DISCH(hd(hyp th2)) th3
in
  DISCH(hd(hyp th1)) th4
end;

val EQF_NOTF_Test =
let
  val th1 = ACL_ASSUM``(f eqf f'):('a,'c,'d,'e)Form``
  val th2 = ACL_ASSUM``(notf f):('a,'c,'d,'e)Form``
  val th3 = EQF_NOTF th1 th2
  val th4 = DISCH(hd(hyp th2)) th3
in
  DISCH(hd(hyp th1)) th4
end;

val EQF_ORF1_Test =
let
  val th1 = ACL_ASSUM``(f eqf f'):('a,'c,'d,'e)Form``
  val th2 = ACL_ASSUM``(f orf g):('a,'c,'d,'e)Form``
  val th3 = EQF_ORF1 th1 th2
  val th4 = DISCH(hd(hyp th2)) th3
in
  DISCH(hd(hyp th1)) th4
end;

val EQF_ORF2_Test =
let
  val th1 = ACL_ASSUM``(f eqf f'):('a,'c,'d,'e)Form``
  val th2 = ACL_ASSUM``(g orf f):('a,'c,'d,'e)Form``
  val th3 = EQF_ORF2 th1 th2
  val th4 = DISCH(hd(hyp th2)) th3
in
  DISCH(hd(hyp th1)) th4
end;

val EQF_REPS_Test =
let
  val th1 = ACL_ASSUM``(f eqf f'):('a,'c,'d,'e)Form``
  val th2 = ACL_ASSUM``(reps P Q f):('a,'c,'d,'e)Form``
  val th3 = EQF_REPS th1 th2
  val th4 = DISCH(hd(hyp th2)) th3
in
  DISCH(hd(hyp th1)) th4
end;

val EQF_SAYS_Test =
let
  val th1 = ACL_ASSUM``(f eqf f'):('a,'c,'d,'e)Form``
  val th2 = ACL_ASSUM``(P says f):('a,'c,'d,'e)Form``
  val th3 = EQF_SAYS th1 th2
  val th4 = DISCH(hd(hyp th2)) th3
in
  DISCH(hd(hyp th1)) th4
end;