(* Created by S-K Chin 11/9/2011 *)

structure missioninf_rules :> missioninf_rules =
struct

(* Load the theories on which the rules are based *)
open HolKernel boolLib Parse bossLib;
open missionRolesTheory missionStaffTheory;

(***********************************************************
* ImpliedControlsSays
*
* ImpliedControlsSays : term -> thm -> thm -> thm -> thm
*
* SYNOPSIS
* Deduces formula f2 if the principal who says f1, controls f1, and
* f1 impf f2.
*
* DESCRIPTION
*
*     A1 |- (M,Oi,Os) sat P says f1  A2 |- (M,Oi,Os) sat P controls f1
*                            A3 |- f1 impf f2
*     ------------------------------------------------------- ImpliedControlsSays Q
*               A1 u A2 u A3 |- (M,Oi,Os) sat Q says f2
*
* FAILURE
* Fails unless the theorems match in terms of principals and formulas
* in the access-control logic.
***********************************************************)
fun ImpliedControlsSays Q th1 th2 th3 =
MATCH_MP (MATCH_MP (MATCH_MP (ISPEC Q ImpliedControlsSays_thm) th1) th2) th3;

(***********************************************************
* DualControl
*
* DualControl : thm -> thm -> thm -> thm
*
* SYNOPSIS
* Deduces formula f if P says f, Q says f, and (P meet Q) controls f
*
* DESCRIPTION
*
*     A1 |- (M,Oi,Os) sat P says f  A2 |- (M,Oi,Os) sat Q says f
*                         A3 |- (P meet Q) controls f
*     ------------------------------------------------------- DualControl
*                         A1 u A2 u A3 |- (M,Oi,Os) sat f
*
* FAILURE
* Fails unless the theorems match in terms of principals and formulas
* in the access-control logic.
***********************************************************)
fun DualControl th1 th2 th3 =
MATCH_MP (MATCH_MP (MATCH_MP DualControl_thm th1) th2) th3;

(***********************************************************
* AltControls1
*
* AltControls : thm -> thm -> thm
*
* SYNOPSIS
* Deduces formula f if P says f and (P controls f andf Q controls f)
*
* DESCRIPTION
*
*     A1 |- (M,Oi,Os) sat P says f A2 |- P controls f andf Q controls f
*     ------------------------------------------------------- AltControls1
*                         A1 u A2 |- (M,Oi,Os) sat f
*
* FAILURE
* Fails unless the theorems match in terms of principals and formulas
* in the access-control logic.
***********************************************************)
fun AltControls1 th1 th2 =
MATCH_MP (MATCH_MP AlternateControls1_thm th1) th2;

(***********************************************************
* AltControls2
*
* AltControls : thm -> thm -> thm
*
* SYNOPSIS
* Deduces formula f if Q says f and (P controls f andf Q controls f)
*
* DESCRIPTION
*
*     A1 |- (M,Oi,Os) sat Q says f A2 |- P controls f andf Q controls f
*     ------------------------------------------------------- AltControls2
*                         A1 u A2 |- (M,Oi,Os) sat f
*
* FAILURE
* Fails unless the theorems match in terms of principals and formulas
* in the access-control logic.
***********************************************************)
fun AltControls2 th1 th2 =
MATCH_MP (MATCH_MP AlternateControls2_thm th1) th2;

(***********************************************************
* ImpliedControlsDelegation
*
* ImpliedControlsDelegation : term -> thm -> thm -> thm -> thm -> thm
*
* SYNOPSIS
* Deduces formula f2 if the principal who says f1, controls f1, and
* f1 impf f2.
*
* DESCRIPTION
*
*     A1 |- (M,Oi,Os) sat Q controls f1  A2 |- (M,Oi,Os) sat reps P Q f1
*            A3 |- P quoting Q says f1  A4 |- f1 impf f2
*     ------------------------------------------------------- ImpliedControlsDelegation R
*          A1 u A2 u A3 u A4 |- (M,Oi,Os) sat R says f2
*
* FAILURE
* Fails unless the theorems match in terms of principals and formulas
* in the access-control logic.
***********************************************************)
fun ImpliedControlsDelegation R th1 th2 th3 th4 =
MATCH_MP(MATCH_MP (MATCH_MP (MATCH_MP (ISPEC R ImpliedControlsDelegation_thm) th1) th2) th3) th4;

end; (* structure *)
