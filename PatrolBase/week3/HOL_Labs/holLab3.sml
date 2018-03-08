(* -------------------------------------------------------------------------- *)
(* Section 7.1: HOL Syntax functions for manipulating HOL terms               *)
(* Constructing and Deconstructing HOL Terms                                  *)
(* Author: Shiu-Kai Chin                                                      *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Disassembling and reassembling HOL terms is an important capability for    *)
(* understanding how HOL works. It is essential for developing our own        *)
(* extensions to HOL.                                                         *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* To practice using the HOL syntax functions, let's deconstruct a HOL term   *)
(* into its atomic components and then reassmeble it to get back the          *)
(* original.                                                                  *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Our starting term amounts to the following:                                *)
(* for all numbers x and y, if x is less than or equal to y, and y is less    *)
(* or equal to x, then x equals y.                                            *)
(* -------------------------------------------------------------------------- *)
val originalTerm = ``!(x:num)(y:num).(x <= y) /\ (x >= y) ==> (x = y)``;

(* -------------------------------------------------------------------------- *)
(* We verify that originalTerm is a universally quantified term.              *)
(* -------------------------------------------------------------------------- *)
is_forall originalTerm;

(* -------------------------------------------------------------------------- *)
(* We deconstruct the outermost universally quantified expression to get the  *)
(* the bound variable x and the scope !y.(x <= y) /\ (x >= y) ==> (x = y).    *)
(* We assign x to bvar1 and !y.(x <= y) /\ (x >= y) ==> (x = y) to scope1     *)
(* -------------------------------------------------------------------------- *)
val (bvar1,scope1) = dest_forall originalTerm;

(* -------------------------------------------------------------------------- *)
(* We deconstruct scope1 into its bound variable and scope.                   *)
(* We verifiy that it scope1 is a universally quantified expression.          *)
(* -------------------------------------------------------------------------- *)
is_forall scope1;

(* -------------------------------------------------------------------------- *)
(* We deconstruct it to get its bound variable y and its scope                *)
(* (x <= y) /\ (x >= y) ==> (x = y)                                           *)
(* -------------------------------------------------------------------------- *)
val (bvar2,scope2) = dest_forall scope1;

(* -------------------------------------------------------------------------- *)
(* We deconstruct scope2. First, we verify that it is an implication.         *)
(* -------------------------------------------------------------------------- *)
is_imp scope2;

(* -------------------------------------------------------------------------- *)
(* We get the antecedent and the conclusion using dest_imp.                   *)
(* -------------------------------------------------------------------------- *)
val (antecedent,conclusion) = dest_imp scope2;

(* -------------------------------------------------------------------------- *)
(* We deconstruct the antecedent. We first verify that it is a conjunction    *)
(* -------------------------------------------------------------------------- *)
is_conj antecedent;

(* -------------------------------------------------------------------------- *)
(* We get the two conjuncts using dest_conj.                                  *)
(* -------------------------------------------------------------------------- *)
val (term1,term2) = dest_conj antecedent;

(* -------------------------------------------------------------------------- *)
(* Here are our basic components for the original expression.  First the      *)
(* variables and their types followed by the atomic sentences.                *)
(* -------------------------------------------------------------------------- *)
bvar1;
bvar2;
term1;
term2;
conclusion;

(******************************************************************************)
(* Now, we reassemble the atomic components into the original formula.        *)
(******************************************************************************)
val conjTerm = mk_conj (term1,term2);

(* -------------------------------------------------------------------------- *)
(* Next, we create the implication from conjTerm and conclusion.              *)
(* -------------------------------------------------------------------------- *)
val impTerm = mk_imp(conjTerm,conclusion);

(* -------------------------------------------------------------------------- *)
(* Next, we recreate scope2 by universally quantifying impTerm with bvar2.    *)
(* -------------------------------------------------------------------------- *)
val newScope1 = mk_forall(bvar2,impTerm);

(* -------------------------------------------------------------------------- *)
(* Finally, we recreate the original term by universally quantifying          *)
(* newScope1 with x in bvar1. We see they match.                              *)
(* -------------------------------------------------------------------------- *)
val recreatedOriginal = mk_forall(bvar1,newScope1);
originalTerm;