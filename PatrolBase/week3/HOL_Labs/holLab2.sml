(* -------------------------------------------------------------------------- *)
(* Section 6.1: HOL Terms                                                     *)
(* Entering HOL terms and types                                               *)
(* Author: Shiu-Kai Chin                                                      *)
(* -------------------------------------------------------------------------- *)


(* -------------------------------------------------------------------------- *)
(* Start a HOL process and do Start HOL horizontal or Start HOL vertical      *)
(* after clicking on HOL followed by Process. Enter the following term in     *)
(* the HOL interpreter. Notice that HOL terms are surrounded by double back   *)
(* quotes.                                                                    *)
(* -------------------------------------------------------------------------- *)
``x``;

(* -------------------------------------------------------------------------- *)
(* Notice that the ML type of ``x`` is term. But, what is the type of the     *)
(* term within the HOL logic?  At the meta-level all HOL formulas are         *)
(* ML type term.  To see the HOL type, we need to print types explicitly.     *)
(* We do this by clicking HOL, Printing Switches, Show types                  *)
(* -------------------------------------------------------------------------- *)
``x``;

(* -------------------------------------------------------------------------- *)
(* We now see that ``x`` is ML type term. We also see that x itself is of     *)
(* HOL type alpha, where alpha is a type variable in HOL, just like 'a is     *)
(* a type variable in ML.                                                     *)
(* -------------------------------------------------------------------------- *)


(* -------------------------------------------------------------------------- *)
(* Notice that alpha is printed out as the greek character alpha. HOL takes   *)
(* advantage of unicode. However, how do we type alpha on our ASCII keyboard? *)
(* The answer is we don't.  Typically, it's easier to work with just the      *)
(* ASCII character set. We toggle unicode off by doing HOL, Printing switches,*)
(* Unicode.  Doing so, we type in ``x`` again and get the following.          *)
(* -------------------------------------------------------------------------- *)
``x``;

(* -------------------------------------------------------------------------- *)
(* Notice that instead of getting the Greek character alpha, we get 'a. We    *)
(* see in HOL that type variables are syntactically the same as in ML.        *)
(* Type variable names in ASCII start with the ' character.                   *)
(* -------------------------------------------------------------------------- *)


(* -------------------------------------------------------------------------- *)
(* Let's type in ``P x`` and see what happens                                 *)
(* -------------------------------------------------------------------------- *)
``P x``;

(* -------------------------------------------------------------------------- *)
(* Since we provided no type information about x and P, HOL has kept things   *)
(* as general as possible. x is of type alpha (:a), and P is a function from  *)
(* alpha (:'a) to beta (:'b).                                                 *)
(* -------------------------------------------------------------------------- *)


(* -------------------------------------------------------------------------- *)
(* Let's give HOL a bit more context. Let's type in ``P x ==> y``, where      *)
(* ==> is logical implication in HOL's ASCII syntax.  What we will see is     *)
(* HOL's type inference capability at work.                                   *)
(* -------------------------------------------------------------------------- *)
``P x ==> y``;

(* -------------------------------------------------------------------------- *)
(* Notice that HOL infers the types of y, x, and P.  Because implication      *)
(* operates on two booleans, the types of y and P x must be boolean. The      *)
(* type of x is unspecified, so HOL assigns it type :'a. Thus, P's type       *)
(* must be :'a -> bool, for P x to be a boolean.                              *)
(* -------------------------------------------------------------------------- *)


(* -------------------------------------------------------------------------- *)
(* As in ML, we explicitly constrain types of HOL formulas using a colon.     *)
(* For example, F and T are false and true, respectively. We explicitly       *)
(* constrain their types as follows: ``F:bool`` and ``T:``.                   *)
(* -------------------------------------------------------------------------- *)
``F:bool``;
``T:bool``;

(* -------------------------------------------------------------------------- *)
(* HOL accepts these constraints because they are consistent with the inferred*)
(* types of F and T. As in ML, type inference works on more complicated       *)
(* formulas.  ``(f:num -> bool) (x:num) \/ (F:bool)``; Notice that we         *)
(* f and x with parenthesis when we give their explicit types. This is        *)
(* typical to help the parser in HOL correctly interpret what's intended.     *)
(* -------------------------------------------------------------------------- *)
``(f:num -> bool)(x:num) \/ (F:bool)``;

(* -------------------------------------------------------------------------- *)
(* Of course, similar to ML, when we give contradictory type constraints,     *)
(* HOL will complain. This is actually a good thing since we don't want to    *)
(* contaminate any of our theories with inconsistent formulas. For example,   *)
(* consider ``(P:'a -> bool)(x:num)``.  HOL complains that we've given it     *)
(* conflicting type information. P is expecting an argument of type 'a but    *)
(* x is of type :num                                                          *)
(* -------------------------------------------------------------------------- *)
``(P:'a -> bool)(x:num)``;



(* ========================================================================== *)
(* Let's practice with HOL's ASCII syntax by translating logic formulas       *)
(* into HOL.  Remember to turn on types and turn off unicode by: HOL followed *)
(* by Printing Switches followed by types or unicode, respectively.           *)
(* ========================================================================== *)


(* -------------------------------------------------------------------------- *)
(* Let's practice by creating some HOL terms corresponding to logical         *)
(* formulas. We've already introduced ``T`` and ``F``. Negation is done with  *)
(* tilda, ``~x``                                                              *)
(* -------------------------------------------------------------------------- *)
``~x``;

(* -------------------------------------------------------------------------- *)
(* Let's do disjunction.  The term "x or y" is ``x \/ y``;                    *)
(* -------------------------------------------------------------------------- *)
``x \/ y``; 

(* -------------------------------------------------------------------------- *)
(* The term "x and y" is ``x /\ y``;                                          *)
(* -------------------------------------------------------------------------- *)
``x /\ y``;

(* -------------------------------------------------------------------------- *)
(* The term "x implies y" is ``x ==> y``;                                     *)
(* -------------------------------------------------------------------------- *)
``x ==> y``;

(* -------------------------------------------------------------------------- *)
(* The term "x equals y" is ``x = y``; Notice that type types of x and y are  *)
(* both the type variable 'a or alpha.                                        *)
(* -------------------------------------------------------------------------- *)
``x = y``;

(* -------------------------------------------------------------------------- *)
(* The term "forall x t is true" is ``!x.t``; Notice that x is polymorphic    *)
(* and t is bool.                                                             *)
(* -------------------------------------------------------------------------- *)
``!x.t``;

(* -------------------------------------------------------------------------- *)
(* The term "there exists an x such that t is true" is ``?x.t``; Again, x is  *)
(* polymorphic and t is a bool                                                *)
(* -------------------------------------------------------------------------- *)
``?x.t``;

(* -------------------------------------------------------------------------- *)
(* The term "an x such that t is true" is a eta expression whose value is     *)
(* some arbitrary value satisfying property t. It's represented as ``@x.t``;  *)
(* -------------------------------------------------------------------------- *)
``@x.t``;

(* -------------------------------------------------------------------------- *)
(* The conditional expression "if cond is true then t1 else t2" is            *)
(* written as ``if cond then t1 else t2``; Notice that cond's type must be    *)
(* boolean, whereas t1 and t2 have type alpha.                                *)
(* -------------------------------------------------------------------------- *)
``if cond then t1 else t2``; 