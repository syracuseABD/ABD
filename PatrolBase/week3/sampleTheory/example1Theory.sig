signature example1Theory =
sig
  type thm = Thm.thm

  (*  Theorems  *)
    val demoTheorem : thm
    val prob1Theorem : thm

  val example1_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [indexedLists] Parent theory of "example1"

   [patternMatches] Parent theory of "example1"

   [demoTheorem]  Theorem

      |- ∀p q. p ⇒ (p ⇒ q) ⇒ q

   [prob1Theorem]  Theorem

      |- ∀p q. p ⇒ (p ⇒ q) ⇒ q


*)
end
