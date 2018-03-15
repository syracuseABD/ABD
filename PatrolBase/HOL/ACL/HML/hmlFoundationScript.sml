(* Hennessy-Milner Logic foundation by SK Chin 22 April 2012 *)

(* Interactive Mode
app load ["pred_setTheory","relationTheory"];
open pred_setTheory relationTheory;
*)
(* HML Syntax *)

structure hmlFoundationScript = struct

open HolKernel boolLib Parse; 
open bossLib pred_setTheory
relationTheory;

val _ = new_theory "hmlFoundation";

(* Syntax of HML *)
val _ = Hol_datatype
    `hmlForm = tt 
             | ff
             | andh of hmlForm => hmlForm 
             | orh of hmlForm => hmlForm
             | Box of 'action set => hmlForm
             | Dia of 'action set => hmlForm`;

(* make andh and orh infix operators *)
val _ = set_fixity "andh" (Infixr 580);
val _ = set_fixity "orh" (Infixr 570);


(* Semantics of hmsat *)
val _ = set_fixity "hmsat" (Infixr 540);

val hmsat_def =
    Define
    `((((E:'configuration),(Trans:'action -> 'configuration -> 'configuration -> bool)) hmsat tt) = T) /\
     ((((E:'configuration),(Trans:'action -> 'configuration -> 'configuration -> bool)) hmsat ff) = F) /\
     ((((E:'configuration),(Trans:'action -> 'configuration -> 'configuration -> bool)) hmsat 
      (f1:'action hmlForm) andh (f2:'action hmlForm)) = (((E,Trans) hmsat f1) /\ (((E,Trans) hmsat f2)))) /\
     ((((E:'configuration),(Trans:'action -> 'configuration -> 'configuration -> bool)) hmsat 
      (f1:'action hmlForm) orh (f2:'action hmlForm)) = (((E,Trans) hmsat f1) \/ (((E,Trans) hmsat f2)))) /\
     ((((E:'configuration),(Trans:'action -> 'configuration -> 'configuration -> bool)) hmsat 
      (Box (Actions:'action set)(f:'action hmlForm))) = 
      (!(E':'configuration)(a:'action).(Trans a E E') ==> ((a IN Actions) ==> ((E',Trans) hmsat f)))) /\
     ((((E:'configuration),(Trans:'action -> 'configuration -> 'configuration -> bool)) hmsat 
      (Dia (Actions:'action set)(f:'action hmlForm))) = 
      (?(E':'configuration)(a:'action).(Trans a E E') /\ ((a IN Actions) /\ ((E',Trans) hmsat f))))`; 

val _ = print_theory "-";
val _ = export_theory();

end;