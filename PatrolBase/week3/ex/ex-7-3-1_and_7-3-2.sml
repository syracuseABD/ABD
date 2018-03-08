Create a function andImp2Imp term that operates on terms of the form p∧q ⊃ r and
returns p ⊃ q ⊃ r.

val impTerm = ``p /\ q ==> r``;
val (t1,t3) = dest_imp impTerm;
val (t11,t2) = dest_conj t1;
val t111 = mk_imp (t11,t2);
mk_imp (t111,t3);

fun andImp2Imp impTerm =
let
 val (t1,t3) = dest_imp impTerm
 val (t11,t2) = dest_conj t1
 val t111 = mk_imp (t11,t2)
in
 mk_imp (t111,t3)
end;



(* -------------------------------------------------------------------------- *)
(*  Test cases                                                                *)
(* -------------------------------------------------------------------------- *)

andImp2Imp `` ( p /\ q ) ==> r ``;





Exercise 7.3.2
Create a function impImpAnd term that operates on terms of the form
p ⊃ q ⊃ r and returns p∧q ⊃ r. Show that impImpAnd reverses the effects of
andImp2Imp, and vice verse.

val impTerm = ``p ==> q ==> r ``;
val (t1,backterm) = dest_imp impTerm;
val (t2,t3) = if (is_imp backterm) then (dest_imp backterm)
   else (dest_imp t1);
val t4 = if (is_imp backterm) then  (mk_conj (t1,t2))
   else (mk_conj (t2,t3));
if (is_imp backterm) then (mk_imp (t4,t3)) else mk_imp (t4, backterm);

fun impImpAnd impTerm2 =
let
 val (t1,backterm) = dest_imp impTerm2
 val (t2,t3) = if (is_imp backterm) then (dest_imp backterm) else (dest_imp t1)
 val t4 = if (is_imp backterm) then (mk_conj (t1,t2)) else (mk_conj (t2,t3))
in
 if (is_imp backterm) then (mk_imp (t4,t3)) else (mk_imp (t4, backterm))
end;


(* -------------------------------------------------------------------------- *)
(*  Test cases                                                                *)
(* -------------------------------------------------------------------------- *)

impImpAnd ``(p ==> q) ==> r ``;

impImpAnd ( andImp2Imp `` (p /\ q) ==> r ``) ;

andImp2Imp (impImpAnd `` p ==> q ==> r ``) ;