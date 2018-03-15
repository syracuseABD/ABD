(* a.c.l. foundation, with arithmetic expressions by skc 2/11/09 *)

(* a.c.l. foundation, mutilated by lm, now with curried J. 1/25/09 *)
(* now with eqp removed (see Access/Plotkin) 1/29/09 *)

(** ACCESS CONTROL LOGIC FOUNDATION in our textbook *)
(************************ 
* ACCESS CONTROL LOGIC FOUNDATION in our textbook
* The semantics of the logic is mainly built using Kripke structures.
* Sets Li, Ls of integrity and security labels (or levels)  are
* considered part of the syntax, and their partial orders Oi, Os are
* separate parameters of the semantics and of the derivation system.
* The components of the 
* Kripke structure <W, I, J, imap, smap>
* we use are:
* (1) W, a non-empty set of worlds,
* (2) I, an interpretation function mapping primitive propositions to the
*     sets of worlds where the propositions are true,
* (3) J, a function mapping principal expressions to relations on worlds,
* (4) imap, a function mapping each simple principal name
*     to an integrity level, and
* (5) smap, a function mapping each simple principal name
*     to a security level.
* **********************)

(***********************
* HOL IMPLEMENTATION APPROACH
* We introduce a Hol type Kripke that is parameterized on 
* a non-empty set of worlds of arbitrary type, a set of integrity
* levels of arbitrary type, and a set of security levels of arbitrary
* type. At the end of this theory, we define Kripke as follows:
* val _ = Hol_datatype 
*    `Kripke = KS of ('var -> ('world set)) =>
*                    ('pn -> ('world -> ('world set))) =>
*                    ('pn -> 'il) =>
*                    ('pn -> 'sl)`
* where:
* (1) 'world is a type variable for the type of possible worlds (note
*      that every type in Hol is non-empty),
* (2) 'var is a type variable for propositional variables,
* (3) 'pn a type variable for the type of simple principal names,
* (4) 'il is a type variable for the type of integrity levels, and
* (5) 'sl is a type variable for the type of security levels,
* 
* To accomplish the above we do the following in order:
* (1) define the type of partial orders, po
* (2) define the type of principal expressions, Princ
* (3) define the type of integrity level expressions, IntLevel,
* (4) define the type of security level expressions, SecLevel,
* (5) define the type of formulas, Form, and
* (6) define the type of Kripke structures, Kripke.
*************************)

(************************
* THE DEFINITIONS START HERE
************************)
(*
load "pred_setTheory";
load "relationTheory";
load "PairedLambda";
*)

structure aclfoundationScript =
struct

open HolKernel boolLib Parse;
open bossLib pred_setTheory relationTheory PairedLambda pairTheory oneTheory;

val _ = new_theory "aclfoundation";
(*********************
* DEFINE PARTIAL ORDER TYPE
* The "dominates" relation on security labels is a partial order (called a
* weak order in HOL - WeakOrder in relationTheory).  These relations are
* reflexive, antisymmetric, and transitive. What we want is a new type
* ('a)po, i.e., a type consisting of partial orderings on 'a.  
* We now obtain this as follows: **************************************)

(* (1) Use predicate WeakOrder to select partial orderings from relations
       of type 'a.
   (2) Prove that the new type is non-empty - this we do by showing $= is
       a partial order (EQ_WeakOrder), then existentially quantifying $=, 
       resulting in WeakOrder_Exists. *)

(* Show that $= satisfies WeakOrder, i.e., is a partial order *)
val EQ_WeakOrder = 
    store_thm("EQ_WeakOrder",
	Term `WeakOrder ($=)`,
	REWRITE_TAC
	(map (SPEC ``($=):('a->'a->bool)``) 
	[(INST_TYPE [Type`:'g` |-> Type `:'a`] WeakOrder), 
	 reflexive_def, antisymmetric_def,transitive_def]) THEN
  	PROVE_TAC []);

(* Show that partial orders exist *)
val WeakOrder_Exists =
    save_thm
    ("WeakOrder_Exists",
     (EXISTS (Term `?R.WeakOrder R`, Term `$=`) EQ_WeakOrder));

(* WeakOrder_Exists = |- ?R. WeakOrder R *)

(* (3) Define the new type ('a)po as a conservative extension to HOL by: *)

val po_type_definition = new_type_definition ("po",WeakOrder_Exists);

(*    which produces:
      val po_type_definition =
      |- ?(rep :'a po -> 'a -> 'a -> bool).
           TYPE_DEFINITION (WeakOrder :('a -> 'a -> bool) -> bool) rep *)

(* (4) Prove that ('a)po is isomorphic to the set of partial orderings
       using the ml function define_new_type_bijections. The mapping
       functions to and from ('a)po to 'a are the abstraction (constructor)
       and representation (destructor) functions PO and repPO. *)

val po_bij = save_thm ("po_bij",
     (define_new_type_bijections
      {name="po_tybij", ABS="PO", REP="repPO", tyax=po_type_definition}));

(* po_bij =
    |- (!a. PO (repPO a) = a) /\ !r. WeakOrder r = (repPO (PO r) = r) *)

(* (5)  Prove additional theorems about the type ('a)po as follows: *)
(* Show that the the construction of ('a)po is one-to-one, i.e., unique. *)
val abs_po11 = 
    save_thm
    ("abs_po11",
     (GEN_BETA_RULE (prove_abs_fn_one_one po_bij)));

(* abs_po11 =
 |- !r r'. WeakOrder r ==> WeakOrder r' ==> ((PO r = PO r') = (r = r')) *)

(* Show that every relation that is a partial order over 'a is in ('a)po *)
val onto_po = 
    save_thm
    ("onto_po",
     (prove_rep_fn_onto po_bij));

(* onto_po = |- !r. WeakOrder r = ?a. r = repPO a *)

(* Show that every member of ('a)po is constructed from a
   partial order over 'a *)
val absPO_fn_onto = 
    save_thm
    ("absPO_fn_onto",
     (prove_abs_fn_onto po_bij));

(*  absPO_fn_onto = |- !a. ?r. (a = PO r) /\ WeakOrder r *)

(* Get the explicit partial-order properties of the relation corresponding
   to anything of type ('a)po. *)
val [PO_repPO, WO_repPO] = map2 (fn x => fn y => save_thm (x, y))
                                ["PO_repPO", "WO_repPO"]
                                (CONJUNCTS po_bij);

(*  PO_repPO = |- !a. PO (repPO a)
    WO_repPO = |- !r. WeakOrder r = (repPO (PO r) = r) *)

val repPO_iPO_partial_order = save_thm ("repPO_iPO_partial_order",
    REWRITE_RULE 
    [(SPEC (Term`iPO:'a po`) PO_repPO),
     WeakOrder, reflexive_def, transitive_def, antisymmetric_def] 
    (SPEC (Term`(repPO iPO)`) WO_repPO));

(* repPO_iPO_partial_order =
    |- (!x. repPO iPO x x) /\
       (!x y. repPO iPO x y /\ repPO iPO y x ==> (x = y)) /\
       !x y z. repPO iPO x y /\ repPO iPO y z ==> repPO iPO x z *)


(***********************************************************************)
(* We now introduce (1) a trivial partial order, (2) the composition of*)
(* partial orders, and (3) show that subset is a partial order.  These *)
(* are used when creating a security and integrity levels using        *)
(* categories or compartments.                                         *)
(***********************************************************************)
(* First a trivial partial order, a product construction on partial
   orders, and definition of the superset partial order. *)

(***********************************************************************)
(* A partial order with one element: used for trivial orders if needed *)
(***********************************************************************)
val one_weakorder_def = Define`one_weakorder (x:one) (y:one) = T`;

val one_weakorder_WO = 
   store_thm 
   ("one_weakorder_WO", 
    Term `WeakOrder one_weakorder`,
    REWRITE_TAC 
    [one_weakorder_def, WeakOrder, reflexive_def, 
     transitive_def,antisymmetric_def] THEN 
    ONCE_REWRITE_TAC [one] THEN 
    REPEAT GEN_TAC THEN 
    REFL_TAC);

val O1_def =
    Define`O1 = PO one_weakorder`;

val repPO_O1 = 
   store_thm 
   ("repPO_O1", 
    Term`repPO O1 = one_weakorder`,
    REWRITE_TAC 
     [O1_def, po_bij,
      EQ_MP (ISPEC (Term`one_weakorder`) WO_repPO) one_weakorder_WO]);


(***********************************************************************)
(* We can create a partial order by composing two partial orders to    *)
(* to form a third.                                                    *)
(***********************************************************************)
(* RPROD, the product of two (Curried) binary relations, turns out to be
   already defined in pairTheory; it will be good style to use it. *)

(* RPROD_DEF = |- !R1 R2. RPROD R1 R2 = (\(s,t) (u,v). R1 s u /\ R2 t v) *)

val RPROD_THM = 
   store_thm 
   ("RPROD_THM", 
    Term`!r s a b:'x#'y. 
           RPROD r s a b = r (FST a) (FST b) /\ s (SND a) (SND b)`,
    REPEAT GEN_TAC THEN 
    REWRITE_TAC [RPROD_DEF] THEN 
    CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV (REWR_CONV (GSYM PAIR)))) THEN 
    CONV_TAC (DEPTH_CONV PAIRED_BETA_CONV) THEN REFL_TAC);

(* The following is perhaps a long-winded approach, but it seems
conceivably worth knowing that some individual properties of relations
are preserved by product: *)

val refl_prod_refl = 
   store_thm 
   ("refl_prod_refl", 
    Term`!r:'a->'a->bool s:'b->'b->bool.
          reflexive r /\ reflexive s ==> reflexive (RPROD r s)`,
    REPEAT GEN_TAC THEN 
    REWRITE_TAC [reflexive_def, RPROD_THM] THEN 
    CONV_TAC (DEPTH_CONV PAIRED_BETA_CONV) THEN 
    STRIP_TAC THEN ASM_REWRITE_TAC []);

val trans_prod_trans = 
   store_thm 
   ("trans_prod_trans", 
    Term`!r:'a->'a->bool s:'b->'b->bool.
          transitive r /\ transitive s ==> transitive (RPROD r s)`,
    REPEAT GEN_TAC THEN 
    REWRITE_TAC [transitive_def, RPROD_THM] THEN 
    REPEAT STRIP_TAC THEN RES_TAC);

val antisym_prod_antisym = 
   store_thm 
   ("antisym_prod_antisym", 
    Term`!r:'a->'a->bool s:'b->'b->bool.
          antisymmetric r /\ antisymmetric s ==> antisymmetric (RPROD r s)`,
    REPEAT GEN_TAC THEN 
    REWRITE_TAC [antisymmetric_def, RPROD_THM] THEN 
    ONCE_REWRITE_TAC [GSYM PAIR] THEN 
    ONCE_REWRITE_TAC [PAIR_EQ] THEN 
    REPEAT STRIP_TAC THEN 
    RES_TAC);

val WO_prod_WO = 
   store_thm 
   ("WO_prod_WO", 
    Term`!r:'a->'a->bool s:'b->'b->bool.
          WeakOrder r /\ WeakOrder s ==> WeakOrder (RPROD r s)`,
    REWRITE_TAC [WeakOrder] THEN 
    REPEAT STRIP_TAC THENL
    [MATCH_MP_TAC refl_prod_refl, 
     MATCH_MP_TAC antisym_prod_antisym,
     MATCH_MP_TAC trans_prod_trans] THEN 
    ASM_REWRITE_TAC []);

val prod_PO_def = 
   Define 
   `prod_PO (PO1:'a po) (PO2:'b po) = PO (RPROD (repPO PO1) (repPO PO2))`;

val repPO_prod_PO = 
   store_thm 
   ("repPO_prod_PO", 
    Term
    `!po1:'a po po2:'b po. 
      repPO (prod_PO po1 po2) = RPROD (repPO po1) (repPO po2)`,
    REPEAT GEN_TAC THEN 
    REWRITE_TAC [prod_PO_def, GSYM (CONJUNCT2 po_bij)] THEN 
    MATCH_MP_TAC WO_prod_WO THEN 
    REWRITE_TAC [WO_repPO, po_bij]);

(* Since inclusion is a weak order, we can define, for any type 'a,
   the partial order Subset_PO of type ('a -> bool) po. *)

val SUBSET_WO = 
   store_thm 
   ("SUBSET_WO", 
    Term `WeakOrder ($SUBSET:('a -> bool) -> ('a -> bool) -> bool)`,
    REWRITE_TAC 
    [WeakOrder, reflexive_def, antisymmetric_def, transitive_def, 
     SUBSET_REFL, SUBSET_ANTISYM, SUBSET_TRANS]);

val Subset_PO_def = 
   Define`Subset_PO:('a -> bool) po = PO $SUBSET`;

val repPO_Subset_PO = 
   store_thm 
   ("repPO_Subset_PO", 
    Term
    `repPO Subset_PO = $SUBSET:('a->bool) -> ('a->bool) -> bool`,
    REWRITE_TAC 
    [Subset_PO_def, po_bij,
     EQ_MP 
     (ISPEC 
      (Term`$SUBSET:('a->bool) -> ('a->bool) -> bool`) 
      WO_repPO)
     SUBSET_WO]);


(*******************************************************
 * Datatypes "Princ", "IntLevel", "SecLevel", and "Form"
 *******************************************************)

(* Initial a's on some type variables below are a Hol kludge to make the
   polymorphic types take their type parameters in the order we expect.*)

val _ = Hol_datatype 
    `Princ = Name of 'apn
           | meet of Princ => Princ
           | quoting of Princ => Princ;

     IntLevel = iLab of 'il
              | il of 'apn;

     SecLevel = sLab of 'sl
              | sl of 'apn`;

(* SKC: we add numerical expressions to Form 2/13/2009 *)
val _ = Hol_datatype
    `Form = TT
	  | FF
 	  | prop of 'aavar
          | notf of Form
          | andf of Form => Form
          | orf of Form => Form
          | impf of Form => Form
          | eqf of Form => Form
          | says of 'apn Princ => Form
          | speaks_for of 'apn Princ => 'apn Princ
          | controls of 'apn Princ => Form
	  | reps of 'apn Princ => 'apn Princ => Form
	  | domi of ('apn, 'il) IntLevel => ('apn, 'il) IntLevel
	  | eqi of ('apn, 'il) IntLevel => ('apn, 'il) IntLevel
	  | doms of ('apn, 'sl) SecLevel => ('apn, 'sl) SecLevel
	  | eqs of ('apn, 'sl) SecLevel => ('apn, 'sl) SecLevel
	  | eqn of num => num
	  | lte of num => num
	  | lt of num => num`;

(* Change "meet" and "quoting" to infix operators *)

val _ = set_fixity "meet" (Infixr 630);
val _ = set_fixity "quoting" (Infixr 620);

(* and the rest *)

val _ = set_fixity "andf" (Infixr 580);
val _ = set_fixity "orf" (Infixr 570);
val _ = set_fixity "impf" (Infixr 560);
val _ = set_fixity "eqf" (Infixr 550);
val _ = set_fixity "says" (Infixr 590);
val _ = set_fixity "speaks_for" (Infixr 615);
val _ = set_fixity "controls" (Infixr 590);
val _ = set_fixity "domi" (Infixr 590);
val _ = set_fixity "eqi" (Infixr 590);
val _ = set_fixity "doms" (Infixr 590);
val _ = set_fixity "eqs" (Infixr 590);
val _ = set_fixity "eqn" (Infixr 590);
val _ = set_fixity "lte" (Infixr 590);
val _ = set_fixity "lt" (Infixr 590);

(* We want eventually to show soundness: that every derivable formula of
 a.c.l. holds in every world of every Kripke structure M. But derivability
 is now to be parameterized by partial orders Oi and Os; these must then
 be separate parameters to the semantic function also, so that the notion
 "all Kripke structures" does not entail a free choice of what the partial
 orders are.

 Thus the new Kripke structure, besides its I and J components, has just 2
 mappings assigning integrity and security levels to the principal names.*)

val _ = Hol_datatype 
    `Kripke = KS of ('aavar -> ('aaworld set)) =>
    	      	    ('apn -> ('aaworld -> ('aaworld set))) =>
		    ('apn -> 'il) => ('apn -> 'sl)`;

(* type arguments to Kripke, in left-to-right order:
   propvar_type, world_type, princ_name_type, integ_type, sec_type *)

(**********
* accessor functions for Kripke structures
**********)
val intpKS_def =
    Define `intpKS(KS Intp Jfn ilmap slmap) = Intp`;

val jKS_def =
    Define `jKS(KS Intp Jfn ilmap slmap) = Jfn`;

val imapKS_def =
    Define `imapKS(KS Intp Jfn ilmap slmap) = ilmap`;

val smapKS_def =
    Define `smapKS(KS Intp Jfn ilmap slmap) = slmap`;

(*********
* properties of Kripke destructors
*********)

val KS_bij =
store_thm(
	"KS_bij",
	``!M.M = KS (intpKS M)(jKS M)(imapKS M)(smapKS M)``,
	Induct_on `M` THEN
	REWRITE_TAC [intpKS_def, jKS_def, imapKS_def, smapKS_def]);

val _ = export_theory();

end;

