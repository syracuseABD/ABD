signature ssm11Theory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val TR_def : thm
    val configuration_TY_DEF : thm
    val configuration_case_def : thm
    val configuration_size_def : thm
    val order_TY_DEF : thm
    val order_case_def : thm
    val order_size_def : thm
    val trType_TY_DEF : thm
    val trType_case_def : thm
    val trType_size_def : thm

  (*  Theorems  *)
    val CFGInterpret_def : thm
    val CFGInterpret_ind : thm
    val TR_EQ_rules_thm : thm
    val TR_cases : thm
    val TR_discard_cmd_rule : thm
    val TR_exec_cmd_rule : thm
    val TR_ind : thm
    val TR_rules : thm
    val TR_strongind : thm
    val TRrule0 : thm
    val TRrule1 : thm
    val configuration_11 : thm
    val configuration_Axiom : thm
    val configuration_case_cong : thm
    val configuration_induction : thm
    val configuration_nchotomy : thm
    val configuration_one_one : thm
    val datatype_configuration : thm
    val datatype_order : thm
    val datatype_trType : thm
    val order_11 : thm
    val order_Axiom : thm
    val order_case_cong : thm
    val order_distinct : thm
    val order_distinct_clauses : thm
    val order_induction : thm
    val order_nchotomy : thm
    val order_one_one : thm
    val trType_11 : thm
    val trType_Axiom : thm
    val trType_case_cong : thm
    val trType_distinct : thm
    val trType_distinct_clauses : thm
    val trType_induction : thm
    val trType_nchotomy : thm
    val trType_one_one : thm

  val ssm11_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [satList] Parent theory of "ssm11"

   [TR_def]  Definition

      |- TR =
         (λa0 a1 a2 a3.
            ∀TR'.
              (∀a0 a1 a2 a3.
                 (∃authenticationTest P NS M Oi Os Out s securityContext
                     stateInterp cmd ins outs.
                    (a0 = (M,Oi,Os)) ∧ (a1 = exec cmd) ∧
                    (a2 =
                     CFG authenticationTest stateInterp securityContext
                       (P says prop (SOME cmd)::ins) s outs) ∧
                    (a3 =
                     CFG authenticationTest stateInterp securityContext ins
                       (NS s (exec cmd)) (Out s (exec cmd)::outs)) ∧
                    authenticationTest (P says prop (SOME cmd)) ∧
                    CFGInterpret (M,Oi,Os)
                      (CFG authenticationTest stateInterp securityContext
                         (P says prop (SOME cmd)::ins) s outs)) ∨
                 (∃authenticationTest P NS M Oi Os Out s securityContext
                     stateInterp cmd ins outs.
                    (a0 = (M,Oi,Os)) ∧ (a1 = trap cmd) ∧
                    (a2 =
                     CFG authenticationTest stateInterp securityContext
                       (P says prop (SOME cmd)::ins) s outs) ∧
                    (a3 =
                     CFG authenticationTest stateInterp securityContext ins
                       (NS s (trap cmd)) (Out s (trap cmd)::outs)) ∧
                    authenticationTest (P says prop (SOME cmd)) ∧
                    CFGInterpret (M,Oi,Os)
                      (CFG authenticationTest stateInterp securityContext
                         (P says prop (SOME cmd)::ins) s outs)) ∨
                 (∃authenticationTest NS M Oi Os Out s securityContext
                     stateInterp cmd x ins outs.
                    (a0 = (M,Oi,Os)) ∧ (a1 = discard cmd) ∧
                    (a2 =
                     CFG authenticationTest stateInterp securityContext
                       (x::ins) s outs) ∧
                    (a3 =
                     CFG authenticationTest stateInterp securityContext ins
                       (NS s (discard cmd)) (Out s (discard cmd)::outs)) ∧
                    ¬authenticationTest x) ⇒
                 TR' a0 a1 a2 a3) ⇒
              TR' a0 a1 a2 a3)

   [configuration_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0'.
                ∀'configuration' .
                  (∀a0'.
                     (∃a0 a1 a2 a3 a4 a5.
                        a0' =
                        (λa0 a1 a2 a3 a4 a5.
                           ind_type$CONSTR 0 (a0,a1,a2,a3,a4,a5)
                             (λn. ind_type$BOTTOM)) a0 a1 a2 a3 a4 a5) ⇒
                     'configuration' a0') ⇒
                  'configuration' a0') rep

   [configuration_case_def]  Definition

      |- ∀a0 a1 a2 a3 a4 a5 f.
           configuration_CASE (CFG a0 a1 a2 a3 a4 a5) f =
           f a0 a1 a2 a3 a4 a5

   [configuration_size_def]  Definition

      |- ∀f f1 f2 f3 f4 f5 a0 a1 a2 a3 a4 a5.
           configuration_size f f1 f2 f3 f4 f5 (CFG a0 a1 a2 a3 a4 a5) =
           1 +
           (list_size (Form_size (order_size f) f4 f1 f2) a2 +
            (list_size (Form_size (order_size f) f4 f1 f2) a3 +
             (f5 a4 + list_size f3 a5)))

   [order_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0.
                ∀'order' .
                  (∀a0.
                     (∃a.
                        a0 =
                        (λa. ind_type$CONSTR 0 a (λn. ind_type$BOTTOM))
                          a) ∨
                     (a0 =
                      ind_type$CONSTR (SUC 0) ARB (λn. ind_type$BOTTOM)) ⇒
                     'order' a0) ⇒
                  'order' a0) rep

   [order_case_def]  Definition

      |- (∀a f v. order_CASE (SOME a) f v = f a) ∧
         ∀f v. order_CASE NONE f v = v

   [order_size_def]  Definition

      |- (∀f a. order_size f (SOME a) = 1 + f a) ∧
         ∀f. order_size f NONE = 0

   [trType_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0.
                ∀'trType' .
                  (∀a0.
                     (∃a.
                        a0 =
                        (λa. ind_type$CONSTR 0 a (λn. ind_type$BOTTOM))
                          a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR (SUC 0) a (λn. ind_type$BOTTOM))
                          a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR (SUC (SUC 0)) a
                             (λn. ind_type$BOTTOM)) a) ⇒
                     'trType' a0) ⇒
                  'trType' a0) rep

   [trType_case_def]  Definition

      |- (∀a f f1 f2. trType_CASE (discard a) f f1 f2 = f a) ∧
         (∀a f f1 f2. trType_CASE (trap a) f f1 f2 = f1 a) ∧
         ∀a f f1 f2. trType_CASE (exec a) f f1 f2 = f2 a

   [trType_size_def]  Definition

      |- (∀f a. trType_size f (discard a) = 1 + f a) ∧
         (∀f a. trType_size f (trap a) = 1 + f a) ∧
         ∀f a. trType_size f (exec a) = 1 + f a

   [CFGInterpret_def]  Theorem

      |- CFGInterpret (M,Oi,Os)
           (CFG authenticationTest stateInterp securityContext (input::ins)
              state outputStream) ⇔
         (M,Oi,Os) satList securityContext ∧ (M,Oi,Os) sat input ∧
         (M,Oi,Os) sat stateInterp state

   [CFGInterpret_ind]  Theorem

      |- ∀P.
           (∀M Oi Os authenticationTest stateInterp securityContext input
               ins state outputStream.
              P (M,Oi,Os)
                (CFG authenticationTest stateInterp securityContext
                   (input::ins) state outputStream)) ∧
           (∀v15 v10 v11 v12 v13 v14. P v15 (CFG v10 v11 v12 [] v13 v14)) ⇒
           ∀v v1 v2 v3. P (v,v1,v2) v3

   [TR_EQ_rules_thm]  Theorem

      |- (TR (M,Oi,Os) (exec cmd)
            (CFG authenticationTest stateInterp securityContext
               (P says prop (SOME cmd)::ins) s outs)
            (CFG authenticationTest stateInterp securityContext ins
               (NS s (exec cmd)) (Out s (exec cmd)::outs)) ⇔
          authenticationTest (P says prop (SOME cmd)) ∧
          CFGInterpret (M,Oi,Os)
            (CFG authenticationTest stateInterp securityContext
               (P says prop (SOME cmd)::ins) s outs)) ∧
         (TR (M,Oi,Os) (trap cmd)
            (CFG authenticationTest stateInterp securityContext
               (P says prop (SOME cmd)::ins) s outs)
            (CFG authenticationTest stateInterp securityContext ins
               (NS s (trap cmd)) (Out s (trap cmd)::outs)) ⇔
          authenticationTest (P says prop (SOME cmd)) ∧
          CFGInterpret (M,Oi,Os)
            (CFG authenticationTest stateInterp securityContext
               (P says prop (SOME cmd)::ins) s outs)) ∧
         (TR (M,Oi,Os) (discard cmd)
            (CFG authenticationTest stateInterp securityContext (x::ins) s
               outs)
            (CFG authenticationTest stateInterp securityContext ins
               (NS s (discard cmd)) (Out s (discard cmd)::outs)) ⇔
          ¬authenticationTest x)

   [TR_cases]  Theorem

      |- ∀a0 a1 a2 a3.
           TR a0 a1 a2 a3 ⇔
           (∃authenticationTest P NS M Oi Os Out s securityContext
               stateInterp cmd ins outs.
              (a0 = (M,Oi,Os)) ∧ (a1 = exec cmd) ∧
              (a2 =
               CFG authenticationTest stateInterp securityContext
                 (P says prop (SOME cmd)::ins) s outs) ∧
              (a3 =
               CFG authenticationTest stateInterp securityContext ins
                 (NS s (exec cmd)) (Out s (exec cmd)::outs)) ∧
              authenticationTest (P says prop (SOME cmd)) ∧
              CFGInterpret (M,Oi,Os)
                (CFG authenticationTest stateInterp securityContext
                   (P says prop (SOME cmd)::ins) s outs)) ∨
           (∃authenticationTest P NS M Oi Os Out s securityContext
               stateInterp cmd ins outs.
              (a0 = (M,Oi,Os)) ∧ (a1 = trap cmd) ∧
              (a2 =
               CFG authenticationTest stateInterp securityContext
                 (P says prop (SOME cmd)::ins) s outs) ∧
              (a3 =
               CFG authenticationTest stateInterp securityContext ins
                 (NS s (trap cmd)) (Out s (trap cmd)::outs)) ∧
              authenticationTest (P says prop (SOME cmd)) ∧
              CFGInterpret (M,Oi,Os)
                (CFG authenticationTest stateInterp securityContext
                   (P says prop (SOME cmd)::ins) s outs)) ∨
           ∃authenticationTest NS M Oi Os Out s securityContext stateInterp
              cmd x ins outs.
             (a0 = (M,Oi,Os)) ∧ (a1 = discard cmd) ∧
             (a2 =
              CFG authenticationTest stateInterp securityContext (x::ins) s
                outs) ∧
             (a3 =
              CFG authenticationTest stateInterp securityContext ins
                (NS s (discard cmd)) (Out s (discard cmd)::outs)) ∧
             ¬authenticationTest x

   [TR_discard_cmd_rule]  Theorem

      |- TR (M,Oi,Os) (discard cmd)
           (CFG authenticationTest stateInterp securityContext (x::ins) s
              outs)
           (CFG authenticationTest stateInterp securityContext ins
              (NS s (discard cmd)) (Out s (discard cmd)::outs)) ⇔
         ¬authenticationTest x

   [TR_exec_cmd_rule]  Theorem

      |- ∀authenticationTest securityContext stateInterp P cmd ins s outs.
           (∀M Oi Os.
              CFGInterpret (M,Oi,Os)
                (CFG authenticationTest stateInterp securityContext
                   (P says prop (SOME cmd)::ins) s outs) ⇒
              (M,Oi,Os) sat prop (SOME cmd)) ⇒
           ∀NS Out M Oi Os.
             TR (M,Oi,Os) (exec cmd)
               (CFG authenticationTest stateInterp securityContext
                  (P says prop (SOME cmd)::ins) s outs)
               (CFG authenticationTest stateInterp securityContext ins
                  (NS s (exec cmd)) (Out s (exec cmd)::outs)) ⇔
             authenticationTest (P says prop (SOME cmd)) ∧
             CFGInterpret (M,Oi,Os)
               (CFG authenticationTest stateInterp securityContext
                  (P says prop (SOME cmd)::ins) s outs) ∧
             (M,Oi,Os) sat prop (SOME cmd)

   [TR_ind]  Theorem

      |- ∀TR'.
           (∀authenticationTest P NS M Oi Os Out s securityContext
               stateInterp cmd ins outs.
              authenticationTest (P says prop (SOME cmd)) ∧
              CFGInterpret (M,Oi,Os)
                (CFG authenticationTest stateInterp securityContext
                   (P says prop (SOME cmd)::ins) s outs) ⇒
              TR' (M,Oi,Os) (exec cmd)
                (CFG authenticationTest stateInterp securityContext
                   (P says prop (SOME cmd)::ins) s outs)
                (CFG authenticationTest stateInterp securityContext ins
                   (NS s (exec cmd)) (Out s (exec cmd)::outs))) ∧
           (∀authenticationTest P NS M Oi Os Out s securityContext
               stateInterp cmd ins outs.
              authenticationTest (P says prop (SOME cmd)) ∧
              CFGInterpret (M,Oi,Os)
                (CFG authenticationTest stateInterp securityContext
                   (P says prop (SOME cmd)::ins) s outs) ⇒
              TR' (M,Oi,Os) (trap cmd)
                (CFG authenticationTest stateInterp securityContext
                   (P says prop (SOME cmd)::ins) s outs)
                (CFG authenticationTest stateInterp securityContext ins
                   (NS s (trap cmd)) (Out s (trap cmd)::outs))) ∧
           (∀authenticationTest NS M Oi Os Out s securityContext
               stateInterp cmd x ins outs.
              ¬authenticationTest x ⇒
              TR' (M,Oi,Os) (discard cmd)
                (CFG authenticationTest stateInterp securityContext
                   (x::ins) s outs)
                (CFG authenticationTest stateInterp securityContext ins
                   (NS s (discard cmd)) (Out s (discard cmd)::outs))) ⇒
           ∀a0 a1 a2 a3. TR a0 a1 a2 a3 ⇒ TR' a0 a1 a2 a3

   [TR_rules]  Theorem

      |- (∀authenticationTest P NS M Oi Os Out s securityContext
             stateInterp cmd ins outs.
            authenticationTest (P says prop (SOME cmd)) ∧
            CFGInterpret (M,Oi,Os)
              (CFG authenticationTest stateInterp securityContext
                 (P says prop (SOME cmd)::ins) s outs) ⇒
            TR (M,Oi,Os) (exec cmd)
              (CFG authenticationTest stateInterp securityContext
                 (P says prop (SOME cmd)::ins) s outs)
              (CFG authenticationTest stateInterp securityContext ins
                 (NS s (exec cmd)) (Out s (exec cmd)::outs))) ∧
         (∀authenticationTest P NS M Oi Os Out s securityContext
             stateInterp cmd ins outs.
            authenticationTest (P says prop (SOME cmd)) ∧
            CFGInterpret (M,Oi,Os)
              (CFG authenticationTest stateInterp securityContext
                 (P says prop (SOME cmd)::ins) s outs) ⇒
            TR (M,Oi,Os) (trap cmd)
              (CFG authenticationTest stateInterp securityContext
                 (P says prop (SOME cmd)::ins) s outs)
              (CFG authenticationTest stateInterp securityContext ins
                 (NS s (trap cmd)) (Out s (trap cmd)::outs))) ∧
         ∀authenticationTest NS M Oi Os Out s securityContext stateInterp
            cmd x ins outs.
           ¬authenticationTest x ⇒
           TR (M,Oi,Os) (discard cmd)
             (CFG authenticationTest stateInterp securityContext (x::ins) s
                outs)
             (CFG authenticationTest stateInterp securityContext ins
                (NS s (discard cmd)) (Out s (discard cmd)::outs))

   [TR_strongind]  Theorem

      |- ∀TR'.
           (∀authenticationTest P NS M Oi Os Out s securityContext
               stateInterp cmd ins outs.
              authenticationTest (P says prop (SOME cmd)) ∧
              CFGInterpret (M,Oi,Os)
                (CFG authenticationTest stateInterp securityContext
                   (P says prop (SOME cmd)::ins) s outs) ⇒
              TR' (M,Oi,Os) (exec cmd)
                (CFG authenticationTest stateInterp securityContext
                   (P says prop (SOME cmd)::ins) s outs)
                (CFG authenticationTest stateInterp securityContext ins
                   (NS s (exec cmd)) (Out s (exec cmd)::outs))) ∧
           (∀authenticationTest P NS M Oi Os Out s securityContext
               stateInterp cmd ins outs.
              authenticationTest (P says prop (SOME cmd)) ∧
              CFGInterpret (M,Oi,Os)
                (CFG authenticationTest stateInterp securityContext
                   (P says prop (SOME cmd)::ins) s outs) ⇒
              TR' (M,Oi,Os) (trap cmd)
                (CFG authenticationTest stateInterp securityContext
                   (P says prop (SOME cmd)::ins) s outs)
                (CFG authenticationTest stateInterp securityContext ins
                   (NS s (trap cmd)) (Out s (trap cmd)::outs))) ∧
           (∀authenticationTest NS M Oi Os Out s securityContext
               stateInterp cmd x ins outs.
              ¬authenticationTest x ⇒
              TR' (M,Oi,Os) (discard cmd)
                (CFG authenticationTest stateInterp securityContext
                   (x::ins) s outs)
                (CFG authenticationTest stateInterp securityContext ins
                   (NS s (discard cmd)) (Out s (discard cmd)::outs))) ⇒
           ∀a0 a1 a2 a3. TR a0 a1 a2 a3 ⇒ TR' a0 a1 a2 a3

   [TRrule0]  Theorem

      |- TR (M,Oi,Os) (exec cmd)
           (CFG authenticationTest stateInterp securityContext
              (P says prop (SOME cmd)::ins) s outs)
           (CFG authenticationTest stateInterp securityContext ins
              (NS s (exec cmd)) (Out s (exec cmd)::outs)) ⇔
         authenticationTest (P says prop (SOME cmd)) ∧
         CFGInterpret (M,Oi,Os)
           (CFG authenticationTest stateInterp securityContext
              (P says prop (SOME cmd)::ins) s outs)

   [TRrule1]  Theorem

      |- TR (M,Oi,Os) (trap cmd)
           (CFG authenticationTest stateInterp securityContext
              (P says prop (SOME cmd)::ins) s outs)
           (CFG authenticationTest stateInterp securityContext ins
              (NS s (trap cmd)) (Out s (trap cmd)::outs)) ⇔
         authenticationTest (P says prop (SOME cmd)) ∧
         CFGInterpret (M,Oi,Os)
           (CFG authenticationTest stateInterp securityContext
              (P says prop (SOME cmd)::ins) s outs)

   [configuration_11]  Theorem

      |- ∀a0 a1 a2 a3 a4 a5 a0' a1' a2' a3' a4' a5'.
           (CFG a0 a1 a2 a3 a4 a5 = CFG a0' a1' a2' a3' a4' a5') ⇔
           (a0 = a0') ∧ (a1 = a1') ∧ (a2 = a2') ∧ (a3 = a3') ∧ (a4 = a4') ∧
           (a5 = a5')

   [configuration_Axiom]  Theorem

      |- ∀f.
           ∃fn.
             ∀a0 a1 a2 a3 a4 a5.
               fn (CFG a0 a1 a2 a3 a4 a5) = f a0 a1 a2 a3 a4 a5

   [configuration_case_cong]  Theorem

      |- ∀M M' f.
           (M = M') ∧
           (∀a0 a1 a2 a3 a4 a5.
              (M' = CFG a0 a1 a2 a3 a4 a5) ⇒
              (f a0 a1 a2 a3 a4 a5 = f' a0 a1 a2 a3 a4 a5)) ⇒
           (configuration_CASE M f = configuration_CASE M' f')

   [configuration_induction]  Theorem

      |- ∀P. (∀f f0 l l0 s l1. P (CFG f f0 l l0 s l1)) ⇒ ∀c. P c

   [configuration_nchotomy]  Theorem

      |- ∀cc. ∃f f0 l l0 s l1. cc = CFG f f0 l l0 s l1

   [configuration_one_one]  Theorem

      |- ∀a0 a1 a2 a3 a4 a5 a0' a1' a2' a3' a4' a5'.
           (CFG a0 a1 a2 a3 a4 a5 = CFG a0' a1' a2' a3' a4' a5') ⇔
           (a0 = a0') ∧ (a1 = a1') ∧ (a2 = a2') ∧ (a3 = a3') ∧ (a4 = a4') ∧
           (a5 = a5')

   [datatype_configuration]  Theorem

      |- DATATYPE (configuration CFG)

   [datatype_order]  Theorem

      |- DATATYPE (order SOME NONE)

   [datatype_trType]  Theorem

      |- DATATYPE (trType discard trap exec)

   [order_11]  Theorem

      |- ∀a a'. (SOME a = SOME a') ⇔ (a = a')

   [order_Axiom]  Theorem

      |- ∀f0 f1. ∃fn. (∀a. fn (SOME a) = f0 a) ∧ (fn NONE = f1)

   [order_case_cong]  Theorem

      |- ∀M M' f v.
           (M = M') ∧ (∀a. (M' = SOME a) ⇒ (f a = f' a)) ∧
           ((M' = NONE) ⇒ (v = v')) ⇒
           (order_CASE M f v = order_CASE M' f' v')

   [order_distinct]  Theorem

      |- ∀a. SOME a ≠ NONE

   [order_distinct_clauses]  Theorem

      |- ∀a. SOME a ≠ NONE

   [order_induction]  Theorem

      |- ∀P. (∀c. P (SOME c)) ∧ P NONE ⇒ ∀ $o. P $o

   [order_nchotomy]  Theorem

      |- ∀oo. (∃c. oo = SOME c) ∨ (oo = NONE)

   [order_one_one]  Theorem

      |- ∀a a'. (SOME a = SOME a') ⇔ (a = a')

   [trType_11]  Theorem

      |- (∀a a'. (discard a = discard a') ⇔ (a = a')) ∧
         (∀a a'. (trap a = trap a') ⇔ (a = a')) ∧
         ∀a a'. (exec a = exec a') ⇔ (a = a')

   [trType_Axiom]  Theorem

      |- ∀f0 f1 f2.
           ∃fn.
             (∀a. fn (discard a) = f0 a) ∧ (∀a. fn (trap a) = f1 a) ∧
             ∀a. fn (exec a) = f2 a

   [trType_case_cong]  Theorem

      |- ∀M M' f f1 f2.
           (M = M') ∧ (∀a. (M' = discard a) ⇒ (f a = f' a)) ∧
           (∀a. (M' = trap a) ⇒ (f1 a = f1' a)) ∧
           (∀a. (M' = exec a) ⇒ (f2 a = f2' a)) ⇒
           (trType_CASE M f f1 f2 = trType_CASE M' f' f1' f2')

   [trType_distinct]  Theorem

      |- (∀a' a. discard a ≠ trap a') ∧ (∀a' a. discard a ≠ exec a') ∧
         ∀a' a. trap a ≠ exec a'

   [trType_distinct_clauses]  Theorem

      |- (∀a' a. discard a ≠ trap a') ∧ (∀a' a. discard a ≠ exec a') ∧
         ∀a' a. trap a ≠ exec a'

   [trType_induction]  Theorem

      |- ∀P.
           (∀c. P (discard c)) ∧ (∀c. P (trap c)) ∧ (∀c. P (exec c)) ⇒
           ∀t. P t

   [trType_nchotomy]  Theorem

      |- ∀tt. (∃c. tt = discard c) ∨ (∃c. tt = trap c) ∨ ∃c. tt = exec c

   [trType_one_one]  Theorem

      |- (∀a a'. (discard a = discard a') ⇔ (a = a')) ∧
         (∀a a'. (trap a = trap a') ⇔ (a = a')) ∧
         ∀a a'. (exec a = exec a') ⇔ (a = a')


*)
end
