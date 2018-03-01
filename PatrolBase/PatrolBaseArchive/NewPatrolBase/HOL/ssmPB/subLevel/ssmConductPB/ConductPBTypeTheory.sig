signature ConductPBTypeTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val plCommandPB_BIJ : thm
    val plCommandPB_CASE : thm
    val plCommandPB_TY_DEF : thm
    val plCommandPB_size_def : thm
    val psgCommandPB_BIJ : thm
    val psgCommandPB_CASE : thm
    val psgCommandPB_TY_DEF : thm
    val psgCommandPB_size_def : thm
    val slCommand_TY_DEF : thm
    val slCommand_case_def : thm
    val slCommand_size_def : thm
    val slOutput_BIJ : thm
    val slOutput_CASE : thm
    val slOutput_TY_DEF : thm
    val slOutput_size_def : thm
    val slState_BIJ : thm
    val slState_CASE : thm
    val slState_TY_DEF : thm
    val slState_size_def : thm
    val stateRole_BIJ : thm
    val stateRole_CASE : thm
    val stateRole_TY_DEF : thm
    val stateRole_size_def : thm

  (*  Theorems  *)
    val datatype_plCommandPB : thm
    val datatype_psgCommandPB : thm
    val datatype_slCommand : thm
    val datatype_slOutput : thm
    val datatype_slState : thm
    val datatype_stateRole : thm
    val num2plCommandPB_11 : thm
    val num2plCommandPB_ONTO : thm
    val num2plCommandPB_plCommandPB2num : thm
    val num2plCommandPB_thm : thm
    val num2psgCommandPB_11 : thm
    val num2psgCommandPB_ONTO : thm
    val num2psgCommandPB_psgCommandPB2num : thm
    val num2psgCommandPB_thm : thm
    val num2slOutput_11 : thm
    val num2slOutput_ONTO : thm
    val num2slOutput_slOutput2num : thm
    val num2slOutput_thm : thm
    val num2slState_11 : thm
    val num2slState_ONTO : thm
    val num2slState_slState2num : thm
    val num2slState_thm : thm
    val num2stateRole_11 : thm
    val num2stateRole_ONTO : thm
    val num2stateRole_stateRole2num : thm
    val num2stateRole_thm : thm
    val plCommandPB2num_11 : thm
    val plCommandPB2num_ONTO : thm
    val plCommandPB2num_num2plCommandPB : thm
    val plCommandPB2num_thm : thm
    val plCommandPB_Axiom : thm
    val plCommandPB_EQ_plCommandPB : thm
    val plCommandPB_case_cong : thm
    val plCommandPB_case_def : thm
    val plCommandPB_distinct : thm
    val plCommandPB_distinct_clauses : thm
    val plCommandPB_induction : thm
    val plCommandPB_nchotomy : thm
    val psgCommandPB2num_11 : thm
    val psgCommandPB2num_ONTO : thm
    val psgCommandPB2num_num2psgCommandPB : thm
    val psgCommandPB2num_thm : thm
    val psgCommandPB_Axiom : thm
    val psgCommandPB_EQ_psgCommandPB : thm
    val psgCommandPB_case_cong : thm
    val psgCommandPB_case_def : thm
    val psgCommandPB_distinct : thm
    val psgCommandPB_distinct_clauses : thm
    val psgCommandPB_induction : thm
    val psgCommandPB_nchotomy : thm
    val slCommand_11 : thm
    val slCommand_Axiom : thm
    val slCommand_case_cong : thm
    val slCommand_distinct : thm
    val slCommand_distinct_clauses : thm
    val slCommand_induction : thm
    val slCommand_nchotomy : thm
    val slCommand_one_one : thm
    val slOutput2num_11 : thm
    val slOutput2num_ONTO : thm
    val slOutput2num_num2slOutput : thm
    val slOutput2num_thm : thm
    val slOutput_Axiom : thm
    val slOutput_EQ_slOutput : thm
    val slOutput_case_cong : thm
    val slOutput_case_def : thm
    val slOutput_distinct : thm
    val slOutput_distinct_clauses : thm
    val slOutput_induction : thm
    val slOutput_nchotomy : thm
    val slRole_distinct_clauses : thm
    val slState2num_11 : thm
    val slState2num_ONTO : thm
    val slState2num_num2slState : thm
    val slState2num_thm : thm
    val slState_Axiom : thm
    val slState_EQ_slState : thm
    val slState_case_cong : thm
    val slState_case_def : thm
    val slState_distinct : thm
    val slState_distinct_clauses : thm
    val slState_induction : thm
    val slState_nchotomy : thm
    val stateRole2num_11 : thm
    val stateRole2num_ONTO : thm
    val stateRole2num_num2stateRole : thm
    val stateRole2num_thm : thm
    val stateRole_Axiom : thm
    val stateRole_EQ_stateRole : thm
    val stateRole_case_cong : thm
    val stateRole_case_def : thm
    val stateRole_distinct : thm
    val stateRole_induction : thm
    val stateRole_nchotomy : thm

  val ConductPBType_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [indexedLists] Parent theory of "ConductPBType"

   [patternMatches] Parent theory of "ConductPBType"

   [plCommandPB_BIJ]  Definition

      |- (∀a. num2plCommandPB (plCommandPB2num a) = a) ∧
         ∀r. (λn. n < 4) r ⇔ (plCommandPB2num (num2plCommandPB r) = r)

   [plCommandPB_CASE]  Definition

      |- ∀x v0 v1 v2 v3.
           (case x of
              securePB => v0
            | withdrawPB => v1
            | completePB => v2
            | plIncompletePB => v3) =
           (λm.
              if m < 1 then v0
              else if m < 2 then v1
              else if m = 2 then v2
              else v3) (plCommandPB2num x)

   [plCommandPB_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 4) rep

   [plCommandPB_size_def]  Definition

      |- ∀x. plCommandPB_size x = 0

   [psgCommandPB_BIJ]  Definition

      |- (∀a. num2psgCommandPB (psgCommandPB2num a) = a) ∧
         ∀r. (λn. n < 2) r ⇔ (psgCommandPB2num (num2psgCommandPB r) = r)

   [psgCommandPB_CASE]  Definition

      |- ∀x v0 v1.
           (case x of actionsInPB => v0 | psgIncompletePB => v1) =
           (λm. if m = 0 then v0 else v1) (psgCommandPB2num x)

   [psgCommandPB_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 2) rep

   [psgCommandPB_size_def]  Definition

      |- ∀x. psgCommandPB_size x = 0

   [slCommand_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0.
                ∀'slCommand' .
                  (∀a0.
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR 0 (a,ARB) (λn. ind_type$BOTTOM))
                          a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR (SUC 0) (ARB,a)
                             (λn. ind_type$BOTTOM)) a) ⇒
                     'slCommand' a0) ⇒
                  'slCommand' a0) rep

   [slCommand_case_def]  Definition

      |- (∀a f f1. slCommand_CASE (PL a) f f1 = f a) ∧
         ∀a f f1. slCommand_CASE (PSG a) f f1 = f1 a

   [slCommand_size_def]  Definition

      |- (∀a. slCommand_size (PL a) = 1 + plCommandPB_size a) ∧
         ∀a. slCommand_size (PSG a) = 1 + psgCommandPB_size a

   [slOutput_BIJ]  Definition

      |- (∀a. num2slOutput (slOutput2num a) = a) ∧
         ∀r. (λn. n < 7) r ⇔ (slOutput2num (num2slOutput r) = r)

   [slOutput_CASE]  Definition

      |- ∀x v0 v1 v2 v3 v4 v5 v6.
           (case x of
              ConductPB => v0
            | SecurePB => v1
            | ActionsInPB => v2
            | WithdrawPB => v3
            | CompletePB => v4
            | unAuthenticated => v5
            | unAuthorized => v6) =
           (λm.
              if m < 3 then if m < 1 then v0 else if m = 1 then v1 else v2
              else if m < 4 then v3
              else if m < 5 then v4
              else if m = 5 then v5
              else v6) (slOutput2num x)

   [slOutput_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 7) rep

   [slOutput_size_def]  Definition

      |- ∀x. slOutput_size x = 0

   [slState_BIJ]  Definition

      |- (∀a. num2slState (slState2num a) = a) ∧
         ∀r. (λn. n < 5) r ⇔ (slState2num (num2slState r) = r)

   [slState_CASE]  Definition

      |- ∀x v0 v1 v2 v3 v4.
           (case x of
              CONDUCT_PB => v0
            | SECURE_PB => v1
            | ACTIONS_IN_PB => v2
            | WITHDRAW_PB => v3
            | COMPLETE_PB => v4) =
           (λm.
              if m < 2 then if m = 0 then v0 else v1
              else if m < 3 then v2
              else if m = 3 then v3
              else v4) (slState2num x)

   [slState_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 5) rep

   [slState_size_def]  Definition

      |- ∀x. slState_size x = 0

   [stateRole_BIJ]  Definition

      |- (∀a. num2stateRole (stateRole2num a) = a) ∧
         ∀r. (λn. n < 2) r ⇔ (stateRole2num (num2stateRole r) = r)

   [stateRole_CASE]  Definition

      |- ∀x v0 v1.
           (case x of PlatoonLeader => v0 | PlatoonSergeant => v1) =
           (λm. if m = 0 then v0 else v1) (stateRole2num x)

   [stateRole_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 2) rep

   [stateRole_size_def]  Definition

      |- ∀x. stateRole_size x = 0

   [datatype_plCommandPB]  Theorem

      |- DATATYPE
           (plCommandPB securePB withdrawPB completePB plIncompletePB)

   [datatype_psgCommandPB]  Theorem

      |- DATATYPE (psgCommandPB actionsInPB psgIncompletePB)

   [datatype_slCommand]  Theorem

      |- DATATYPE (slCommand PL PSG)

   [datatype_slOutput]  Theorem

      |- DATATYPE
           (slOutput ConductPB SecurePB ActionsInPB WithdrawPB CompletePB
              unAuthenticated unAuthorized)

   [datatype_slState]  Theorem

      |- DATATYPE
           (slState CONDUCT_PB SECURE_PB ACTIONS_IN_PB WITHDRAW_PB
              COMPLETE_PB)

   [datatype_stateRole]  Theorem

      |- DATATYPE (stateRole PlatoonLeader PlatoonSergeant)

   [num2plCommandPB_11]  Theorem

      |- ∀r r'.
           r < 4 ⇒
           r' < 4 ⇒
           ((num2plCommandPB r = num2plCommandPB r') ⇔ (r = r'))

   [num2plCommandPB_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2plCommandPB r) ∧ r < 4

   [num2plCommandPB_plCommandPB2num]  Theorem

      |- ∀a. num2plCommandPB (plCommandPB2num a) = a

   [num2plCommandPB_thm]  Theorem

      |- (num2plCommandPB 0 = securePB) ∧
         (num2plCommandPB 1 = withdrawPB) ∧
         (num2plCommandPB 2 = completePB) ∧
         (num2plCommandPB 3 = plIncompletePB)

   [num2psgCommandPB_11]  Theorem

      |- ∀r r'.
           r < 2 ⇒
           r' < 2 ⇒
           ((num2psgCommandPB r = num2psgCommandPB r') ⇔ (r = r'))

   [num2psgCommandPB_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2psgCommandPB r) ∧ r < 2

   [num2psgCommandPB_psgCommandPB2num]  Theorem

      |- ∀a. num2psgCommandPB (psgCommandPB2num a) = a

   [num2psgCommandPB_thm]  Theorem

      |- (num2psgCommandPB 0 = actionsInPB) ∧
         (num2psgCommandPB 1 = psgIncompletePB)

   [num2slOutput_11]  Theorem

      |- ∀r r'.
           r < 7 ⇒ r' < 7 ⇒ ((num2slOutput r = num2slOutput r') ⇔ (r = r'))

   [num2slOutput_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2slOutput r) ∧ r < 7

   [num2slOutput_slOutput2num]  Theorem

      |- ∀a. num2slOutput (slOutput2num a) = a

   [num2slOutput_thm]  Theorem

      |- (num2slOutput 0 = ConductPB) ∧ (num2slOutput 1 = SecurePB) ∧
         (num2slOutput 2 = ActionsInPB) ∧ (num2slOutput 3 = WithdrawPB) ∧
         (num2slOutput 4 = CompletePB) ∧
         (num2slOutput 5 = unAuthenticated) ∧
         (num2slOutput 6 = unAuthorized)

   [num2slState_11]  Theorem

      |- ∀r r'.
           r < 5 ⇒ r' < 5 ⇒ ((num2slState r = num2slState r') ⇔ (r = r'))

   [num2slState_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2slState r) ∧ r < 5

   [num2slState_slState2num]  Theorem

      |- ∀a. num2slState (slState2num a) = a

   [num2slState_thm]  Theorem

      |- (num2slState 0 = CONDUCT_PB) ∧ (num2slState 1 = SECURE_PB) ∧
         (num2slState 2 = ACTIONS_IN_PB) ∧ (num2slState 3 = WITHDRAW_PB) ∧
         (num2slState 4 = COMPLETE_PB)

   [num2stateRole_11]  Theorem

      |- ∀r r'.
           r < 2 ⇒
           r' < 2 ⇒
           ((num2stateRole r = num2stateRole r') ⇔ (r = r'))

   [num2stateRole_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2stateRole r) ∧ r < 2

   [num2stateRole_stateRole2num]  Theorem

      |- ∀a. num2stateRole (stateRole2num a) = a

   [num2stateRole_thm]  Theorem

      |- (num2stateRole 0 = PlatoonLeader) ∧
         (num2stateRole 1 = PlatoonSergeant)

   [plCommandPB2num_11]  Theorem

      |- ∀a a'. (plCommandPB2num a = plCommandPB2num a') ⇔ (a = a')

   [plCommandPB2num_ONTO]  Theorem

      |- ∀r. r < 4 ⇔ ∃a. r = plCommandPB2num a

   [plCommandPB2num_num2plCommandPB]  Theorem

      |- ∀r. r < 4 ⇔ (plCommandPB2num (num2plCommandPB r) = r)

   [plCommandPB2num_thm]  Theorem

      |- (plCommandPB2num securePB = 0) ∧
         (plCommandPB2num withdrawPB = 1) ∧
         (plCommandPB2num completePB = 2) ∧
         (plCommandPB2num plIncompletePB = 3)

   [plCommandPB_Axiom]  Theorem

      |- ∀x0 x1 x2 x3.
           ∃f.
             (f securePB = x0) ∧ (f withdrawPB = x1) ∧
             (f completePB = x2) ∧ (f plIncompletePB = x3)

   [plCommandPB_EQ_plCommandPB]  Theorem

      |- ∀a a'. (a = a') ⇔ (plCommandPB2num a = plCommandPB2num a')

   [plCommandPB_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3.
           (M = M') ∧ ((M' = securePB) ⇒ (v0 = v0')) ∧
           ((M' = withdrawPB) ⇒ (v1 = v1')) ∧
           ((M' = completePB) ⇒ (v2 = v2')) ∧
           ((M' = plIncompletePB) ⇒ (v3 = v3')) ⇒
           ((case M of
               securePB => v0
             | withdrawPB => v1
             | completePB => v2
             | plIncompletePB => v3) =
            case M' of
              securePB => v0'
            | withdrawPB => v1'
            | completePB => v2'
            | plIncompletePB => v3')

   [plCommandPB_case_def]  Theorem

      |- (∀v0 v1 v2 v3.
            (case securePB of
               securePB => v0
             | withdrawPB => v1
             | completePB => v2
             | plIncompletePB => v3) =
            v0) ∧
         (∀v0 v1 v2 v3.
            (case withdrawPB of
               securePB => v0
             | withdrawPB => v1
             | completePB => v2
             | plIncompletePB => v3) =
            v1) ∧
         (∀v0 v1 v2 v3.
            (case completePB of
               securePB => v0
             | withdrawPB => v1
             | completePB => v2
             | plIncompletePB => v3) =
            v2) ∧
         ∀v0 v1 v2 v3.
           (case plIncompletePB of
              securePB => v0
            | withdrawPB => v1
            | completePB => v2
            | plIncompletePB => v3) =
           v3

   [plCommandPB_distinct]  Theorem

      |- securePB ≠ withdrawPB ∧ securePB ≠ completePB ∧
         securePB ≠ plIncompletePB ∧ withdrawPB ≠ completePB ∧
         withdrawPB ≠ plIncompletePB ∧ completePB ≠ plIncompletePB

   [plCommandPB_distinct_clauses]  Theorem

      |- securePB ≠ withdrawPB ∧ securePB ≠ completePB ∧
         securePB ≠ plIncompletePB ∧ withdrawPB ≠ completePB ∧
         withdrawPB ≠ plIncompletePB ∧ completePB ≠ plIncompletePB

   [plCommandPB_induction]  Theorem

      |- ∀P.
           P completePB ∧ P plIncompletePB ∧ P securePB ∧ P withdrawPB ⇒
           ∀a. P a

   [plCommandPB_nchotomy]  Theorem

      |- ∀a.
           (a = securePB) ∨ (a = withdrawPB) ∨ (a = completePB) ∨
           (a = plIncompletePB)

   [psgCommandPB2num_11]  Theorem

      |- ∀a a'. (psgCommandPB2num a = psgCommandPB2num a') ⇔ (a = a')

   [psgCommandPB2num_ONTO]  Theorem

      |- ∀r. r < 2 ⇔ ∃a. r = psgCommandPB2num a

   [psgCommandPB2num_num2psgCommandPB]  Theorem

      |- ∀r. r < 2 ⇔ (psgCommandPB2num (num2psgCommandPB r) = r)

   [psgCommandPB2num_thm]  Theorem

      |- (psgCommandPB2num actionsInPB = 0) ∧
         (psgCommandPB2num psgIncompletePB = 1)

   [psgCommandPB_Axiom]  Theorem

      |- ∀x0 x1. ∃f. (f actionsInPB = x0) ∧ (f psgIncompletePB = x1)

   [psgCommandPB_EQ_psgCommandPB]  Theorem

      |- ∀a a'. (a = a') ⇔ (psgCommandPB2num a = psgCommandPB2num a')

   [psgCommandPB_case_cong]  Theorem

      |- ∀M M' v0 v1.
           (M = M') ∧ ((M' = actionsInPB) ⇒ (v0 = v0')) ∧
           ((M' = psgIncompletePB) ⇒ (v1 = v1')) ⇒
           ((case M of actionsInPB => v0 | psgIncompletePB => v1) =
            case M' of actionsInPB => v0' | psgIncompletePB => v1')

   [psgCommandPB_case_def]  Theorem

      |- (∀v0 v1.
            (case actionsInPB of
               actionsInPB => v0
             | psgIncompletePB => v1) =
            v0) ∧
         ∀v0 v1.
           (case psgIncompletePB of
              actionsInPB => v0
            | psgIncompletePB => v1) =
           v1

   [psgCommandPB_distinct]  Theorem

      |- actionsInPB ≠ psgIncompletePB

   [psgCommandPB_distinct_clauses]  Theorem

      |- actionsInPB ≠ psgIncompletePB

   [psgCommandPB_induction]  Theorem

      |- ∀P. P actionsInPB ∧ P psgIncompletePB ⇒ ∀a. P a

   [psgCommandPB_nchotomy]  Theorem

      |- ∀a. (a = actionsInPB) ∨ (a = psgIncompletePB)

   [slCommand_11]  Theorem

      |- (∀a a'. (PL a = PL a') ⇔ (a = a')) ∧
         ∀a a'. (PSG a = PSG a') ⇔ (a = a')

   [slCommand_Axiom]  Theorem

      |- ∀f0 f1. ∃fn. (∀a. fn (PL a) = f0 a) ∧ ∀a. fn (PSG a) = f1 a

   [slCommand_case_cong]  Theorem

      |- ∀M M' f f1.
           (M = M') ∧ (∀a. (M' = PL a) ⇒ (f a = f' a)) ∧
           (∀a. (M' = PSG a) ⇒ (f1 a = f1' a)) ⇒
           (slCommand_CASE M f f1 = slCommand_CASE M' f' f1')

   [slCommand_distinct]  Theorem

      |- ∀a' a. PL a ≠ PSG a'

   [slCommand_distinct_clauses]  Theorem

      |- ∀a' a. PL a ≠ PSG a'

   [slCommand_induction]  Theorem

      |- ∀P. (∀p. P (PL p)) ∧ (∀p. P (PSG p)) ⇒ ∀s. P s

   [slCommand_nchotomy]  Theorem

      |- ∀ss. (∃p. ss = PL p) ∨ ∃p. ss = PSG p

   [slCommand_one_one]  Theorem

      |- (∀a a'. (PL a = PL a') ⇔ (a = a')) ∧
         ∀a a'. (PSG a = PSG a') ⇔ (a = a')

   [slOutput2num_11]  Theorem

      |- ∀a a'. (slOutput2num a = slOutput2num a') ⇔ (a = a')

   [slOutput2num_ONTO]  Theorem

      |- ∀r. r < 7 ⇔ ∃a. r = slOutput2num a

   [slOutput2num_num2slOutput]  Theorem

      |- ∀r. r < 7 ⇔ (slOutput2num (num2slOutput r) = r)

   [slOutput2num_thm]  Theorem

      |- (slOutput2num ConductPB = 0) ∧ (slOutput2num SecurePB = 1) ∧
         (slOutput2num ActionsInPB = 2) ∧ (slOutput2num WithdrawPB = 3) ∧
         (slOutput2num CompletePB = 4) ∧
         (slOutput2num unAuthenticated = 5) ∧
         (slOutput2num unAuthorized = 6)

   [slOutput_Axiom]  Theorem

      |- ∀x0 x1 x2 x3 x4 x5 x6.
           ∃f.
             (f ConductPB = x0) ∧ (f SecurePB = x1) ∧
             (f ActionsInPB = x2) ∧ (f WithdrawPB = x3) ∧
             (f CompletePB = x4) ∧ (f unAuthenticated = x5) ∧
             (f unAuthorized = x6)

   [slOutput_EQ_slOutput]  Theorem

      |- ∀a a'. (a = a') ⇔ (slOutput2num a = slOutput2num a')

   [slOutput_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3 v4 v5 v6.
           (M = M') ∧ ((M' = ConductPB) ⇒ (v0 = v0')) ∧
           ((M' = SecurePB) ⇒ (v1 = v1')) ∧
           ((M' = ActionsInPB) ⇒ (v2 = v2')) ∧
           ((M' = WithdrawPB) ⇒ (v3 = v3')) ∧
           ((M' = CompletePB) ⇒ (v4 = v4')) ∧
           ((M' = unAuthenticated) ⇒ (v5 = v5')) ∧
           ((M' = unAuthorized) ⇒ (v6 = v6')) ⇒
           ((case M of
               ConductPB => v0
             | SecurePB => v1
             | ActionsInPB => v2
             | WithdrawPB => v3
             | CompletePB => v4
             | unAuthenticated => v5
             | unAuthorized => v6) =
            case M' of
              ConductPB => v0'
            | SecurePB => v1'
            | ActionsInPB => v2'
            | WithdrawPB => v3'
            | CompletePB => v4'
            | unAuthenticated => v5'
            | unAuthorized => v6')

   [slOutput_case_def]  Theorem

      |- (∀v0 v1 v2 v3 v4 v5 v6.
            (case ConductPB of
               ConductPB => v0
             | SecurePB => v1
             | ActionsInPB => v2
             | WithdrawPB => v3
             | CompletePB => v4
             | unAuthenticated => v5
             | unAuthorized => v6) =
            v0) ∧
         (∀v0 v1 v2 v3 v4 v5 v6.
            (case SecurePB of
               ConductPB => v0
             | SecurePB => v1
             | ActionsInPB => v2
             | WithdrawPB => v3
             | CompletePB => v4
             | unAuthenticated => v5
             | unAuthorized => v6) =
            v1) ∧
         (∀v0 v1 v2 v3 v4 v5 v6.
            (case ActionsInPB of
               ConductPB => v0
             | SecurePB => v1
             | ActionsInPB => v2
             | WithdrawPB => v3
             | CompletePB => v4
             | unAuthenticated => v5
             | unAuthorized => v6) =
            v2) ∧
         (∀v0 v1 v2 v3 v4 v5 v6.
            (case WithdrawPB of
               ConductPB => v0
             | SecurePB => v1
             | ActionsInPB => v2
             | WithdrawPB => v3
             | CompletePB => v4
             | unAuthenticated => v5
             | unAuthorized => v6) =
            v3) ∧
         (∀v0 v1 v2 v3 v4 v5 v6.
            (case CompletePB of
               ConductPB => v0
             | SecurePB => v1
             | ActionsInPB => v2
             | WithdrawPB => v3
             | CompletePB => v4
             | unAuthenticated => v5
             | unAuthorized => v6) =
            v4) ∧
         (∀v0 v1 v2 v3 v4 v5 v6.
            (case unAuthenticated of
               ConductPB => v0
             | SecurePB => v1
             | ActionsInPB => v2
             | WithdrawPB => v3
             | CompletePB => v4
             | unAuthenticated => v5
             | unAuthorized => v6) =
            v5) ∧
         ∀v0 v1 v2 v3 v4 v5 v6.
           (case unAuthorized of
              ConductPB => v0
            | SecurePB => v1
            | ActionsInPB => v2
            | WithdrawPB => v3
            | CompletePB => v4
            | unAuthenticated => v5
            | unAuthorized => v6) =
           v6

   [slOutput_distinct]  Theorem

      |- ConductPB ≠ SecurePB ∧ ConductPB ≠ ActionsInPB ∧
         ConductPB ≠ WithdrawPB ∧ ConductPB ≠ CompletePB ∧
         ConductPB ≠ unAuthenticated ∧ ConductPB ≠ unAuthorized ∧
         SecurePB ≠ ActionsInPB ∧ SecurePB ≠ WithdrawPB ∧
         SecurePB ≠ CompletePB ∧ SecurePB ≠ unAuthenticated ∧
         SecurePB ≠ unAuthorized ∧ ActionsInPB ≠ WithdrawPB ∧
         ActionsInPB ≠ CompletePB ∧ ActionsInPB ≠ unAuthenticated ∧
         ActionsInPB ≠ unAuthorized ∧ WithdrawPB ≠ CompletePB ∧
         WithdrawPB ≠ unAuthenticated ∧ WithdrawPB ≠ unAuthorized ∧
         CompletePB ≠ unAuthenticated ∧ CompletePB ≠ unAuthorized ∧
         unAuthenticated ≠ unAuthorized

   [slOutput_distinct_clauses]  Theorem

      |- ConductPB ≠ SecurePB ∧ ConductPB ≠ ActionsInPB ∧
         ConductPB ≠ WithdrawPB ∧ ConductPB ≠ CompletePB ∧
         ConductPB ≠ unAuthenticated ∧ ConductPB ≠ unAuthorized ∧
         SecurePB ≠ ActionsInPB ∧ SecurePB ≠ WithdrawPB ∧
         SecurePB ≠ CompletePB ∧ SecurePB ≠ unAuthenticated ∧
         SecurePB ≠ unAuthorized ∧ ActionsInPB ≠ WithdrawPB ∧
         ActionsInPB ≠ CompletePB ∧ ActionsInPB ≠ unAuthenticated ∧
         ActionsInPB ≠ unAuthorized ∧ WithdrawPB ≠ CompletePB ∧
         WithdrawPB ≠ unAuthenticated ∧ WithdrawPB ≠ unAuthorized ∧
         CompletePB ≠ unAuthenticated ∧ CompletePB ≠ unAuthorized ∧
         unAuthenticated ≠ unAuthorized

   [slOutput_induction]  Theorem

      |- ∀P.
           P ActionsInPB ∧ P CompletePB ∧ P ConductPB ∧ P SecurePB ∧
           P WithdrawPB ∧ P unAuthenticated ∧ P unAuthorized ⇒
           ∀a. P a

   [slOutput_nchotomy]  Theorem

      |- ∀a.
           (a = ConductPB) ∨ (a = SecurePB) ∨ (a = ActionsInPB) ∨
           (a = WithdrawPB) ∨ (a = CompletePB) ∨ (a = unAuthenticated) ∨
           (a = unAuthorized)

   [slRole_distinct_clauses]  Theorem

      |- PlatoonLeader ≠ PlatoonSergeant

   [slState2num_11]  Theorem

      |- ∀a a'. (slState2num a = slState2num a') ⇔ (a = a')

   [slState2num_ONTO]  Theorem

      |- ∀r. r < 5 ⇔ ∃a. r = slState2num a

   [slState2num_num2slState]  Theorem

      |- ∀r. r < 5 ⇔ (slState2num (num2slState r) = r)

   [slState2num_thm]  Theorem

      |- (slState2num CONDUCT_PB = 0) ∧ (slState2num SECURE_PB = 1) ∧
         (slState2num ACTIONS_IN_PB = 2) ∧ (slState2num WITHDRAW_PB = 3) ∧
         (slState2num COMPLETE_PB = 4)

   [slState_Axiom]  Theorem

      |- ∀x0 x1 x2 x3 x4.
           ∃f.
             (f CONDUCT_PB = x0) ∧ (f SECURE_PB = x1) ∧
             (f ACTIONS_IN_PB = x2) ∧ (f WITHDRAW_PB = x3) ∧
             (f COMPLETE_PB = x4)

   [slState_EQ_slState]  Theorem

      |- ∀a a'. (a = a') ⇔ (slState2num a = slState2num a')

   [slState_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3 v4.
           (M = M') ∧ ((M' = CONDUCT_PB) ⇒ (v0 = v0')) ∧
           ((M' = SECURE_PB) ⇒ (v1 = v1')) ∧
           ((M' = ACTIONS_IN_PB) ⇒ (v2 = v2')) ∧
           ((M' = WITHDRAW_PB) ⇒ (v3 = v3')) ∧
           ((M' = COMPLETE_PB) ⇒ (v4 = v4')) ⇒
           ((case M of
               CONDUCT_PB => v0
             | SECURE_PB => v1
             | ACTIONS_IN_PB => v2
             | WITHDRAW_PB => v3
             | COMPLETE_PB => v4) =
            case M' of
              CONDUCT_PB => v0'
            | SECURE_PB => v1'
            | ACTIONS_IN_PB => v2'
            | WITHDRAW_PB => v3'
            | COMPLETE_PB => v4')

   [slState_case_def]  Theorem

      |- (∀v0 v1 v2 v3 v4.
            (case CONDUCT_PB of
               CONDUCT_PB => v0
             | SECURE_PB => v1
             | ACTIONS_IN_PB => v2
             | WITHDRAW_PB => v3
             | COMPLETE_PB => v4) =
            v0) ∧
         (∀v0 v1 v2 v3 v4.
            (case SECURE_PB of
               CONDUCT_PB => v0
             | SECURE_PB => v1
             | ACTIONS_IN_PB => v2
             | WITHDRAW_PB => v3
             | COMPLETE_PB => v4) =
            v1) ∧
         (∀v0 v1 v2 v3 v4.
            (case ACTIONS_IN_PB of
               CONDUCT_PB => v0
             | SECURE_PB => v1
             | ACTIONS_IN_PB => v2
             | WITHDRAW_PB => v3
             | COMPLETE_PB => v4) =
            v2) ∧
         (∀v0 v1 v2 v3 v4.
            (case WITHDRAW_PB of
               CONDUCT_PB => v0
             | SECURE_PB => v1
             | ACTIONS_IN_PB => v2
             | WITHDRAW_PB => v3
             | COMPLETE_PB => v4) =
            v3) ∧
         ∀v0 v1 v2 v3 v4.
           (case COMPLETE_PB of
              CONDUCT_PB => v0
            | SECURE_PB => v1
            | ACTIONS_IN_PB => v2
            | WITHDRAW_PB => v3
            | COMPLETE_PB => v4) =
           v4

   [slState_distinct]  Theorem

      |- CONDUCT_PB ≠ SECURE_PB ∧ CONDUCT_PB ≠ ACTIONS_IN_PB ∧
         CONDUCT_PB ≠ WITHDRAW_PB ∧ CONDUCT_PB ≠ COMPLETE_PB ∧
         SECURE_PB ≠ ACTIONS_IN_PB ∧ SECURE_PB ≠ WITHDRAW_PB ∧
         SECURE_PB ≠ COMPLETE_PB ∧ ACTIONS_IN_PB ≠ WITHDRAW_PB ∧
         ACTIONS_IN_PB ≠ COMPLETE_PB ∧ WITHDRAW_PB ≠ COMPLETE_PB

   [slState_distinct_clauses]  Theorem

      |- CONDUCT_PB ≠ SECURE_PB ∧ CONDUCT_PB ≠ ACTIONS_IN_PB ∧
         CONDUCT_PB ≠ WITHDRAW_PB ∧ CONDUCT_PB ≠ COMPLETE_PB ∧
         SECURE_PB ≠ ACTIONS_IN_PB ∧ SECURE_PB ≠ WITHDRAW_PB ∧
         SECURE_PB ≠ COMPLETE_PB ∧ ACTIONS_IN_PB ≠ WITHDRAW_PB ∧
         ACTIONS_IN_PB ≠ COMPLETE_PB ∧ WITHDRAW_PB ≠ COMPLETE_PB

   [slState_induction]  Theorem

      |- ∀P.
           P ACTIONS_IN_PB ∧ P COMPLETE_PB ∧ P CONDUCT_PB ∧ P SECURE_PB ∧
           P WITHDRAW_PB ⇒
           ∀a. P a

   [slState_nchotomy]  Theorem

      |- ∀a.
           (a = CONDUCT_PB) ∨ (a = SECURE_PB) ∨ (a = ACTIONS_IN_PB) ∨
           (a = WITHDRAW_PB) ∨ (a = COMPLETE_PB)

   [stateRole2num_11]  Theorem

      |- ∀a a'. (stateRole2num a = stateRole2num a') ⇔ (a = a')

   [stateRole2num_ONTO]  Theorem

      |- ∀r. r < 2 ⇔ ∃a. r = stateRole2num a

   [stateRole2num_num2stateRole]  Theorem

      |- ∀r. r < 2 ⇔ (stateRole2num (num2stateRole r) = r)

   [stateRole2num_thm]  Theorem

      |- (stateRole2num PlatoonLeader = 0) ∧
         (stateRole2num PlatoonSergeant = 1)

   [stateRole_Axiom]  Theorem

      |- ∀x0 x1. ∃f. (f PlatoonLeader = x0) ∧ (f PlatoonSergeant = x1)

   [stateRole_EQ_stateRole]  Theorem

      |- ∀a a'. (a = a') ⇔ (stateRole2num a = stateRole2num a')

   [stateRole_case_cong]  Theorem

      |- ∀M M' v0 v1.
           (M = M') ∧ ((M' = PlatoonLeader) ⇒ (v0 = v0')) ∧
           ((M' = PlatoonSergeant) ⇒ (v1 = v1')) ⇒
           ((case M of PlatoonLeader => v0 | PlatoonSergeant => v1) =
            case M' of PlatoonLeader => v0' | PlatoonSergeant => v1')

   [stateRole_case_def]  Theorem

      |- (∀v0 v1.
            (case PlatoonLeader of
               PlatoonLeader => v0
             | PlatoonSergeant => v1) =
            v0) ∧
         ∀v0 v1.
           (case PlatoonSergeant of
              PlatoonLeader => v0
            | PlatoonSergeant => v1) =
           v1

   [stateRole_distinct]  Theorem

      |- PlatoonLeader ≠ PlatoonSergeant

   [stateRole_induction]  Theorem

      |- ∀P. P PlatoonLeader ∧ P PlatoonSergeant ⇒ ∀a. P a

   [stateRole_nchotomy]  Theorem

      |- ∀a. (a = PlatoonLeader) ∨ (a = PlatoonSergeant)


*)
end
