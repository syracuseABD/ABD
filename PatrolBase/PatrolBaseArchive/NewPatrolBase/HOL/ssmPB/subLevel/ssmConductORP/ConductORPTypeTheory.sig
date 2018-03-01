signature ConductORPTypeTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val plCommand_BIJ : thm
    val plCommand_CASE : thm
    val plCommand_TY_DEF : thm
    val plCommand_size_def : thm
    val psgCommand_BIJ : thm
    val psgCommand_CASE : thm
    val psgCommand_TY_DEF : thm
    val psgCommand_size_def : thm
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
    val datatype_plCommand : thm
    val datatype_psgCommand : thm
    val datatype_slCommand : thm
    val datatype_slOutput : thm
    val datatype_slState : thm
    val datatype_stateRole : thm
    val num2plCommand_11 : thm
    val num2plCommand_ONTO : thm
    val num2plCommand_plCommand2num : thm
    val num2plCommand_thm : thm
    val num2psgCommand_11 : thm
    val num2psgCommand_ONTO : thm
    val num2psgCommand_psgCommand2num : thm
    val num2psgCommand_thm : thm
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
    val plCommand2num_11 : thm
    val plCommand2num_ONTO : thm
    val plCommand2num_num2plCommand : thm
    val plCommand2num_thm : thm
    val plCommand_Axiom : thm
    val plCommand_EQ_plCommand : thm
    val plCommand_case_cong : thm
    val plCommand_case_def : thm
    val plCommand_distinct : thm
    val plCommand_distinct_clauses : thm
    val plCommand_induction : thm
    val plCommand_nchotomy : thm
    val psgCommand2num_11 : thm
    val psgCommand2num_ONTO : thm
    val psgCommand2num_num2psgCommand : thm
    val psgCommand2num_thm : thm
    val psgCommand_Axiom : thm
    val psgCommand_EQ_psgCommand : thm
    val psgCommand_case_cong : thm
    val psgCommand_case_def : thm
    val psgCommand_distinct : thm
    val psgCommand_distinct_clauses : thm
    val psgCommand_induction : thm
    val psgCommand_nchotomy : thm
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

  val ConductORPType_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [indexedLists] Parent theory of "ConductORPType"

   [patternMatches] Parent theory of "ConductORPType"

   [plCommand_BIJ]  Definition

      |- (∀a. num2plCommand (plCommand2num a) = a) ∧
         ∀r. (λn. n < 4) r ⇔ (plCommand2num (num2plCommand r) = r)

   [plCommand_CASE]  Definition

      |- ∀x v0 v1 v2 v3.
           (case x of
              secure => v0
            | withdraw => v1
            | complete => v2
            | plIncomplete => v3) =
           (λm.
              if m < 1 then v0
              else if m < 2 then v1
              else if m = 2 then v2
              else v3) (plCommand2num x)

   [plCommand_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 4) rep

   [plCommand_size_def]  Definition

      |- ∀x. plCommand_size x = 0

   [psgCommand_BIJ]  Definition

      |- (∀a. num2psgCommand (psgCommand2num a) = a) ∧
         ∀r. (λn. n < 2) r ⇔ (psgCommand2num (num2psgCommand r) = r)

   [psgCommand_CASE]  Definition

      |- ∀x v0 v1.
           (case x of actionsIn => v0 | psgIncomplete => v1) =
           (λm. if m = 0 then v0 else v1) (psgCommand2num x)

   [psgCommand_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 2) rep

   [psgCommand_size_def]  Definition

      |- ∀x. psgCommand_size x = 0

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

      |- (∀a. slCommand_size (PL a) = 1 + plCommand_size a) ∧
         ∀a. slCommand_size (PSG a) = 1 + psgCommand_size a

   [slOutput_BIJ]  Definition

      |- (∀a. num2slOutput (slOutput2num a) = a) ∧
         ∀r. (λn. n < 7) r ⇔ (slOutput2num (num2slOutput r) = r)

   [slOutput_CASE]  Definition

      |- ∀x v0 v1 v2 v3 v4 v5 v6.
           (case x of
              ConductORP => v0
            | Secure => v1
            | ActionsIn => v2
            | Withdraw => v3
            | Complete => v4
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
              CONDUCT_ORP => v0
            | SECURE => v1
            | ACTIONS_IN => v2
            | WITHDRAW => v3
            | COMPLETE => v4) =
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

   [datatype_plCommand]  Theorem

      |- DATATYPE (plCommand secure withdraw complete plIncomplete)

   [datatype_psgCommand]  Theorem

      |- DATATYPE (psgCommand actionsIn psgIncomplete)

   [datatype_slCommand]  Theorem

      |- DATATYPE (slCommand PL PSG)

   [datatype_slOutput]  Theorem

      |- DATATYPE
           (slOutput ConductORP Secure ActionsIn Withdraw Complete
              unAuthenticated unAuthorized)

   [datatype_slState]  Theorem

      |- DATATYPE (slState CONDUCT_ORP SECURE ACTIONS_IN WITHDRAW COMPLETE)

   [datatype_stateRole]  Theorem

      |- DATATYPE (stateRole PlatoonLeader PlatoonSergeant)

   [num2plCommand_11]  Theorem

      |- ∀r r'.
           r < 4 ⇒
           r' < 4 ⇒
           ((num2plCommand r = num2plCommand r') ⇔ (r = r'))

   [num2plCommand_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2plCommand r) ∧ r < 4

   [num2plCommand_plCommand2num]  Theorem

      |- ∀a. num2plCommand (plCommand2num a) = a

   [num2plCommand_thm]  Theorem

      |- (num2plCommand 0 = secure) ∧ (num2plCommand 1 = withdraw) ∧
         (num2plCommand 2 = complete) ∧ (num2plCommand 3 = plIncomplete)

   [num2psgCommand_11]  Theorem

      |- ∀r r'.
           r < 2 ⇒
           r' < 2 ⇒
           ((num2psgCommand r = num2psgCommand r') ⇔ (r = r'))

   [num2psgCommand_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2psgCommand r) ∧ r < 2

   [num2psgCommand_psgCommand2num]  Theorem

      |- ∀a. num2psgCommand (psgCommand2num a) = a

   [num2psgCommand_thm]  Theorem

      |- (num2psgCommand 0 = actionsIn) ∧
         (num2psgCommand 1 = psgIncomplete)

   [num2slOutput_11]  Theorem

      |- ∀r r'.
           r < 7 ⇒ r' < 7 ⇒ ((num2slOutput r = num2slOutput r') ⇔ (r = r'))

   [num2slOutput_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2slOutput r) ∧ r < 7

   [num2slOutput_slOutput2num]  Theorem

      |- ∀a. num2slOutput (slOutput2num a) = a

   [num2slOutput_thm]  Theorem

      |- (num2slOutput 0 = ConductORP) ∧ (num2slOutput 1 = Secure) ∧
         (num2slOutput 2 = ActionsIn) ∧ (num2slOutput 3 = Withdraw) ∧
         (num2slOutput 4 = Complete) ∧ (num2slOutput 5 = unAuthenticated) ∧
         (num2slOutput 6 = unAuthorized)

   [num2slState_11]  Theorem

      |- ∀r r'.
           r < 5 ⇒ r' < 5 ⇒ ((num2slState r = num2slState r') ⇔ (r = r'))

   [num2slState_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2slState r) ∧ r < 5

   [num2slState_slState2num]  Theorem

      |- ∀a. num2slState (slState2num a) = a

   [num2slState_thm]  Theorem

      |- (num2slState 0 = CONDUCT_ORP) ∧ (num2slState 1 = SECURE) ∧
         (num2slState 2 = ACTIONS_IN) ∧ (num2slState 3 = WITHDRAW) ∧
         (num2slState 4 = COMPLETE)

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

   [plCommand2num_11]  Theorem

      |- ∀a a'. (plCommand2num a = plCommand2num a') ⇔ (a = a')

   [plCommand2num_ONTO]  Theorem

      |- ∀r. r < 4 ⇔ ∃a. r = plCommand2num a

   [plCommand2num_num2plCommand]  Theorem

      |- ∀r. r < 4 ⇔ (plCommand2num (num2plCommand r) = r)

   [plCommand2num_thm]  Theorem

      |- (plCommand2num secure = 0) ∧ (plCommand2num withdraw = 1) ∧
         (plCommand2num complete = 2) ∧ (plCommand2num plIncomplete = 3)

   [plCommand_Axiom]  Theorem

      |- ∀x0 x1 x2 x3.
           ∃f.
             (f secure = x0) ∧ (f withdraw = x1) ∧ (f complete = x2) ∧
             (f plIncomplete = x3)

   [plCommand_EQ_plCommand]  Theorem

      |- ∀a a'. (a = a') ⇔ (plCommand2num a = plCommand2num a')

   [plCommand_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3.
           (M = M') ∧ ((M' = secure) ⇒ (v0 = v0')) ∧
           ((M' = withdraw) ⇒ (v1 = v1')) ∧
           ((M' = complete) ⇒ (v2 = v2')) ∧
           ((M' = plIncomplete) ⇒ (v3 = v3')) ⇒
           ((case M of
               secure => v0
             | withdraw => v1
             | complete => v2
             | plIncomplete => v3) =
            case M' of
              secure => v0'
            | withdraw => v1'
            | complete => v2'
            | plIncomplete => v3')

   [plCommand_case_def]  Theorem

      |- (∀v0 v1 v2 v3.
            (case secure of
               secure => v0
             | withdraw => v1
             | complete => v2
             | plIncomplete => v3) =
            v0) ∧
         (∀v0 v1 v2 v3.
            (case withdraw of
               secure => v0
             | withdraw => v1
             | complete => v2
             | plIncomplete => v3) =
            v1) ∧
         (∀v0 v1 v2 v3.
            (case complete of
               secure => v0
             | withdraw => v1
             | complete => v2
             | plIncomplete => v3) =
            v2) ∧
         ∀v0 v1 v2 v3.
           (case plIncomplete of
              secure => v0
            | withdraw => v1
            | complete => v2
            | plIncomplete => v3) =
           v3

   [plCommand_distinct]  Theorem

      |- secure ≠ withdraw ∧ secure ≠ complete ∧ secure ≠ plIncomplete ∧
         withdraw ≠ complete ∧ withdraw ≠ plIncomplete ∧
         complete ≠ plIncomplete

   [plCommand_distinct_clauses]  Theorem

      |- secure ≠ withdraw ∧ secure ≠ complete ∧ secure ≠ plIncomplete ∧
         withdraw ≠ complete ∧ withdraw ≠ plIncomplete ∧
         complete ≠ plIncomplete

   [plCommand_induction]  Theorem

      |- ∀P. P complete ∧ P plIncomplete ∧ P secure ∧ P withdraw ⇒ ∀a. P a

   [plCommand_nchotomy]  Theorem

      |- ∀a.
           (a = secure) ∨ (a = withdraw) ∨ (a = complete) ∨
           (a = plIncomplete)

   [psgCommand2num_11]  Theorem

      |- ∀a a'. (psgCommand2num a = psgCommand2num a') ⇔ (a = a')

   [psgCommand2num_ONTO]  Theorem

      |- ∀r. r < 2 ⇔ ∃a. r = psgCommand2num a

   [psgCommand2num_num2psgCommand]  Theorem

      |- ∀r. r < 2 ⇔ (psgCommand2num (num2psgCommand r) = r)

   [psgCommand2num_thm]  Theorem

      |- (psgCommand2num actionsIn = 0) ∧
         (psgCommand2num psgIncomplete = 1)

   [psgCommand_Axiom]  Theorem

      |- ∀x0 x1. ∃f. (f actionsIn = x0) ∧ (f psgIncomplete = x1)

   [psgCommand_EQ_psgCommand]  Theorem

      |- ∀a a'. (a = a') ⇔ (psgCommand2num a = psgCommand2num a')

   [psgCommand_case_cong]  Theorem

      |- ∀M M' v0 v1.
           (M = M') ∧ ((M' = actionsIn) ⇒ (v0 = v0')) ∧
           ((M' = psgIncomplete) ⇒ (v1 = v1')) ⇒
           ((case M of actionsIn => v0 | psgIncomplete => v1) =
            case M' of actionsIn => v0' | psgIncomplete => v1')

   [psgCommand_case_def]  Theorem

      |- (∀v0 v1.
            (case actionsIn of actionsIn => v0 | psgIncomplete => v1) =
            v0) ∧
         ∀v0 v1.
           (case psgIncomplete of actionsIn => v0 | psgIncomplete => v1) =
           v1

   [psgCommand_distinct]  Theorem

      |- actionsIn ≠ psgIncomplete

   [psgCommand_distinct_clauses]  Theorem

      |- actionsIn ≠ psgIncomplete

   [psgCommand_induction]  Theorem

      |- ∀P. P actionsIn ∧ P psgIncomplete ⇒ ∀a. P a

   [psgCommand_nchotomy]  Theorem

      |- ∀a. (a = actionsIn) ∨ (a = psgIncomplete)

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

      |- (slOutput2num ConductORP = 0) ∧ (slOutput2num Secure = 1) ∧
         (slOutput2num ActionsIn = 2) ∧ (slOutput2num Withdraw = 3) ∧
         (slOutput2num Complete = 4) ∧ (slOutput2num unAuthenticated = 5) ∧
         (slOutput2num unAuthorized = 6)

   [slOutput_Axiom]  Theorem

      |- ∀x0 x1 x2 x3 x4 x5 x6.
           ∃f.
             (f ConductORP = x0) ∧ (f Secure = x1) ∧ (f ActionsIn = x2) ∧
             (f Withdraw = x3) ∧ (f Complete = x4) ∧
             (f unAuthenticated = x5) ∧ (f unAuthorized = x6)

   [slOutput_EQ_slOutput]  Theorem

      |- ∀a a'. (a = a') ⇔ (slOutput2num a = slOutput2num a')

   [slOutput_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3 v4 v5 v6.
           (M = M') ∧ ((M' = ConductORP) ⇒ (v0 = v0')) ∧
           ((M' = Secure) ⇒ (v1 = v1')) ∧ ((M' = ActionsIn) ⇒ (v2 = v2')) ∧
           ((M' = Withdraw) ⇒ (v3 = v3')) ∧
           ((M' = Complete) ⇒ (v4 = v4')) ∧
           ((M' = unAuthenticated) ⇒ (v5 = v5')) ∧
           ((M' = unAuthorized) ⇒ (v6 = v6')) ⇒
           ((case M of
               ConductORP => v0
             | Secure => v1
             | ActionsIn => v2
             | Withdraw => v3
             | Complete => v4
             | unAuthenticated => v5
             | unAuthorized => v6) =
            case M' of
              ConductORP => v0'
            | Secure => v1'
            | ActionsIn => v2'
            | Withdraw => v3'
            | Complete => v4'
            | unAuthenticated => v5'
            | unAuthorized => v6')

   [slOutput_case_def]  Theorem

      |- (∀v0 v1 v2 v3 v4 v5 v6.
            (case ConductORP of
               ConductORP => v0
             | Secure => v1
             | ActionsIn => v2
             | Withdraw => v3
             | Complete => v4
             | unAuthenticated => v5
             | unAuthorized => v6) =
            v0) ∧
         (∀v0 v1 v2 v3 v4 v5 v6.
            (case Secure of
               ConductORP => v0
             | Secure => v1
             | ActionsIn => v2
             | Withdraw => v3
             | Complete => v4
             | unAuthenticated => v5
             | unAuthorized => v6) =
            v1) ∧
         (∀v0 v1 v2 v3 v4 v5 v6.
            (case ActionsIn of
               ConductORP => v0
             | Secure => v1
             | ActionsIn => v2
             | Withdraw => v3
             | Complete => v4
             | unAuthenticated => v5
             | unAuthorized => v6) =
            v2) ∧
         (∀v0 v1 v2 v3 v4 v5 v6.
            (case Withdraw of
               ConductORP => v0
             | Secure => v1
             | ActionsIn => v2
             | Withdraw => v3
             | Complete => v4
             | unAuthenticated => v5
             | unAuthorized => v6) =
            v3) ∧
         (∀v0 v1 v2 v3 v4 v5 v6.
            (case Complete of
               ConductORP => v0
             | Secure => v1
             | ActionsIn => v2
             | Withdraw => v3
             | Complete => v4
             | unAuthenticated => v5
             | unAuthorized => v6) =
            v4) ∧
         (∀v0 v1 v2 v3 v4 v5 v6.
            (case unAuthenticated of
               ConductORP => v0
             | Secure => v1
             | ActionsIn => v2
             | Withdraw => v3
             | Complete => v4
             | unAuthenticated => v5
             | unAuthorized => v6) =
            v5) ∧
         ∀v0 v1 v2 v3 v4 v5 v6.
           (case unAuthorized of
              ConductORP => v0
            | Secure => v1
            | ActionsIn => v2
            | Withdraw => v3
            | Complete => v4
            | unAuthenticated => v5
            | unAuthorized => v6) =
           v6

   [slOutput_distinct]  Theorem

      |- ConductORP ≠ Secure ∧ ConductORP ≠ ActionsIn ∧
         ConductORP ≠ Withdraw ∧ ConductORP ≠ Complete ∧
         ConductORP ≠ unAuthenticated ∧ ConductORP ≠ unAuthorized ∧
         Secure ≠ ActionsIn ∧ Secure ≠ Withdraw ∧ Secure ≠ Complete ∧
         Secure ≠ unAuthenticated ∧ Secure ≠ unAuthorized ∧
         ActionsIn ≠ Withdraw ∧ ActionsIn ≠ Complete ∧
         ActionsIn ≠ unAuthenticated ∧ ActionsIn ≠ unAuthorized ∧
         Withdraw ≠ Complete ∧ Withdraw ≠ unAuthenticated ∧
         Withdraw ≠ unAuthorized ∧ Complete ≠ unAuthenticated ∧
         Complete ≠ unAuthorized ∧ unAuthenticated ≠ unAuthorized

   [slOutput_distinct_clauses]  Theorem

      |- ConductORP ≠ Secure ∧ ConductORP ≠ ActionsIn ∧
         ConductORP ≠ Withdraw ∧ ConductORP ≠ Complete ∧
         ConductORP ≠ unAuthenticated ∧ ConductORP ≠ unAuthorized ∧
         Secure ≠ ActionsIn ∧ Secure ≠ Withdraw ∧ Secure ≠ Complete ∧
         Secure ≠ unAuthenticated ∧ Secure ≠ unAuthorized ∧
         ActionsIn ≠ Withdraw ∧ ActionsIn ≠ Complete ∧
         ActionsIn ≠ unAuthenticated ∧ ActionsIn ≠ unAuthorized ∧
         Withdraw ≠ Complete ∧ Withdraw ≠ unAuthenticated ∧
         Withdraw ≠ unAuthorized ∧ Complete ≠ unAuthenticated ∧
         Complete ≠ unAuthorized ∧ unAuthenticated ≠ unAuthorized

   [slOutput_induction]  Theorem

      |- ∀P.
           P ActionsIn ∧ P Complete ∧ P ConductORP ∧ P Secure ∧
           P Withdraw ∧ P unAuthenticated ∧ P unAuthorized ⇒
           ∀a. P a

   [slOutput_nchotomy]  Theorem

      |- ∀a.
           (a = ConductORP) ∨ (a = Secure) ∨ (a = ActionsIn) ∨
           (a = Withdraw) ∨ (a = Complete) ∨ (a = unAuthenticated) ∨
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

      |- (slState2num CONDUCT_ORP = 0) ∧ (slState2num SECURE = 1) ∧
         (slState2num ACTIONS_IN = 2) ∧ (slState2num WITHDRAW = 3) ∧
         (slState2num COMPLETE = 4)

   [slState_Axiom]  Theorem

      |- ∀x0 x1 x2 x3 x4.
           ∃f.
             (f CONDUCT_ORP = x0) ∧ (f SECURE = x1) ∧ (f ACTIONS_IN = x2) ∧
             (f WITHDRAW = x3) ∧ (f COMPLETE = x4)

   [slState_EQ_slState]  Theorem

      |- ∀a a'. (a = a') ⇔ (slState2num a = slState2num a')

   [slState_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3 v4.
           (M = M') ∧ ((M' = CONDUCT_ORP) ⇒ (v0 = v0')) ∧
           ((M' = SECURE) ⇒ (v1 = v1')) ∧
           ((M' = ACTIONS_IN) ⇒ (v2 = v2')) ∧
           ((M' = WITHDRAW) ⇒ (v3 = v3')) ∧
           ((M' = COMPLETE) ⇒ (v4 = v4')) ⇒
           ((case M of
               CONDUCT_ORP => v0
             | SECURE => v1
             | ACTIONS_IN => v2
             | WITHDRAW => v3
             | COMPLETE => v4) =
            case M' of
              CONDUCT_ORP => v0'
            | SECURE => v1'
            | ACTIONS_IN => v2'
            | WITHDRAW => v3'
            | COMPLETE => v4')

   [slState_case_def]  Theorem

      |- (∀v0 v1 v2 v3 v4.
            (case CONDUCT_ORP of
               CONDUCT_ORP => v0
             | SECURE => v1
             | ACTIONS_IN => v2
             | WITHDRAW => v3
             | COMPLETE => v4) =
            v0) ∧
         (∀v0 v1 v2 v3 v4.
            (case SECURE of
               CONDUCT_ORP => v0
             | SECURE => v1
             | ACTIONS_IN => v2
             | WITHDRAW => v3
             | COMPLETE => v4) =
            v1) ∧
         (∀v0 v1 v2 v3 v4.
            (case ACTIONS_IN of
               CONDUCT_ORP => v0
             | SECURE => v1
             | ACTIONS_IN => v2
             | WITHDRAW => v3
             | COMPLETE => v4) =
            v2) ∧
         (∀v0 v1 v2 v3 v4.
            (case WITHDRAW of
               CONDUCT_ORP => v0
             | SECURE => v1
             | ACTIONS_IN => v2
             | WITHDRAW => v3
             | COMPLETE => v4) =
            v3) ∧
         ∀v0 v1 v2 v3 v4.
           (case COMPLETE of
              CONDUCT_ORP => v0
            | SECURE => v1
            | ACTIONS_IN => v2
            | WITHDRAW => v3
            | COMPLETE => v4) =
           v4

   [slState_distinct]  Theorem

      |- CONDUCT_ORP ≠ SECURE ∧ CONDUCT_ORP ≠ ACTIONS_IN ∧
         CONDUCT_ORP ≠ WITHDRAW ∧ CONDUCT_ORP ≠ COMPLETE ∧
         SECURE ≠ ACTIONS_IN ∧ SECURE ≠ WITHDRAW ∧ SECURE ≠ COMPLETE ∧
         ACTIONS_IN ≠ WITHDRAW ∧ ACTIONS_IN ≠ COMPLETE ∧
         WITHDRAW ≠ COMPLETE

   [slState_distinct_clauses]  Theorem

      |- CONDUCT_ORP ≠ SECURE ∧ CONDUCT_ORP ≠ ACTIONS_IN ∧
         CONDUCT_ORP ≠ WITHDRAW ∧ CONDUCT_ORP ≠ COMPLETE ∧
         SECURE ≠ ACTIONS_IN ∧ SECURE ≠ WITHDRAW ∧ SECURE ≠ COMPLETE ∧
         ACTIONS_IN ≠ WITHDRAW ∧ ACTIONS_IN ≠ COMPLETE ∧
         WITHDRAW ≠ COMPLETE

   [slState_induction]  Theorem

      |- ∀P.
           P ACTIONS_IN ∧ P COMPLETE ∧ P CONDUCT_ORP ∧ P SECURE ∧
           P WITHDRAW ⇒
           ∀a. P a

   [slState_nchotomy]  Theorem

      |- ∀a.
           (a = CONDUCT_ORP) ∨ (a = SECURE) ∨ (a = ACTIONS_IN) ∨
           (a = WITHDRAW) ∨ (a = COMPLETE)

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
