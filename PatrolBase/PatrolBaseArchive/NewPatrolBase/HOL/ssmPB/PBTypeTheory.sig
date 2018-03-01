signature PBTypeTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val slCommand_BIJ : thm
    val slCommand_CASE : thm
    val slCommand_TY_DEF : thm
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
    val datatype_slCommand : thm
    val datatype_slOutput : thm
    val datatype_slState : thm
    val datatype_stateRole : thm
    val num2slCommand_11 : thm
    val num2slCommand_ONTO : thm
    val num2slCommand_slCommand2num : thm
    val num2slCommand_thm : thm
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
    val slCommand2num_11 : thm
    val slCommand2num_ONTO : thm
    val slCommand2num_num2slCommand : thm
    val slCommand2num_thm : thm
    val slCommand_Axiom : thm
    val slCommand_EQ_slCommand : thm
    val slCommand_case_cong : thm
    val slCommand_case_def : thm
    val slCommand_distinct : thm
    val slCommand_distinct_clauses : thm
    val slCommand_induction : thm
    val slCommand_nchotomy : thm
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
    val stateRole_induction : thm
    val stateRole_nchotomy : thm

  val PBType_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [indexedLists] Parent theory of "PBType"

   [patternMatches] Parent theory of "PBType"

   [slCommand_BIJ]  Definition

      |- (∀a. num2slCommand (slCommand2num a) = a) ∧
         ∀r. (λn. n < 6) r ⇔ (slCommand2num (num2slCommand r) = r)

   [slCommand_CASE]  Definition

      |- ∀x v0 v1 v2 v3 v4 v5.
           (case x of
              crossLD => v0
            | conductORP => v1
            | moveToPB => v2
            | conductPB => v3
            | completePB => v4
            | incomplete => v5) =
           (λm.
              if m < 2 then if m = 0 then v0 else v1
              else if m < 3 then v2
              else if m < 4 then v3
              else if m = 4 then v4
              else v5) (slCommand2num x)

   [slCommand_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 6) rep

   [slCommand_size_def]  Definition

      |- ∀x. slCommand_size x = 0

   [slOutput_BIJ]  Definition

      |- (∀a. num2slOutput (slOutput2num a) = a) ∧
         ∀r. (λn. n < 8) r ⇔ (slOutput2num (num2slOutput r) = r)

   [slOutput_CASE]  Definition

      |- ∀x v0 v1 v2 v3 v4 v5 v6 v7.
           (case x of
              PlanPB => v0
            | MoveToORP => v1
            | ConductORP => v2
            | MoveToPB => v3
            | ConductPB => v4
            | CompletePB => v5
            | unAuthenticated => v6
            | unAuthorized => v7) =
           (λm.
              if m < 3 then if m < 1 then v0 else if m = 1 then v1 else v2
              else if m < 5 then if m = 3 then v3 else v4
              else if m < 6 then v5
              else if m = 6 then v6
              else v7) (slOutput2num x)

   [slOutput_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 8) rep

   [slOutput_size_def]  Definition

      |- ∀x. slOutput_size x = 0

   [slState_BIJ]  Definition

      |- (∀a. num2slState (slState2num a) = a) ∧
         ∀r. (λn. n < 6) r ⇔ (slState2num (num2slState r) = r)

   [slState_CASE]  Definition

      |- ∀x v0 v1 v2 v3 v4 v5.
           (case x of
              PLAN_PB => v0
            | MOVE_TO_ORP => v1
            | CONDUCT_ORP => v2
            | MOVE_TO_PB => v3
            | CONDUCT_PB => v4
            | COMPLETE_PB => v5) =
           (λm.
              if m < 2 then if m = 0 then v0 else v1
              else if m < 3 then v2
              else if m < 4 then v3
              else if m = 4 then v4
              else v5) (slState2num x)

   [slState_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 6) rep

   [slState_size_def]  Definition

      |- ∀x. slState_size x = 0

   [stateRole_BIJ]  Definition

      |- (∀a. num2stateRole (stateRole2num a) = a) ∧
         ∀r. (λn. n < 1) r ⇔ (stateRole2num (num2stateRole r) = r)

   [stateRole_CASE]  Definition

      |- ∀x v0.
           (case x of PlatoonLeader => v0) = (λm. v0) (stateRole2num x)

   [stateRole_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 1) rep

   [stateRole_size_def]  Definition

      |- ∀x. stateRole_size x = 0

   [datatype_slCommand]  Theorem

      |- DATATYPE
           (slCommand crossLD conductORP moveToPB conductPB completePB
              incomplete)

   [datatype_slOutput]  Theorem

      |- DATATYPE
           (slOutput PlanPB MoveToORP ConductORP MoveToPB ConductPB
              CompletePB unAuthenticated unAuthorized)

   [datatype_slState]  Theorem

      |- DATATYPE
           (slState PLAN_PB MOVE_TO_ORP CONDUCT_ORP MOVE_TO_PB CONDUCT_PB
              COMPLETE_PB)

   [datatype_stateRole]  Theorem

      |- DATATYPE (stateRole PlatoonLeader)

   [num2slCommand_11]  Theorem

      |- ∀r r'.
           r < 6 ⇒
           r' < 6 ⇒
           ((num2slCommand r = num2slCommand r') ⇔ (r = r'))

   [num2slCommand_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2slCommand r) ∧ r < 6

   [num2slCommand_slCommand2num]  Theorem

      |- ∀a. num2slCommand (slCommand2num a) = a

   [num2slCommand_thm]  Theorem

      |- (num2slCommand 0 = crossLD) ∧ (num2slCommand 1 = conductORP) ∧
         (num2slCommand 2 = moveToPB) ∧ (num2slCommand 3 = conductPB) ∧
         (num2slCommand 4 = completePB) ∧ (num2slCommand 5 = incomplete)

   [num2slOutput_11]  Theorem

      |- ∀r r'.
           r < 8 ⇒ r' < 8 ⇒ ((num2slOutput r = num2slOutput r') ⇔ (r = r'))

   [num2slOutput_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2slOutput r) ∧ r < 8

   [num2slOutput_slOutput2num]  Theorem

      |- ∀a. num2slOutput (slOutput2num a) = a

   [num2slOutput_thm]  Theorem

      |- (num2slOutput 0 = PlanPB) ∧ (num2slOutput 1 = MoveToORP) ∧
         (num2slOutput 2 = ConductORP) ∧ (num2slOutput 3 = MoveToPB) ∧
         (num2slOutput 4 = ConductPB) ∧ (num2slOutput 5 = CompletePB) ∧
         (num2slOutput 6 = unAuthenticated) ∧
         (num2slOutput 7 = unAuthorized)

   [num2slState_11]  Theorem

      |- ∀r r'.
           r < 6 ⇒ r' < 6 ⇒ ((num2slState r = num2slState r') ⇔ (r = r'))

   [num2slState_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2slState r) ∧ r < 6

   [num2slState_slState2num]  Theorem

      |- ∀a. num2slState (slState2num a) = a

   [num2slState_thm]  Theorem

      |- (num2slState 0 = PLAN_PB) ∧ (num2slState 1 = MOVE_TO_ORP) ∧
         (num2slState 2 = CONDUCT_ORP) ∧ (num2slState 3 = MOVE_TO_PB) ∧
         (num2slState 4 = CONDUCT_PB) ∧ (num2slState 5 = COMPLETE_PB)

   [num2stateRole_11]  Theorem

      |- ∀r r'.
           r < 1 ⇒
           r' < 1 ⇒
           ((num2stateRole r = num2stateRole r') ⇔ (r = r'))

   [num2stateRole_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2stateRole r) ∧ r < 1

   [num2stateRole_stateRole2num]  Theorem

      |- ∀a. num2stateRole (stateRole2num a) = a

   [num2stateRole_thm]  Theorem

      |- num2stateRole 0 = PlatoonLeader

   [slCommand2num_11]  Theorem

      |- ∀a a'. (slCommand2num a = slCommand2num a') ⇔ (a = a')

   [slCommand2num_ONTO]  Theorem

      |- ∀r. r < 6 ⇔ ∃a. r = slCommand2num a

   [slCommand2num_num2slCommand]  Theorem

      |- ∀r. r < 6 ⇔ (slCommand2num (num2slCommand r) = r)

   [slCommand2num_thm]  Theorem

      |- (slCommand2num crossLD = 0) ∧ (slCommand2num conductORP = 1) ∧
         (slCommand2num moveToPB = 2) ∧ (slCommand2num conductPB = 3) ∧
         (slCommand2num completePB = 4) ∧ (slCommand2num incomplete = 5)

   [slCommand_Axiom]  Theorem

      |- ∀x0 x1 x2 x3 x4 x5.
           ∃f.
             (f crossLD = x0) ∧ (f conductORP = x1) ∧ (f moveToPB = x2) ∧
             (f conductPB = x3) ∧ (f completePB = x4) ∧ (f incomplete = x5)

   [slCommand_EQ_slCommand]  Theorem

      |- ∀a a'. (a = a') ⇔ (slCommand2num a = slCommand2num a')

   [slCommand_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3 v4 v5.
           (M = M') ∧ ((M' = crossLD) ⇒ (v0 = v0')) ∧
           ((M' = conductORP) ⇒ (v1 = v1')) ∧
           ((M' = moveToPB) ⇒ (v2 = v2')) ∧
           ((M' = conductPB) ⇒ (v3 = v3')) ∧
           ((M' = completePB) ⇒ (v4 = v4')) ∧
           ((M' = incomplete) ⇒ (v5 = v5')) ⇒
           ((case M of
               crossLD => v0
             | conductORP => v1
             | moveToPB => v2
             | conductPB => v3
             | completePB => v4
             | incomplete => v5) =
            case M' of
              crossLD => v0'
            | conductORP => v1'
            | moveToPB => v2'
            | conductPB => v3'
            | completePB => v4'
            | incomplete => v5')

   [slCommand_case_def]  Theorem

      |- (∀v0 v1 v2 v3 v4 v5.
            (case crossLD of
               crossLD => v0
             | conductORP => v1
             | moveToPB => v2
             | conductPB => v3
             | completePB => v4
             | incomplete => v5) =
            v0) ∧
         (∀v0 v1 v2 v3 v4 v5.
            (case conductORP of
               crossLD => v0
             | conductORP => v1
             | moveToPB => v2
             | conductPB => v3
             | completePB => v4
             | incomplete => v5) =
            v1) ∧
         (∀v0 v1 v2 v3 v4 v5.
            (case moveToPB of
               crossLD => v0
             | conductORP => v1
             | moveToPB => v2
             | conductPB => v3
             | completePB => v4
             | incomplete => v5) =
            v2) ∧
         (∀v0 v1 v2 v3 v4 v5.
            (case conductPB of
               crossLD => v0
             | conductORP => v1
             | moveToPB => v2
             | conductPB => v3
             | completePB => v4
             | incomplete => v5) =
            v3) ∧
         (∀v0 v1 v2 v3 v4 v5.
            (case completePB of
               crossLD => v0
             | conductORP => v1
             | moveToPB => v2
             | conductPB => v3
             | completePB => v4
             | incomplete => v5) =
            v4) ∧
         ∀v0 v1 v2 v3 v4 v5.
           (case incomplete of
              crossLD => v0
            | conductORP => v1
            | moveToPB => v2
            | conductPB => v3
            | completePB => v4
            | incomplete => v5) =
           v5

   [slCommand_distinct]  Theorem

      |- crossLD ≠ conductORP ∧ crossLD ≠ moveToPB ∧ crossLD ≠ conductPB ∧
         crossLD ≠ completePB ∧ crossLD ≠ incomplete ∧
         conductORP ≠ moveToPB ∧ conductORP ≠ conductPB ∧
         conductORP ≠ completePB ∧ conductORP ≠ incomplete ∧
         moveToPB ≠ conductPB ∧ moveToPB ≠ completePB ∧
         moveToPB ≠ incomplete ∧ conductPB ≠ completePB ∧
         conductPB ≠ incomplete ∧ completePB ≠ incomplete

   [slCommand_distinct_clauses]  Theorem

      |- crossLD ≠ conductORP ∧ crossLD ≠ moveToPB ∧ crossLD ≠ conductPB ∧
         crossLD ≠ completePB ∧ crossLD ≠ incomplete ∧
         conductORP ≠ moveToPB ∧ conductORP ≠ conductPB ∧
         conductORP ≠ completePB ∧ conductORP ≠ incomplete ∧
         moveToPB ≠ conductPB ∧ moveToPB ≠ completePB ∧
         moveToPB ≠ incomplete ∧ conductPB ≠ completePB ∧
         conductPB ≠ incomplete ∧ completePB ≠ incomplete

   [slCommand_induction]  Theorem

      |- ∀P.
           P completePB ∧ P conductORP ∧ P conductPB ∧ P crossLD ∧
           P incomplete ∧ P moveToPB ⇒
           ∀a. P a

   [slCommand_nchotomy]  Theorem

      |- ∀a.
           (a = crossLD) ∨ (a = conductORP) ∨ (a = moveToPB) ∨
           (a = conductPB) ∨ (a = completePB) ∨ (a = incomplete)

   [slOutput2num_11]  Theorem

      |- ∀a a'. (slOutput2num a = slOutput2num a') ⇔ (a = a')

   [slOutput2num_ONTO]  Theorem

      |- ∀r. r < 8 ⇔ ∃a. r = slOutput2num a

   [slOutput2num_num2slOutput]  Theorem

      |- ∀r. r < 8 ⇔ (slOutput2num (num2slOutput r) = r)

   [slOutput2num_thm]  Theorem

      |- (slOutput2num PlanPB = 0) ∧ (slOutput2num MoveToORP = 1) ∧
         (slOutput2num ConductORP = 2) ∧ (slOutput2num MoveToPB = 3) ∧
         (slOutput2num ConductPB = 4) ∧ (slOutput2num CompletePB = 5) ∧
         (slOutput2num unAuthenticated = 6) ∧
         (slOutput2num unAuthorized = 7)

   [slOutput_Axiom]  Theorem

      |- ∀x0 x1 x2 x3 x4 x5 x6 x7.
           ∃f.
             (f PlanPB = x0) ∧ (f MoveToORP = x1) ∧ (f ConductORP = x2) ∧
             (f MoveToPB = x3) ∧ (f ConductPB = x4) ∧ (f CompletePB = x5) ∧
             (f unAuthenticated = x6) ∧ (f unAuthorized = x7)

   [slOutput_EQ_slOutput]  Theorem

      |- ∀a a'. (a = a') ⇔ (slOutput2num a = slOutput2num a')

   [slOutput_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3 v4 v5 v6 v7.
           (M = M') ∧ ((M' = PlanPB) ⇒ (v0 = v0')) ∧
           ((M' = MoveToORP) ⇒ (v1 = v1')) ∧
           ((M' = ConductORP) ⇒ (v2 = v2')) ∧
           ((M' = MoveToPB) ⇒ (v3 = v3')) ∧
           ((M' = ConductPB) ⇒ (v4 = v4')) ∧
           ((M' = CompletePB) ⇒ (v5 = v5')) ∧
           ((M' = unAuthenticated) ⇒ (v6 = v6')) ∧
           ((M' = unAuthorized) ⇒ (v7 = v7')) ⇒
           ((case M of
               PlanPB => v0
             | MoveToORP => v1
             | ConductORP => v2
             | MoveToPB => v3
             | ConductPB => v4
             | CompletePB => v5
             | unAuthenticated => v6
             | unAuthorized => v7) =
            case M' of
              PlanPB => v0'
            | MoveToORP => v1'
            | ConductORP => v2'
            | MoveToPB => v3'
            | ConductPB => v4'
            | CompletePB => v5'
            | unAuthenticated => v6'
            | unAuthorized => v7')

   [slOutput_case_def]  Theorem

      |- (∀v0 v1 v2 v3 v4 v5 v6 v7.
            (case PlanPB of
               PlanPB => v0
             | MoveToORP => v1
             | ConductORP => v2
             | MoveToPB => v3
             | ConductPB => v4
             | CompletePB => v5
             | unAuthenticated => v6
             | unAuthorized => v7) =
            v0) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7.
            (case MoveToORP of
               PlanPB => v0
             | MoveToORP => v1
             | ConductORP => v2
             | MoveToPB => v3
             | ConductPB => v4
             | CompletePB => v5
             | unAuthenticated => v6
             | unAuthorized => v7) =
            v1) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7.
            (case ConductORP of
               PlanPB => v0
             | MoveToORP => v1
             | ConductORP => v2
             | MoveToPB => v3
             | ConductPB => v4
             | CompletePB => v5
             | unAuthenticated => v6
             | unAuthorized => v7) =
            v2) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7.
            (case MoveToPB of
               PlanPB => v0
             | MoveToORP => v1
             | ConductORP => v2
             | MoveToPB => v3
             | ConductPB => v4
             | CompletePB => v5
             | unAuthenticated => v6
             | unAuthorized => v7) =
            v3) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7.
            (case ConductPB of
               PlanPB => v0
             | MoveToORP => v1
             | ConductORP => v2
             | MoveToPB => v3
             | ConductPB => v4
             | CompletePB => v5
             | unAuthenticated => v6
             | unAuthorized => v7) =
            v4) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7.
            (case CompletePB of
               PlanPB => v0
             | MoveToORP => v1
             | ConductORP => v2
             | MoveToPB => v3
             | ConductPB => v4
             | CompletePB => v5
             | unAuthenticated => v6
             | unAuthorized => v7) =
            v5) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7.
            (case unAuthenticated of
               PlanPB => v0
             | MoveToORP => v1
             | ConductORP => v2
             | MoveToPB => v3
             | ConductPB => v4
             | CompletePB => v5
             | unAuthenticated => v6
             | unAuthorized => v7) =
            v6) ∧
         ∀v0 v1 v2 v3 v4 v5 v6 v7.
           (case unAuthorized of
              PlanPB => v0
            | MoveToORP => v1
            | ConductORP => v2
            | MoveToPB => v3
            | ConductPB => v4
            | CompletePB => v5
            | unAuthenticated => v6
            | unAuthorized => v7) =
           v7

   [slOutput_distinct]  Theorem

      |- PlanPB ≠ MoveToORP ∧ PlanPB ≠ ConductORP ∧ PlanPB ≠ MoveToPB ∧
         PlanPB ≠ ConductPB ∧ PlanPB ≠ CompletePB ∧
         PlanPB ≠ unAuthenticated ∧ PlanPB ≠ unAuthorized ∧
         MoveToORP ≠ ConductORP ∧ MoveToORP ≠ MoveToPB ∧
         MoveToORP ≠ ConductPB ∧ MoveToORP ≠ CompletePB ∧
         MoveToORP ≠ unAuthenticated ∧ MoveToORP ≠ unAuthorized ∧
         ConductORP ≠ MoveToPB ∧ ConductORP ≠ ConductPB ∧
         ConductORP ≠ CompletePB ∧ ConductORP ≠ unAuthenticated ∧
         ConductORP ≠ unAuthorized ∧ MoveToPB ≠ ConductPB ∧
         MoveToPB ≠ CompletePB ∧ MoveToPB ≠ unAuthenticated ∧
         MoveToPB ≠ unAuthorized ∧ ConductPB ≠ CompletePB ∧
         ConductPB ≠ unAuthenticated ∧ ConductPB ≠ unAuthorized ∧
         CompletePB ≠ unAuthenticated ∧ CompletePB ≠ unAuthorized ∧
         unAuthenticated ≠ unAuthorized

   [slOutput_distinct_clauses]  Theorem

      |- PlanPB ≠ MoveToORP ∧ PlanPB ≠ ConductORP ∧ PlanPB ≠ MoveToPB ∧
         PlanPB ≠ ConductPB ∧ PlanPB ≠ CompletePB ∧
         PlanPB ≠ unAuthenticated ∧ PlanPB ≠ unAuthorized ∧
         MoveToORP ≠ ConductORP ∧ MoveToORP ≠ MoveToPB ∧
         MoveToORP ≠ ConductPB ∧ MoveToORP ≠ CompletePB ∧
         MoveToORP ≠ unAuthenticated ∧ MoveToORP ≠ unAuthorized ∧
         ConductORP ≠ MoveToPB ∧ ConductORP ≠ ConductPB ∧
         ConductORP ≠ CompletePB ∧ ConductORP ≠ unAuthenticated ∧
         ConductORP ≠ unAuthorized ∧ MoveToPB ≠ ConductPB ∧
         MoveToPB ≠ CompletePB ∧ MoveToPB ≠ unAuthenticated ∧
         MoveToPB ≠ unAuthorized ∧ ConductPB ≠ CompletePB ∧
         ConductPB ≠ unAuthenticated ∧ ConductPB ≠ unAuthorized ∧
         CompletePB ≠ unAuthenticated ∧ CompletePB ≠ unAuthorized ∧
         unAuthenticated ≠ unAuthorized

   [slOutput_induction]  Theorem

      |- ∀P.
           P CompletePB ∧ P ConductORP ∧ P ConductPB ∧ P MoveToORP ∧
           P MoveToPB ∧ P PlanPB ∧ P unAuthenticated ∧ P unAuthorized ⇒
           ∀a. P a

   [slOutput_nchotomy]  Theorem

      |- ∀a.
           (a = PlanPB) ∨ (a = MoveToORP) ∨ (a = ConductORP) ∨
           (a = MoveToPB) ∨ (a = ConductPB) ∨ (a = CompletePB) ∨
           (a = unAuthenticated) ∨ (a = unAuthorized)

   [slState2num_11]  Theorem

      |- ∀a a'. (slState2num a = slState2num a') ⇔ (a = a')

   [slState2num_ONTO]  Theorem

      |- ∀r. r < 6 ⇔ ∃a. r = slState2num a

   [slState2num_num2slState]  Theorem

      |- ∀r. r < 6 ⇔ (slState2num (num2slState r) = r)

   [slState2num_thm]  Theorem

      |- (slState2num PLAN_PB = 0) ∧ (slState2num MOVE_TO_ORP = 1) ∧
         (slState2num CONDUCT_ORP = 2) ∧ (slState2num MOVE_TO_PB = 3) ∧
         (slState2num CONDUCT_PB = 4) ∧ (slState2num COMPLETE_PB = 5)

   [slState_Axiom]  Theorem

      |- ∀x0 x1 x2 x3 x4 x5.
           ∃f.
             (f PLAN_PB = x0) ∧ (f MOVE_TO_ORP = x1) ∧
             (f CONDUCT_ORP = x2) ∧ (f MOVE_TO_PB = x3) ∧
             (f CONDUCT_PB = x4) ∧ (f COMPLETE_PB = x5)

   [slState_EQ_slState]  Theorem

      |- ∀a a'. (a = a') ⇔ (slState2num a = slState2num a')

   [slState_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3 v4 v5.
           (M = M') ∧ ((M' = PLAN_PB) ⇒ (v0 = v0')) ∧
           ((M' = MOVE_TO_ORP) ⇒ (v1 = v1')) ∧
           ((M' = CONDUCT_ORP) ⇒ (v2 = v2')) ∧
           ((M' = MOVE_TO_PB) ⇒ (v3 = v3')) ∧
           ((M' = CONDUCT_PB) ⇒ (v4 = v4')) ∧
           ((M' = COMPLETE_PB) ⇒ (v5 = v5')) ⇒
           ((case M of
               PLAN_PB => v0
             | MOVE_TO_ORP => v1
             | CONDUCT_ORP => v2
             | MOVE_TO_PB => v3
             | CONDUCT_PB => v4
             | COMPLETE_PB => v5) =
            case M' of
              PLAN_PB => v0'
            | MOVE_TO_ORP => v1'
            | CONDUCT_ORP => v2'
            | MOVE_TO_PB => v3'
            | CONDUCT_PB => v4'
            | COMPLETE_PB => v5')

   [slState_case_def]  Theorem

      |- (∀v0 v1 v2 v3 v4 v5.
            (case PLAN_PB of
               PLAN_PB => v0
             | MOVE_TO_ORP => v1
             | CONDUCT_ORP => v2
             | MOVE_TO_PB => v3
             | CONDUCT_PB => v4
             | COMPLETE_PB => v5) =
            v0) ∧
         (∀v0 v1 v2 v3 v4 v5.
            (case MOVE_TO_ORP of
               PLAN_PB => v0
             | MOVE_TO_ORP => v1
             | CONDUCT_ORP => v2
             | MOVE_TO_PB => v3
             | CONDUCT_PB => v4
             | COMPLETE_PB => v5) =
            v1) ∧
         (∀v0 v1 v2 v3 v4 v5.
            (case CONDUCT_ORP of
               PLAN_PB => v0
             | MOVE_TO_ORP => v1
             | CONDUCT_ORP => v2
             | MOVE_TO_PB => v3
             | CONDUCT_PB => v4
             | COMPLETE_PB => v5) =
            v2) ∧
         (∀v0 v1 v2 v3 v4 v5.
            (case MOVE_TO_PB of
               PLAN_PB => v0
             | MOVE_TO_ORP => v1
             | CONDUCT_ORP => v2
             | MOVE_TO_PB => v3
             | CONDUCT_PB => v4
             | COMPLETE_PB => v5) =
            v3) ∧
         (∀v0 v1 v2 v3 v4 v5.
            (case CONDUCT_PB of
               PLAN_PB => v0
             | MOVE_TO_ORP => v1
             | CONDUCT_ORP => v2
             | MOVE_TO_PB => v3
             | CONDUCT_PB => v4
             | COMPLETE_PB => v5) =
            v4) ∧
         ∀v0 v1 v2 v3 v4 v5.
           (case COMPLETE_PB of
              PLAN_PB => v0
            | MOVE_TO_ORP => v1
            | CONDUCT_ORP => v2
            | MOVE_TO_PB => v3
            | CONDUCT_PB => v4
            | COMPLETE_PB => v5) =
           v5

   [slState_distinct]  Theorem

      |- PLAN_PB ≠ MOVE_TO_ORP ∧ PLAN_PB ≠ CONDUCT_ORP ∧
         PLAN_PB ≠ MOVE_TO_PB ∧ PLAN_PB ≠ CONDUCT_PB ∧
         PLAN_PB ≠ COMPLETE_PB ∧ MOVE_TO_ORP ≠ CONDUCT_ORP ∧
         MOVE_TO_ORP ≠ MOVE_TO_PB ∧ MOVE_TO_ORP ≠ CONDUCT_PB ∧
         MOVE_TO_ORP ≠ COMPLETE_PB ∧ CONDUCT_ORP ≠ MOVE_TO_PB ∧
         CONDUCT_ORP ≠ CONDUCT_PB ∧ CONDUCT_ORP ≠ COMPLETE_PB ∧
         MOVE_TO_PB ≠ CONDUCT_PB ∧ MOVE_TO_PB ≠ COMPLETE_PB ∧
         CONDUCT_PB ≠ COMPLETE_PB

   [slState_distinct_clauses]  Theorem

      |- PLAN_PB ≠ MOVE_TO_ORP ∧ PLAN_PB ≠ CONDUCT_ORP ∧
         PLAN_PB ≠ MOVE_TO_PB ∧ PLAN_PB ≠ CONDUCT_PB ∧
         PLAN_PB ≠ COMPLETE_PB ∧ MOVE_TO_ORP ≠ CONDUCT_ORP ∧
         MOVE_TO_ORP ≠ MOVE_TO_PB ∧ MOVE_TO_ORP ≠ CONDUCT_PB ∧
         MOVE_TO_ORP ≠ COMPLETE_PB ∧ CONDUCT_ORP ≠ MOVE_TO_PB ∧
         CONDUCT_ORP ≠ CONDUCT_PB ∧ CONDUCT_ORP ≠ COMPLETE_PB ∧
         MOVE_TO_PB ≠ CONDUCT_PB ∧ MOVE_TO_PB ≠ COMPLETE_PB ∧
         CONDUCT_PB ≠ COMPLETE_PB

   [slState_induction]  Theorem

      |- ∀P.
           P COMPLETE_PB ∧ P CONDUCT_ORP ∧ P CONDUCT_PB ∧ P MOVE_TO_ORP ∧
           P MOVE_TO_PB ∧ P PLAN_PB ⇒
           ∀a. P a

   [slState_nchotomy]  Theorem

      |- ∀a.
           (a = PLAN_PB) ∨ (a = MOVE_TO_ORP) ∨ (a = CONDUCT_ORP) ∨
           (a = MOVE_TO_PB) ∨ (a = CONDUCT_PB) ∨ (a = COMPLETE_PB)

   [stateRole2num_11]  Theorem

      |- ∀a a'. (stateRole2num a = stateRole2num a') ⇔ (a = a')

   [stateRole2num_ONTO]  Theorem

      |- ∀r. r < 1 ⇔ ∃a. r = stateRole2num a

   [stateRole2num_num2stateRole]  Theorem

      |- ∀r. r < 1 ⇔ (stateRole2num (num2stateRole r) = r)

   [stateRole2num_thm]  Theorem

      |- stateRole2num PlatoonLeader = 0

   [stateRole_Axiom]  Theorem

      |- ∀x0. ∃f. f PlatoonLeader = x0

   [stateRole_EQ_stateRole]  Theorem

      |- ∀a a'. (a = a') ⇔ (stateRole2num a = stateRole2num a')

   [stateRole_case_cong]  Theorem

      |- ∀M M' v0.
           (M = M') ∧ ((M' = PlatoonLeader) ⇒ (v0 = v0')) ⇒
           ((case M of PlatoonLeader => v0) =
            case M' of PlatoonLeader => v0')

   [stateRole_case_def]  Theorem

      |- ∀v0. (case PlatoonLeader of PlatoonLeader => v0) = v0

   [stateRole_induction]  Theorem

      |- ∀P. P PlatoonLeader ⇒ ∀a. P a

   [stateRole_nchotomy]  Theorem

      |- ∀a. a = PlatoonLeader


*)
end
