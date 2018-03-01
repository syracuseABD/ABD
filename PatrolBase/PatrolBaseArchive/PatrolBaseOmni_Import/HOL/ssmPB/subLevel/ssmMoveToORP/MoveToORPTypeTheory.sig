signature MoveToORPTypeTheory =
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

  val MoveToORPType_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [indexedLists] Parent theory of "MoveToORPType"

   [patternMatches] Parent theory of "MoveToORPType"

   [slCommand_BIJ]  Definition

      |- (∀a. num2slCommand (slCommand2num a) = a) ∧
         ∀r. (λn. n < 5) r ⇔ (slCommand2num (num2slCommand r) = r)

   [slCommand_CASE]  Definition

      |- ∀x v0 v1 v2 v3 v4.
           (case x of
              pltForm => v0
            | pltMove => v1
            | pltSecureHalt => v2
            | complete => v3
            | incomplete => v4) =
           (λm.
              if m < 2 then if m = 0 then v0 else v1
              else if m < 3 then v2
              else if m = 3 then v3
              else v4) (slCommand2num x)

   [slCommand_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 5) rep

   [slCommand_size_def]  Definition

      |- ∀x. slCommand_size x = 0

   [slOutput_BIJ]  Definition

      |- (∀a. num2slOutput (slOutput2num a) = a) ∧
         ∀r. (λn. n < 7) r ⇔ (slOutput2num (num2slOutput r) = r)

   [slOutput_CASE]  Definition

      |- ∀x v0 v1 v2 v3 v4 v5 v6.
           (case x of
              PLTPlan => v0
            | PLTForm => v1
            | PLTMove => v2
            | PLTSecureHalt => v3
            | Complete => v4
            | unAuthorized => v5
            | unAuthenticated => v6) =
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
              PLAN_PB => v0
            | PLT_FORM => v1
            | PLT_MOVE => v2
            | PLT_SECURE_HALT => v3
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
           (slCommand pltForm pltMove pltSecureHalt complete incomplete)

   [datatype_slOutput]  Theorem

      |- DATATYPE
           (slOutput PLTPlan PLTForm PLTMove PLTSecureHalt Complete
              unAuthorized unAuthenticated)

   [datatype_slState]  Theorem

      |- DATATYPE
           (slState PLAN_PB PLT_FORM PLT_MOVE PLT_SECURE_HALT COMPLETE)

   [datatype_stateRole]  Theorem

      |- DATATYPE (stateRole PlatoonLeader)

   [num2slCommand_11]  Theorem

      |- ∀r r'.
           r < 5 ⇒
           r' < 5 ⇒
           ((num2slCommand r = num2slCommand r') ⇔ (r = r'))

   [num2slCommand_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2slCommand r) ∧ r < 5

   [num2slCommand_slCommand2num]  Theorem

      |- ∀a. num2slCommand (slCommand2num a) = a

   [num2slCommand_thm]  Theorem

      |- (num2slCommand 0 = pltForm) ∧ (num2slCommand 1 = pltMove) ∧
         (num2slCommand 2 = pltSecureHalt) ∧ (num2slCommand 3 = complete) ∧
         (num2slCommand 4 = incomplete)

   [num2slOutput_11]  Theorem

      |- ∀r r'.
           r < 7 ⇒ r' < 7 ⇒ ((num2slOutput r = num2slOutput r') ⇔ (r = r'))

   [num2slOutput_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2slOutput r) ∧ r < 7

   [num2slOutput_slOutput2num]  Theorem

      |- ∀a. num2slOutput (slOutput2num a) = a

   [num2slOutput_thm]  Theorem

      |- (num2slOutput 0 = PLTPlan) ∧ (num2slOutput 1 = PLTForm) ∧
         (num2slOutput 2 = PLTMove) ∧ (num2slOutput 3 = PLTSecureHalt) ∧
         (num2slOutput 4 = Complete) ∧ (num2slOutput 5 = unAuthorized) ∧
         (num2slOutput 6 = unAuthenticated)

   [num2slState_11]  Theorem

      |- ∀r r'.
           r < 5 ⇒ r' < 5 ⇒ ((num2slState r = num2slState r') ⇔ (r = r'))

   [num2slState_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2slState r) ∧ r < 5

   [num2slState_slState2num]  Theorem

      |- ∀a. num2slState (slState2num a) = a

   [num2slState_thm]  Theorem

      |- (num2slState 0 = PLAN_PB) ∧ (num2slState 1 = PLT_FORM) ∧
         (num2slState 2 = PLT_MOVE) ∧ (num2slState 3 = PLT_SECURE_HALT) ∧
         (num2slState 4 = COMPLETE)

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

      |- ∀r. r < 5 ⇔ ∃a. r = slCommand2num a

   [slCommand2num_num2slCommand]  Theorem

      |- ∀r. r < 5 ⇔ (slCommand2num (num2slCommand r) = r)

   [slCommand2num_thm]  Theorem

      |- (slCommand2num pltForm = 0) ∧ (slCommand2num pltMove = 1) ∧
         (slCommand2num pltSecureHalt = 2) ∧ (slCommand2num complete = 3) ∧
         (slCommand2num incomplete = 4)

   [slCommand_Axiom]  Theorem

      |- ∀x0 x1 x2 x3 x4.
           ∃f.
             (f pltForm = x0) ∧ (f pltMove = x1) ∧ (f pltSecureHalt = x2) ∧
             (f complete = x3) ∧ (f incomplete = x4)

   [slCommand_EQ_slCommand]  Theorem

      |- ∀a a'. (a = a') ⇔ (slCommand2num a = slCommand2num a')

   [slCommand_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3 v4.
           (M = M') ∧ ((M' = pltForm) ⇒ (v0 = v0')) ∧
           ((M' = pltMove) ⇒ (v1 = v1')) ∧
           ((M' = pltSecureHalt) ⇒ (v2 = v2')) ∧
           ((M' = complete) ⇒ (v3 = v3')) ∧
           ((M' = incomplete) ⇒ (v4 = v4')) ⇒
           ((case M of
               pltForm => v0
             | pltMove => v1
             | pltSecureHalt => v2
             | complete => v3
             | incomplete => v4) =
            case M' of
              pltForm => v0'
            | pltMove => v1'
            | pltSecureHalt => v2'
            | complete => v3'
            | incomplete => v4')

   [slCommand_case_def]  Theorem

      |- (∀v0 v1 v2 v3 v4.
            (case pltForm of
               pltForm => v0
             | pltMove => v1
             | pltSecureHalt => v2
             | complete => v3
             | incomplete => v4) =
            v0) ∧
         (∀v0 v1 v2 v3 v4.
            (case pltMove of
               pltForm => v0
             | pltMove => v1
             | pltSecureHalt => v2
             | complete => v3
             | incomplete => v4) =
            v1) ∧
         (∀v0 v1 v2 v3 v4.
            (case pltSecureHalt of
               pltForm => v0
             | pltMove => v1
             | pltSecureHalt => v2
             | complete => v3
             | incomplete => v4) =
            v2) ∧
         (∀v0 v1 v2 v3 v4.
            (case complete of
               pltForm => v0
             | pltMove => v1
             | pltSecureHalt => v2
             | complete => v3
             | incomplete => v4) =
            v3) ∧
         ∀v0 v1 v2 v3 v4.
           (case incomplete of
              pltForm => v0
            | pltMove => v1
            | pltSecureHalt => v2
            | complete => v3
            | incomplete => v4) =
           v4

   [slCommand_distinct]  Theorem

      |- pltForm ≠ pltMove ∧ pltForm ≠ pltSecureHalt ∧ pltForm ≠ complete ∧
         pltForm ≠ incomplete ∧ pltMove ≠ pltSecureHalt ∧
         pltMove ≠ complete ∧ pltMove ≠ incomplete ∧
         pltSecureHalt ≠ complete ∧ pltSecureHalt ≠ incomplete ∧
         complete ≠ incomplete

   [slCommand_distinct_clauses]  Theorem

      |- pltForm ≠ pltMove ∧ pltForm ≠ pltSecureHalt ∧ pltForm ≠ complete ∧
         pltForm ≠ incomplete ∧ pltMove ≠ pltSecureHalt ∧
         pltMove ≠ complete ∧ pltMove ≠ incomplete ∧
         pltSecureHalt ≠ complete ∧ pltSecureHalt ≠ incomplete ∧
         complete ≠ incomplete

   [slCommand_induction]  Theorem

      |- ∀P.
           P complete ∧ P incomplete ∧ P pltForm ∧ P pltMove ∧
           P pltSecureHalt ⇒
           ∀a. P a

   [slCommand_nchotomy]  Theorem

      |- ∀a.
           (a = pltForm) ∨ (a = pltMove) ∨ (a = pltSecureHalt) ∨
           (a = complete) ∨ (a = incomplete)

   [slOutput2num_11]  Theorem

      |- ∀a a'. (slOutput2num a = slOutput2num a') ⇔ (a = a')

   [slOutput2num_ONTO]  Theorem

      |- ∀r. r < 7 ⇔ ∃a. r = slOutput2num a

   [slOutput2num_num2slOutput]  Theorem

      |- ∀r. r < 7 ⇔ (slOutput2num (num2slOutput r) = r)

   [slOutput2num_thm]  Theorem

      |- (slOutput2num PLTPlan = 0) ∧ (slOutput2num PLTForm = 1) ∧
         (slOutput2num PLTMove = 2) ∧ (slOutput2num PLTSecureHalt = 3) ∧
         (slOutput2num Complete = 4) ∧ (slOutput2num unAuthorized = 5) ∧
         (slOutput2num unAuthenticated = 6)

   [slOutput_Axiom]  Theorem

      |- ∀x0 x1 x2 x3 x4 x5 x6.
           ∃f.
             (f PLTPlan = x0) ∧ (f PLTForm = x1) ∧ (f PLTMove = x2) ∧
             (f PLTSecureHalt = x3) ∧ (f Complete = x4) ∧
             (f unAuthorized = x5) ∧ (f unAuthenticated = x6)

   [slOutput_EQ_slOutput]  Theorem

      |- ∀a a'. (a = a') ⇔ (slOutput2num a = slOutput2num a')

   [slOutput_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3 v4 v5 v6.
           (M = M') ∧ ((M' = PLTPlan) ⇒ (v0 = v0')) ∧
           ((M' = PLTForm) ⇒ (v1 = v1')) ∧ ((M' = PLTMove) ⇒ (v2 = v2')) ∧
           ((M' = PLTSecureHalt) ⇒ (v3 = v3')) ∧
           ((M' = Complete) ⇒ (v4 = v4')) ∧
           ((M' = unAuthorized) ⇒ (v5 = v5')) ∧
           ((M' = unAuthenticated) ⇒ (v6 = v6')) ⇒
           ((case M of
               PLTPlan => v0
             | PLTForm => v1
             | PLTMove => v2
             | PLTSecureHalt => v3
             | Complete => v4
             | unAuthorized => v5
             | unAuthenticated => v6) =
            case M' of
              PLTPlan => v0'
            | PLTForm => v1'
            | PLTMove => v2'
            | PLTSecureHalt => v3'
            | Complete => v4'
            | unAuthorized => v5'
            | unAuthenticated => v6')

   [slOutput_case_def]  Theorem

      |- (∀v0 v1 v2 v3 v4 v5 v6.
            (case PLTPlan of
               PLTPlan => v0
             | PLTForm => v1
             | PLTMove => v2
             | PLTSecureHalt => v3
             | Complete => v4
             | unAuthorized => v5
             | unAuthenticated => v6) =
            v0) ∧
         (∀v0 v1 v2 v3 v4 v5 v6.
            (case PLTForm of
               PLTPlan => v0
             | PLTForm => v1
             | PLTMove => v2
             | PLTSecureHalt => v3
             | Complete => v4
             | unAuthorized => v5
             | unAuthenticated => v6) =
            v1) ∧
         (∀v0 v1 v2 v3 v4 v5 v6.
            (case PLTMove of
               PLTPlan => v0
             | PLTForm => v1
             | PLTMove => v2
             | PLTSecureHalt => v3
             | Complete => v4
             | unAuthorized => v5
             | unAuthenticated => v6) =
            v2) ∧
         (∀v0 v1 v2 v3 v4 v5 v6.
            (case PLTSecureHalt of
               PLTPlan => v0
             | PLTForm => v1
             | PLTMove => v2
             | PLTSecureHalt => v3
             | Complete => v4
             | unAuthorized => v5
             | unAuthenticated => v6) =
            v3) ∧
         (∀v0 v1 v2 v3 v4 v5 v6.
            (case Complete of
               PLTPlan => v0
             | PLTForm => v1
             | PLTMove => v2
             | PLTSecureHalt => v3
             | Complete => v4
             | unAuthorized => v5
             | unAuthenticated => v6) =
            v4) ∧
         (∀v0 v1 v2 v3 v4 v5 v6.
            (case unAuthorized of
               PLTPlan => v0
             | PLTForm => v1
             | PLTMove => v2
             | PLTSecureHalt => v3
             | Complete => v4
             | unAuthorized => v5
             | unAuthenticated => v6) =
            v5) ∧
         ∀v0 v1 v2 v3 v4 v5 v6.
           (case unAuthenticated of
              PLTPlan => v0
            | PLTForm => v1
            | PLTMove => v2
            | PLTSecureHalt => v3
            | Complete => v4
            | unAuthorized => v5
            | unAuthenticated => v6) =
           v6

   [slOutput_distinct]  Theorem

      |- PLTPlan ≠ PLTForm ∧ PLTPlan ≠ PLTMove ∧ PLTPlan ≠ PLTSecureHalt ∧
         PLTPlan ≠ Complete ∧ PLTPlan ≠ unAuthorized ∧
         PLTPlan ≠ unAuthenticated ∧ PLTForm ≠ PLTMove ∧
         PLTForm ≠ PLTSecureHalt ∧ PLTForm ≠ Complete ∧
         PLTForm ≠ unAuthorized ∧ PLTForm ≠ unAuthenticated ∧
         PLTMove ≠ PLTSecureHalt ∧ PLTMove ≠ Complete ∧
         PLTMove ≠ unAuthorized ∧ PLTMove ≠ unAuthenticated ∧
         PLTSecureHalt ≠ Complete ∧ PLTSecureHalt ≠ unAuthorized ∧
         PLTSecureHalt ≠ unAuthenticated ∧ Complete ≠ unAuthorized ∧
         Complete ≠ unAuthenticated ∧ unAuthorized ≠ unAuthenticated

   [slOutput_distinct_clauses]  Theorem

      |- PLTPlan ≠ PLTForm ∧ PLTPlan ≠ PLTMove ∧ PLTPlan ≠ PLTSecureHalt ∧
         PLTPlan ≠ Complete ∧ PLTPlan ≠ unAuthorized ∧
         PLTPlan ≠ unAuthenticated ∧ PLTForm ≠ PLTMove ∧
         PLTForm ≠ PLTSecureHalt ∧ PLTForm ≠ Complete ∧
         PLTForm ≠ unAuthorized ∧ PLTForm ≠ unAuthenticated ∧
         PLTMove ≠ PLTSecureHalt ∧ PLTMove ≠ Complete ∧
         PLTMove ≠ unAuthorized ∧ PLTMove ≠ unAuthenticated ∧
         PLTSecureHalt ≠ Complete ∧ PLTSecureHalt ≠ unAuthorized ∧
         PLTSecureHalt ≠ unAuthenticated ∧ Complete ≠ unAuthorized ∧
         Complete ≠ unAuthenticated ∧ unAuthorized ≠ unAuthenticated

   [slOutput_induction]  Theorem

      |- ∀P.
           P Complete ∧ P PLTForm ∧ P PLTMove ∧ P PLTPlan ∧
           P PLTSecureHalt ∧ P unAuthenticated ∧ P unAuthorized ⇒
           ∀a. P a

   [slOutput_nchotomy]  Theorem

      |- ∀a.
           (a = PLTPlan) ∨ (a = PLTForm) ∨ (a = PLTMove) ∨
           (a = PLTSecureHalt) ∨ (a = Complete) ∨ (a = unAuthorized) ∨
           (a = unAuthenticated)

   [slState2num_11]  Theorem

      |- ∀a a'. (slState2num a = slState2num a') ⇔ (a = a')

   [slState2num_ONTO]  Theorem

      |- ∀r. r < 5 ⇔ ∃a. r = slState2num a

   [slState2num_num2slState]  Theorem

      |- ∀r. r < 5 ⇔ (slState2num (num2slState r) = r)

   [slState2num_thm]  Theorem

      |- (slState2num PLAN_PB = 0) ∧ (slState2num PLT_FORM = 1) ∧
         (slState2num PLT_MOVE = 2) ∧ (slState2num PLT_SECURE_HALT = 3) ∧
         (slState2num COMPLETE = 4)

   [slState_Axiom]  Theorem

      |- ∀x0 x1 x2 x3 x4.
           ∃f.
             (f PLAN_PB = x0) ∧ (f PLT_FORM = x1) ∧ (f PLT_MOVE = x2) ∧
             (f PLT_SECURE_HALT = x3) ∧ (f COMPLETE = x4)

   [slState_EQ_slState]  Theorem

      |- ∀a a'. (a = a') ⇔ (slState2num a = slState2num a')

   [slState_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3 v4.
           (M = M') ∧ ((M' = PLAN_PB) ⇒ (v0 = v0')) ∧
           ((M' = PLT_FORM) ⇒ (v1 = v1')) ∧
           ((M' = PLT_MOVE) ⇒ (v2 = v2')) ∧
           ((M' = PLT_SECURE_HALT) ⇒ (v3 = v3')) ∧
           ((M' = COMPLETE) ⇒ (v4 = v4')) ⇒
           ((case M of
               PLAN_PB => v0
             | PLT_FORM => v1
             | PLT_MOVE => v2
             | PLT_SECURE_HALT => v3
             | COMPLETE => v4) =
            case M' of
              PLAN_PB => v0'
            | PLT_FORM => v1'
            | PLT_MOVE => v2'
            | PLT_SECURE_HALT => v3'
            | COMPLETE => v4')

   [slState_case_def]  Theorem

      |- (∀v0 v1 v2 v3 v4.
            (case PLAN_PB of
               PLAN_PB => v0
             | PLT_FORM => v1
             | PLT_MOVE => v2
             | PLT_SECURE_HALT => v3
             | COMPLETE => v4) =
            v0) ∧
         (∀v0 v1 v2 v3 v4.
            (case PLT_FORM of
               PLAN_PB => v0
             | PLT_FORM => v1
             | PLT_MOVE => v2
             | PLT_SECURE_HALT => v3
             | COMPLETE => v4) =
            v1) ∧
         (∀v0 v1 v2 v3 v4.
            (case PLT_MOVE of
               PLAN_PB => v0
             | PLT_FORM => v1
             | PLT_MOVE => v2
             | PLT_SECURE_HALT => v3
             | COMPLETE => v4) =
            v2) ∧
         (∀v0 v1 v2 v3 v4.
            (case PLT_SECURE_HALT of
               PLAN_PB => v0
             | PLT_FORM => v1
             | PLT_MOVE => v2
             | PLT_SECURE_HALT => v3
             | COMPLETE => v4) =
            v3) ∧
         ∀v0 v1 v2 v3 v4.
           (case COMPLETE of
              PLAN_PB => v0
            | PLT_FORM => v1
            | PLT_MOVE => v2
            | PLT_SECURE_HALT => v3
            | COMPLETE => v4) =
           v4

   [slState_distinct]  Theorem

      |- PLAN_PB ≠ PLT_FORM ∧ PLAN_PB ≠ PLT_MOVE ∧
         PLAN_PB ≠ PLT_SECURE_HALT ∧ PLAN_PB ≠ COMPLETE ∧
         PLT_FORM ≠ PLT_MOVE ∧ PLT_FORM ≠ PLT_SECURE_HALT ∧
         PLT_FORM ≠ COMPLETE ∧ PLT_MOVE ≠ PLT_SECURE_HALT ∧
         PLT_MOVE ≠ COMPLETE ∧ PLT_SECURE_HALT ≠ COMPLETE

   [slState_distinct_clauses]  Theorem

      |- PLAN_PB ≠ PLT_FORM ∧ PLAN_PB ≠ PLT_MOVE ∧
         PLAN_PB ≠ PLT_SECURE_HALT ∧ PLAN_PB ≠ COMPLETE ∧
         PLT_FORM ≠ PLT_MOVE ∧ PLT_FORM ≠ PLT_SECURE_HALT ∧
         PLT_FORM ≠ COMPLETE ∧ PLT_MOVE ≠ PLT_SECURE_HALT ∧
         PLT_MOVE ≠ COMPLETE ∧ PLT_SECURE_HALT ≠ COMPLETE

   [slState_induction]  Theorem

      |- ∀P.
           P COMPLETE ∧ P PLAN_PB ∧ P PLT_FORM ∧ P PLT_MOVE ∧
           P PLT_SECURE_HALT ⇒
           ∀a. P a

   [slState_nchotomy]  Theorem

      |- ∀a.
           (a = PLAN_PB) ∨ (a = PLT_FORM) ∨ (a = PLT_MOVE) ∨
           (a = PLT_SECURE_HALT) ∨ (a = COMPLETE)

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
