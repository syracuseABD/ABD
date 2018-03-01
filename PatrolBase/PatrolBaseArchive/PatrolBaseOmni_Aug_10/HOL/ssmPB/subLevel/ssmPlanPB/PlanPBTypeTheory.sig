signature PlanPBTypeTheory =
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

  val PlanPBType_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [indexedLists] Parent theory of "PlanPBType"

   [patternMatches] Parent theory of "PlanPBType"

   [plCommand_BIJ]  Definition

      |- (∀a. num2plCommand (plCommand2num a) = a) ∧
         ∀r. (λn. n < 6) r ⇔ (plCommand2num (num2plCommand r) = r)

   [plCommand_CASE]  Definition

      |- ∀x v0 v1 v2 v3 v4 v5.
           (case x of
              receiveMission => v0
            | warno => v1
            | tentativePlan => v2
            | recon => v3
            | complete => v4
            | plIncomplete => v5) =
           (λm.
              if m < 2 then if m = 0 then v0 else v1
              else if m < 3 then v2
              else if m < 4 then v3
              else if m = 4 then v4
              else v5) (plCommand2num x)

   [plCommand_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 6) rep

   [plCommand_size_def]  Definition

      |- ∀x. plCommand_size x = 0

   [psgCommand_BIJ]  Definition

      |- (∀a. num2psgCommand (psgCommand2num a) = a) ∧
         ∀r. (λn. n < 2) r ⇔ (psgCommand2num (num2psgCommand r) = r)

   [psgCommand_CASE]  Definition

      |- ∀x v0 v1.
           (case x of initiateMovement => v0 | psgIncomplete => v1) =
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
         ∀r. (λn. n < 8) r ⇔ (slOutput2num (num2slOutput r) = r)

   [slOutput_CASE]  Definition

      |- ∀x v0 v1 v2 v3 v4 v5 v6 v7.
           (case x of
              ReceiveMission => v0
            | Warno => v1
            | TentativePlan => v2
            | InitiateMovement => v3
            | Recon => v4
            | Complete => v5
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
              RECEIVE_MISSION => v0
            | WARNO => v1
            | TENTATIVE_PLAN => v2
            | INITIATE_MOVEMENT => v3
            | RECON => v4
            | COMPLETE => v5) =
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

      |- DATATYPE
           (plCommand receiveMission warno tentativePlan recon complete
              plIncomplete)

   [datatype_psgCommand]  Theorem

      |- DATATYPE (psgCommand initiateMovement psgIncomplete)

   [datatype_slCommand]  Theorem

      |- DATATYPE (slCommand PL PSG)

   [datatype_slOutput]  Theorem

      |- DATATYPE
           (slOutput ReceiveMission Warno TentativePlan InitiateMovement
              Recon Complete unAuthenticated unAuthorized)

   [datatype_slState]  Theorem

      |- DATATYPE
           (slState RECEIVE_MISSION WARNO TENTATIVE_PLAN INITIATE_MOVEMENT
              RECON COMPLETE)

   [datatype_stateRole]  Theorem

      |- DATATYPE (stateRole PlatoonLeader PlatoonSergeant)

   [num2plCommand_11]  Theorem

      |- ∀r r'.
           r < 6 ⇒
           r' < 6 ⇒
           ((num2plCommand r = num2plCommand r') ⇔ (r = r'))

   [num2plCommand_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2plCommand r) ∧ r < 6

   [num2plCommand_plCommand2num]  Theorem

      |- ∀a. num2plCommand (plCommand2num a) = a

   [num2plCommand_thm]  Theorem

      |- (num2plCommand 0 = receiveMission) ∧ (num2plCommand 1 = warno) ∧
         (num2plCommand 2 = tentativePlan) ∧ (num2plCommand 3 = recon) ∧
         (num2plCommand 4 = complete) ∧ (num2plCommand 5 = plIncomplete)

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

      |- (num2psgCommand 0 = initiateMovement) ∧
         (num2psgCommand 1 = psgIncomplete)

   [num2slOutput_11]  Theorem

      |- ∀r r'.
           r < 8 ⇒ r' < 8 ⇒ ((num2slOutput r = num2slOutput r') ⇔ (r = r'))

   [num2slOutput_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2slOutput r) ∧ r < 8

   [num2slOutput_slOutput2num]  Theorem

      |- ∀a. num2slOutput (slOutput2num a) = a

   [num2slOutput_thm]  Theorem

      |- (num2slOutput 0 = ReceiveMission) ∧ (num2slOutput 1 = Warno) ∧
         (num2slOutput 2 = TentativePlan) ∧
         (num2slOutput 3 = InitiateMovement) ∧ (num2slOutput 4 = Recon) ∧
         (num2slOutput 5 = Complete) ∧ (num2slOutput 6 = unAuthenticated) ∧
         (num2slOutput 7 = unAuthorized)

   [num2slState_11]  Theorem

      |- ∀r r'.
           r < 6 ⇒ r' < 6 ⇒ ((num2slState r = num2slState r') ⇔ (r = r'))

   [num2slState_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2slState r) ∧ r < 6

   [num2slState_slState2num]  Theorem

      |- ∀a. num2slState (slState2num a) = a

   [num2slState_thm]  Theorem

      |- (num2slState 0 = RECEIVE_MISSION) ∧ (num2slState 1 = WARNO) ∧
         (num2slState 2 = TENTATIVE_PLAN) ∧
         (num2slState 3 = INITIATE_MOVEMENT) ∧ (num2slState 4 = RECON) ∧
         (num2slState 5 = COMPLETE)

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

      |- ∀r. r < 6 ⇔ ∃a. r = plCommand2num a

   [plCommand2num_num2plCommand]  Theorem

      |- ∀r. r < 6 ⇔ (plCommand2num (num2plCommand r) = r)

   [plCommand2num_thm]  Theorem

      |- (plCommand2num receiveMission = 0) ∧ (plCommand2num warno = 1) ∧
         (plCommand2num tentativePlan = 2) ∧ (plCommand2num recon = 3) ∧
         (plCommand2num complete = 4) ∧ (plCommand2num plIncomplete = 5)

   [plCommand_Axiom]  Theorem

      |- ∀x0 x1 x2 x3 x4 x5.
           ∃f.
             (f receiveMission = x0) ∧ (f warno = x1) ∧
             (f tentativePlan = x2) ∧ (f recon = x3) ∧ (f complete = x4) ∧
             (f plIncomplete = x5)

   [plCommand_EQ_plCommand]  Theorem

      |- ∀a a'. (a = a') ⇔ (plCommand2num a = plCommand2num a')

   [plCommand_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3 v4 v5.
           (M = M') ∧ ((M' = receiveMission) ⇒ (v0 = v0')) ∧
           ((M' = warno) ⇒ (v1 = v1')) ∧
           ((M' = tentativePlan) ⇒ (v2 = v2')) ∧
           ((M' = recon) ⇒ (v3 = v3')) ∧ ((M' = complete) ⇒ (v4 = v4')) ∧
           ((M' = plIncomplete) ⇒ (v5 = v5')) ⇒
           ((case M of
               receiveMission => v0
             | warno => v1
             | tentativePlan => v2
             | recon => v3
             | complete => v4
             | plIncomplete => v5) =
            case M' of
              receiveMission => v0'
            | warno => v1'
            | tentativePlan => v2'
            | recon => v3'
            | complete => v4'
            | plIncomplete => v5')

   [plCommand_case_def]  Theorem

      |- (∀v0 v1 v2 v3 v4 v5.
            (case receiveMission of
               receiveMission => v0
             | warno => v1
             | tentativePlan => v2
             | recon => v3
             | complete => v4
             | plIncomplete => v5) =
            v0) ∧
         (∀v0 v1 v2 v3 v4 v5.
            (case warno of
               receiveMission => v0
             | warno => v1
             | tentativePlan => v2
             | recon => v3
             | complete => v4
             | plIncomplete => v5) =
            v1) ∧
         (∀v0 v1 v2 v3 v4 v5.
            (case tentativePlan of
               receiveMission => v0
             | warno => v1
             | tentativePlan => v2
             | recon => v3
             | complete => v4
             | plIncomplete => v5) =
            v2) ∧
         (∀v0 v1 v2 v3 v4 v5.
            (case recon of
               receiveMission => v0
             | warno => v1
             | tentativePlan => v2
             | recon => v3
             | complete => v4
             | plIncomplete => v5) =
            v3) ∧
         (∀v0 v1 v2 v3 v4 v5.
            (case complete of
               receiveMission => v0
             | warno => v1
             | tentativePlan => v2
             | recon => v3
             | complete => v4
             | plIncomplete => v5) =
            v4) ∧
         ∀v0 v1 v2 v3 v4 v5.
           (case plIncomplete of
              receiveMission => v0
            | warno => v1
            | tentativePlan => v2
            | recon => v3
            | complete => v4
            | plIncomplete => v5) =
           v5

   [plCommand_distinct]  Theorem

      |- receiveMission ≠ warno ∧ receiveMission ≠ tentativePlan ∧
         receiveMission ≠ recon ∧ receiveMission ≠ complete ∧
         receiveMission ≠ plIncomplete ∧ warno ≠ tentativePlan ∧
         warno ≠ recon ∧ warno ≠ complete ∧ warno ≠ plIncomplete ∧
         tentativePlan ≠ recon ∧ tentativePlan ≠ complete ∧
         tentativePlan ≠ plIncomplete ∧ recon ≠ complete ∧
         recon ≠ plIncomplete ∧ complete ≠ plIncomplete

   [plCommand_distinct_clauses]  Theorem

      |- receiveMission ≠ warno ∧ receiveMission ≠ tentativePlan ∧
         receiveMission ≠ recon ∧ receiveMission ≠ complete ∧
         receiveMission ≠ plIncomplete ∧ warno ≠ tentativePlan ∧
         warno ≠ recon ∧ warno ≠ complete ∧ warno ≠ plIncomplete ∧
         tentativePlan ≠ recon ∧ tentativePlan ≠ complete ∧
         tentativePlan ≠ plIncomplete ∧ recon ≠ complete ∧
         recon ≠ plIncomplete ∧ complete ≠ plIncomplete

   [plCommand_induction]  Theorem

      |- ∀P.
           P complete ∧ P plIncomplete ∧ P receiveMission ∧ P recon ∧
           P tentativePlan ∧ P warno ⇒
           ∀a. P a

   [plCommand_nchotomy]  Theorem

      |- ∀a.
           (a = receiveMission) ∨ (a = warno) ∨ (a = tentativePlan) ∨
           (a = recon) ∨ (a = complete) ∨ (a = plIncomplete)

   [psgCommand2num_11]  Theorem

      |- ∀a a'. (psgCommand2num a = psgCommand2num a') ⇔ (a = a')

   [psgCommand2num_ONTO]  Theorem

      |- ∀r. r < 2 ⇔ ∃a. r = psgCommand2num a

   [psgCommand2num_num2psgCommand]  Theorem

      |- ∀r. r < 2 ⇔ (psgCommand2num (num2psgCommand r) = r)

   [psgCommand2num_thm]  Theorem

      |- (psgCommand2num initiateMovement = 0) ∧
         (psgCommand2num psgIncomplete = 1)

   [psgCommand_Axiom]  Theorem

      |- ∀x0 x1. ∃f. (f initiateMovement = x0) ∧ (f psgIncomplete = x1)

   [psgCommand_EQ_psgCommand]  Theorem

      |- ∀a a'. (a = a') ⇔ (psgCommand2num a = psgCommand2num a')

   [psgCommand_case_cong]  Theorem

      |- ∀M M' v0 v1.
           (M = M') ∧ ((M' = initiateMovement) ⇒ (v0 = v0')) ∧
           ((M' = psgIncomplete) ⇒ (v1 = v1')) ⇒
           ((case M of initiateMovement => v0 | psgIncomplete => v1) =
            case M' of initiateMovement => v0' | psgIncomplete => v1')

   [psgCommand_case_def]  Theorem

      |- (∀v0 v1.
            (case initiateMovement of
               initiateMovement => v0
             | psgIncomplete => v1) =
            v0) ∧
         ∀v0 v1.
           (case psgIncomplete of
              initiateMovement => v0
            | psgIncomplete => v1) =
           v1

   [psgCommand_distinct]  Theorem

      |- initiateMovement ≠ psgIncomplete

   [psgCommand_distinct_clauses]  Theorem

      |- initiateMovement ≠ psgIncomplete

   [psgCommand_induction]  Theorem

      |- ∀P. P initiateMovement ∧ P psgIncomplete ⇒ ∀a. P a

   [psgCommand_nchotomy]  Theorem

      |- ∀a. (a = initiateMovement) ∨ (a = psgIncomplete)

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

      |- ∀r. r < 8 ⇔ ∃a. r = slOutput2num a

   [slOutput2num_num2slOutput]  Theorem

      |- ∀r. r < 8 ⇔ (slOutput2num (num2slOutput r) = r)

   [slOutput2num_thm]  Theorem

      |- (slOutput2num ReceiveMission = 0) ∧ (slOutput2num Warno = 1) ∧
         (slOutput2num TentativePlan = 2) ∧
         (slOutput2num InitiateMovement = 3) ∧ (slOutput2num Recon = 4) ∧
         (slOutput2num Complete = 5) ∧ (slOutput2num unAuthenticated = 6) ∧
         (slOutput2num unAuthorized = 7)

   [slOutput_Axiom]  Theorem

      |- ∀x0 x1 x2 x3 x4 x5 x6 x7.
           ∃f.
             (f ReceiveMission = x0) ∧ (f Warno = x1) ∧
             (f TentativePlan = x2) ∧ (f InitiateMovement = x3) ∧
             (f Recon = x4) ∧ (f Complete = x5) ∧
             (f unAuthenticated = x6) ∧ (f unAuthorized = x7)

   [slOutput_EQ_slOutput]  Theorem

      |- ∀a a'. (a = a') ⇔ (slOutput2num a = slOutput2num a')

   [slOutput_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3 v4 v5 v6 v7.
           (M = M') ∧ ((M' = ReceiveMission) ⇒ (v0 = v0')) ∧
           ((M' = Warno) ⇒ (v1 = v1')) ∧
           ((M' = TentativePlan) ⇒ (v2 = v2')) ∧
           ((M' = InitiateMovement) ⇒ (v3 = v3')) ∧
           ((M' = Recon) ⇒ (v4 = v4')) ∧ ((M' = Complete) ⇒ (v5 = v5')) ∧
           ((M' = unAuthenticated) ⇒ (v6 = v6')) ∧
           ((M' = unAuthorized) ⇒ (v7 = v7')) ⇒
           ((case M of
               ReceiveMission => v0
             | Warno => v1
             | TentativePlan => v2
             | InitiateMovement => v3
             | Recon => v4
             | Complete => v5
             | unAuthenticated => v6
             | unAuthorized => v7) =
            case M' of
              ReceiveMission => v0'
            | Warno => v1'
            | TentativePlan => v2'
            | InitiateMovement => v3'
            | Recon => v4'
            | Complete => v5'
            | unAuthenticated => v6'
            | unAuthorized => v7')

   [slOutput_case_def]  Theorem

      |- (∀v0 v1 v2 v3 v4 v5 v6 v7.
            (case ReceiveMission of
               ReceiveMission => v0
             | Warno => v1
             | TentativePlan => v2
             | InitiateMovement => v3
             | Recon => v4
             | Complete => v5
             | unAuthenticated => v6
             | unAuthorized => v7) =
            v0) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7.
            (case Warno of
               ReceiveMission => v0
             | Warno => v1
             | TentativePlan => v2
             | InitiateMovement => v3
             | Recon => v4
             | Complete => v5
             | unAuthenticated => v6
             | unAuthorized => v7) =
            v1) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7.
            (case TentativePlan of
               ReceiveMission => v0
             | Warno => v1
             | TentativePlan => v2
             | InitiateMovement => v3
             | Recon => v4
             | Complete => v5
             | unAuthenticated => v6
             | unAuthorized => v7) =
            v2) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7.
            (case InitiateMovement of
               ReceiveMission => v0
             | Warno => v1
             | TentativePlan => v2
             | InitiateMovement => v3
             | Recon => v4
             | Complete => v5
             | unAuthenticated => v6
             | unAuthorized => v7) =
            v3) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7.
            (case Recon of
               ReceiveMission => v0
             | Warno => v1
             | TentativePlan => v2
             | InitiateMovement => v3
             | Recon => v4
             | Complete => v5
             | unAuthenticated => v6
             | unAuthorized => v7) =
            v4) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7.
            (case Complete of
               ReceiveMission => v0
             | Warno => v1
             | TentativePlan => v2
             | InitiateMovement => v3
             | Recon => v4
             | Complete => v5
             | unAuthenticated => v6
             | unAuthorized => v7) =
            v5) ∧
         (∀v0 v1 v2 v3 v4 v5 v6 v7.
            (case unAuthenticated of
               ReceiveMission => v0
             | Warno => v1
             | TentativePlan => v2
             | InitiateMovement => v3
             | Recon => v4
             | Complete => v5
             | unAuthenticated => v6
             | unAuthorized => v7) =
            v6) ∧
         ∀v0 v1 v2 v3 v4 v5 v6 v7.
           (case unAuthorized of
              ReceiveMission => v0
            | Warno => v1
            | TentativePlan => v2
            | InitiateMovement => v3
            | Recon => v4
            | Complete => v5
            | unAuthenticated => v6
            | unAuthorized => v7) =
           v7

   [slOutput_distinct]  Theorem

      |- ReceiveMission ≠ Warno ∧ ReceiveMission ≠ TentativePlan ∧
         ReceiveMission ≠ InitiateMovement ∧ ReceiveMission ≠ Recon ∧
         ReceiveMission ≠ Complete ∧ ReceiveMission ≠ unAuthenticated ∧
         ReceiveMission ≠ unAuthorized ∧ Warno ≠ TentativePlan ∧
         Warno ≠ InitiateMovement ∧ Warno ≠ Recon ∧ Warno ≠ Complete ∧
         Warno ≠ unAuthenticated ∧ Warno ≠ unAuthorized ∧
         TentativePlan ≠ InitiateMovement ∧ TentativePlan ≠ Recon ∧
         TentativePlan ≠ Complete ∧ TentativePlan ≠ unAuthenticated ∧
         TentativePlan ≠ unAuthorized ∧ InitiateMovement ≠ Recon ∧
         InitiateMovement ≠ Complete ∧ InitiateMovement ≠ unAuthenticated ∧
         InitiateMovement ≠ unAuthorized ∧ Recon ≠ Complete ∧
         Recon ≠ unAuthenticated ∧ Recon ≠ unAuthorized ∧
         Complete ≠ unAuthenticated ∧ Complete ≠ unAuthorized ∧
         unAuthenticated ≠ unAuthorized

   [slOutput_distinct_clauses]  Theorem

      |- ReceiveMission ≠ Warno ∧ ReceiveMission ≠ TentativePlan ∧
         ReceiveMission ≠ InitiateMovement ∧ ReceiveMission ≠ Recon ∧
         ReceiveMission ≠ Complete ∧ ReceiveMission ≠ unAuthenticated ∧
         ReceiveMission ≠ unAuthorized ∧ Warno ≠ TentativePlan ∧
         Warno ≠ InitiateMovement ∧ Warno ≠ Recon ∧ Warno ≠ Complete ∧
         Warno ≠ unAuthenticated ∧ Warno ≠ unAuthorized ∧
         TentativePlan ≠ InitiateMovement ∧ TentativePlan ≠ Recon ∧
         TentativePlan ≠ Complete ∧ TentativePlan ≠ unAuthenticated ∧
         TentativePlan ≠ unAuthorized ∧ InitiateMovement ≠ Recon ∧
         InitiateMovement ≠ Complete ∧ InitiateMovement ≠ unAuthenticated ∧
         InitiateMovement ≠ unAuthorized ∧ Recon ≠ Complete ∧
         Recon ≠ unAuthenticated ∧ Recon ≠ unAuthorized ∧
         Complete ≠ unAuthenticated ∧ Complete ≠ unAuthorized ∧
         unAuthenticated ≠ unAuthorized

   [slOutput_induction]  Theorem

      |- ∀P.
           P Complete ∧ P InitiateMovement ∧ P ReceiveMission ∧ P Recon ∧
           P TentativePlan ∧ P Warno ∧ P unAuthenticated ∧ P unAuthorized ⇒
           ∀a. P a

   [slOutput_nchotomy]  Theorem

      |- ∀a.
           (a = ReceiveMission) ∨ (a = Warno) ∨ (a = TentativePlan) ∨
           (a = InitiateMovement) ∨ (a = Recon) ∨ (a = Complete) ∨
           (a = unAuthenticated) ∨ (a = unAuthorized)

   [slRole_distinct_clauses]  Theorem

      |- PlatoonLeader ≠ PlatoonSergeant

   [slState2num_11]  Theorem

      |- ∀a a'. (slState2num a = slState2num a') ⇔ (a = a')

   [slState2num_ONTO]  Theorem

      |- ∀r. r < 6 ⇔ ∃a. r = slState2num a

   [slState2num_num2slState]  Theorem

      |- ∀r. r < 6 ⇔ (slState2num (num2slState r) = r)

   [slState2num_thm]  Theorem

      |- (slState2num RECEIVE_MISSION = 0) ∧ (slState2num WARNO = 1) ∧
         (slState2num TENTATIVE_PLAN = 2) ∧
         (slState2num INITIATE_MOVEMENT = 3) ∧ (slState2num RECON = 4) ∧
         (slState2num COMPLETE = 5)

   [slState_Axiom]  Theorem

      |- ∀x0 x1 x2 x3 x4 x5.
           ∃f.
             (f RECEIVE_MISSION = x0) ∧ (f WARNO = x1) ∧
             (f TENTATIVE_PLAN = x2) ∧ (f INITIATE_MOVEMENT = x3) ∧
             (f RECON = x4) ∧ (f COMPLETE = x5)

   [slState_EQ_slState]  Theorem

      |- ∀a a'. (a = a') ⇔ (slState2num a = slState2num a')

   [slState_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3 v4 v5.
           (M = M') ∧ ((M' = RECEIVE_MISSION) ⇒ (v0 = v0')) ∧
           ((M' = WARNO) ⇒ (v1 = v1')) ∧
           ((M' = TENTATIVE_PLAN) ⇒ (v2 = v2')) ∧
           ((M' = INITIATE_MOVEMENT) ⇒ (v3 = v3')) ∧
           ((M' = RECON) ⇒ (v4 = v4')) ∧ ((M' = COMPLETE) ⇒ (v5 = v5')) ⇒
           ((case M of
               RECEIVE_MISSION => v0
             | WARNO => v1
             | TENTATIVE_PLAN => v2
             | INITIATE_MOVEMENT => v3
             | RECON => v4
             | COMPLETE => v5) =
            case M' of
              RECEIVE_MISSION => v0'
            | WARNO => v1'
            | TENTATIVE_PLAN => v2'
            | INITIATE_MOVEMENT => v3'
            | RECON => v4'
            | COMPLETE => v5')

   [slState_case_def]  Theorem

      |- (∀v0 v1 v2 v3 v4 v5.
            (case RECEIVE_MISSION of
               RECEIVE_MISSION => v0
             | WARNO => v1
             | TENTATIVE_PLAN => v2
             | INITIATE_MOVEMENT => v3
             | RECON => v4
             | COMPLETE => v5) =
            v0) ∧
         (∀v0 v1 v2 v3 v4 v5.
            (case WARNO of
               RECEIVE_MISSION => v0
             | WARNO => v1
             | TENTATIVE_PLAN => v2
             | INITIATE_MOVEMENT => v3
             | RECON => v4
             | COMPLETE => v5) =
            v1) ∧
         (∀v0 v1 v2 v3 v4 v5.
            (case TENTATIVE_PLAN of
               RECEIVE_MISSION => v0
             | WARNO => v1
             | TENTATIVE_PLAN => v2
             | INITIATE_MOVEMENT => v3
             | RECON => v4
             | COMPLETE => v5) =
            v2) ∧
         (∀v0 v1 v2 v3 v4 v5.
            (case INITIATE_MOVEMENT of
               RECEIVE_MISSION => v0
             | WARNO => v1
             | TENTATIVE_PLAN => v2
             | INITIATE_MOVEMENT => v3
             | RECON => v4
             | COMPLETE => v5) =
            v3) ∧
         (∀v0 v1 v2 v3 v4 v5.
            (case RECON of
               RECEIVE_MISSION => v0
             | WARNO => v1
             | TENTATIVE_PLAN => v2
             | INITIATE_MOVEMENT => v3
             | RECON => v4
             | COMPLETE => v5) =
            v4) ∧
         ∀v0 v1 v2 v3 v4 v5.
           (case COMPLETE of
              RECEIVE_MISSION => v0
            | WARNO => v1
            | TENTATIVE_PLAN => v2
            | INITIATE_MOVEMENT => v3
            | RECON => v4
            | COMPLETE => v5) =
           v5

   [slState_distinct]  Theorem

      |- RECEIVE_MISSION ≠ WARNO ∧ RECEIVE_MISSION ≠ TENTATIVE_PLAN ∧
         RECEIVE_MISSION ≠ INITIATE_MOVEMENT ∧ RECEIVE_MISSION ≠ RECON ∧
         RECEIVE_MISSION ≠ COMPLETE ∧ WARNO ≠ TENTATIVE_PLAN ∧
         WARNO ≠ INITIATE_MOVEMENT ∧ WARNO ≠ RECON ∧ WARNO ≠ COMPLETE ∧
         TENTATIVE_PLAN ≠ INITIATE_MOVEMENT ∧ TENTATIVE_PLAN ≠ RECON ∧
         TENTATIVE_PLAN ≠ COMPLETE ∧ INITIATE_MOVEMENT ≠ RECON ∧
         INITIATE_MOVEMENT ≠ COMPLETE ∧ RECON ≠ COMPLETE

   [slState_distinct_clauses]  Theorem

      |- RECEIVE_MISSION ≠ WARNO ∧ RECEIVE_MISSION ≠ TENTATIVE_PLAN ∧
         RECEIVE_MISSION ≠ INITIATE_MOVEMENT ∧ RECEIVE_MISSION ≠ RECON ∧
         RECEIVE_MISSION ≠ COMPLETE ∧ WARNO ≠ TENTATIVE_PLAN ∧
         WARNO ≠ INITIATE_MOVEMENT ∧ WARNO ≠ RECON ∧ WARNO ≠ COMPLETE ∧
         TENTATIVE_PLAN ≠ INITIATE_MOVEMENT ∧ TENTATIVE_PLAN ≠ RECON ∧
         TENTATIVE_PLAN ≠ COMPLETE ∧ INITIATE_MOVEMENT ≠ RECON ∧
         INITIATE_MOVEMENT ≠ COMPLETE ∧ RECON ≠ COMPLETE

   [slState_induction]  Theorem

      |- ∀P.
           P COMPLETE ∧ P INITIATE_MOVEMENT ∧ P RECEIVE_MISSION ∧ P RECON ∧
           P TENTATIVE_PLAN ∧ P WARNO ⇒
           ∀a. P a

   [slState_nchotomy]  Theorem

      |- ∀a.
           (a = RECEIVE_MISSION) ∨ (a = WARNO) ∨ (a = TENTATIVE_PLAN) ∨
           (a = INITIATE_MOVEMENT) ∨ (a = RECON) ∨ (a = COMPLETE)

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
