signature OMNITypeTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val command_TY_DEF : thm
    val command_case_def : thm
    val command_size_def : thm
    val escCommand_BIJ : thm
    val escCommand_CASE : thm
    val escCommand_TY_DEF : thm
    val escCommand_size_def : thm
    val escOutput_BIJ : thm
    val escOutput_CASE : thm
    val escOutput_TY_DEF : thm
    val escOutput_size_def : thm
    val escState_BIJ : thm
    val escState_CASE : thm
    val escState_TY_DEF : thm
    val escState_size_def : thm
    val output_TY_DEF : thm
    val output_case_def : thm
    val output_size_def : thm
    val principal_TY_DEF : thm
    val principal_case_def : thm
    val principal_size_def : thm
    val state_TY_DEF : thm
    val state_case_def : thm
    val state_size_def : thm

  (*  Theorems  *)
    val command_11 : thm
    val command_Axiom : thm
    val command_case_cong : thm
    val command_distinct : thm
    val command_distinct_clauses : thm
    val command_induction : thm
    val command_nchotomy : thm
    val command_one_one : thm
    val datatype_command : thm
    val datatype_escCommand : thm
    val datatype_escOutput : thm
    val datatype_escState : thm
    val datatype_output : thm
    val datatype_principal : thm
    val datatype_state : thm
    val escCommand2num_11 : thm
    val escCommand2num_ONTO : thm
    val escCommand2num_num2escCommand : thm
    val escCommand2num_thm : thm
    val escCommand_Axiom : thm
    val escCommand_EQ_escCommand : thm
    val escCommand_case_cong : thm
    val escCommand_case_def : thm
    val escCommand_distinct : thm
    val escCommand_distinct_clauses : thm
    val escCommand_induction : thm
    val escCommand_nchotomy : thm
    val escOutput2num_11 : thm
    val escOutput2num_ONTO : thm
    val escOutput2num_num2escOutput : thm
    val escOutput2num_thm : thm
    val escOutput_Axiom : thm
    val escOutput_EQ_escOutput : thm
    val escOutput_case_cong : thm
    val escOutput_case_def : thm
    val escOutput_distinct : thm
    val escOutput_distinct_clauses : thm
    val escOutput_induction : thm
    val escOutput_nchotomy : thm
    val escState2num_11 : thm
    val escState2num_ONTO : thm
    val escState2num_num2escState : thm
    val escState2num_thm : thm
    val escState_Axiom : thm
    val escState_EQ_escState : thm
    val escState_case_cong : thm
    val escState_case_def : thm
    val escState_distinct : thm
    val escState_distinct_clauses : thm
    val escState_induction : thm
    val escState_nchotomy : thm
    val num2escCommand_11 : thm
    val num2escCommand_ONTO : thm
    val num2escCommand_escCommand2num : thm
    val num2escCommand_thm : thm
    val num2escOutput_11 : thm
    val num2escOutput_ONTO : thm
    val num2escOutput_escOutput2num : thm
    val num2escOutput_thm : thm
    val num2escState_11 : thm
    val num2escState_ONTO : thm
    val num2escState_escState2num : thm
    val num2escState_thm : thm
    val output_11 : thm
    val output_Axiom : thm
    val output_case_cong : thm
    val output_distinct : thm
    val output_distinct_clauses : thm
    val output_induction : thm
    val output_nchotomy : thm
    val output_one_one : thm
    val principal_11 : thm
    val principal_Axiom : thm
    val principal_case_cong : thm
    val principal_induction : thm
    val principal_nchotomy : thm
    val principal_one_one : thm
    val state_11 : thm
    val state_Axiom : thm
    val state_case_cong : thm
    val state_distinct : thm
    val state_distinct_clauses : thm
    val state_induction : thm
    val state_nchotomy : thm
    val state_one_one : thm

  val OMNIType_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [indexedLists] Parent theory of "OMNIType"

   [patternMatches] Parent theory of "OMNIType"

   [command_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0.
                ∀'command' .
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
                     'command' a0) ⇒
                  'command' a0) rep

   [command_case_def]  Definition

      |- (∀a f f1. command_CASE (ESCc a) f f1 = f a) ∧
         ∀a f f1. command_CASE (SLc a) f f1 = f1 a

   [command_size_def]  Definition

      |- (∀f a. command_size f (ESCc a) = 1 + escCommand_size a) ∧
         ∀f a. command_size f (SLc a) = 1 + f a

   [escCommand_BIJ]  Definition

      |- (∀a. num2escCommand (escCommand2num a) = a) ∧
         ∀r. (λn. n < 4) r ⇔ (escCommand2num (num2escCommand r) = r)

   [escCommand_CASE]  Definition

      |- ∀x v0 v1 v2 v3.
           (case x of
              returnToBase => v0
            | changeMission => v1
            | resupply => v2
            | reactToContact => v3) =
           (λm.
              if m < 1 then v0
              else if m < 2 then v1
              else if m = 2 then v2
              else v3) (escCommand2num x)

   [escCommand_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 4) rep

   [escCommand_size_def]  Definition

      |- ∀x. escCommand_size x = 0

   [escOutput_BIJ]  Definition

      |- (∀a. num2escOutput (escOutput2num a) = a) ∧
         ∀r. (λn. n < 4) r ⇔ (escOutput2num (num2escOutput r) = r)

   [escOutput_CASE]  Definition

      |- ∀x v0 v1 v2 v3.
           (case x of
              ReturnToBase => v0
            | ChangeMission => v1
            | Resupply => v2
            | ReactToContact => v3) =
           (λm.
              if m < 1 then v0
              else if m < 2 then v1
              else if m = 2 then v2
              else v3) (escOutput2num x)

   [escOutput_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 4) rep

   [escOutput_size_def]  Definition

      |- ∀x. escOutput_size x = 0

   [escState_BIJ]  Definition

      |- (∀a. num2escState (escState2num a) = a) ∧
         ∀r. (λn. n < 4) r ⇔ (escState2num (num2escState r) = r)

   [escState_CASE]  Definition

      |- ∀x v0 v1 v2 v3.
           (case x of RTB => v0 | CM => v1 | RESUPPLY => v2 | RTC => v3) =
           (λm.
              if m < 1 then v0
              else if m < 2 then v1
              else if m = 2 then v2
              else v3) (escState2num x)

   [escState_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 4) rep

   [escState_size_def]  Definition

      |- ∀x. escState_size x = 0

   [output_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0.
                ∀'output' .
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
                     'output' a0) ⇒
                  'output' a0) rep

   [output_case_def]  Definition

      |- (∀a f f1. output_CASE (ESCo a) f f1 = f a) ∧
         ∀a f f1. output_CASE (SLo a) f f1 = f1 a

   [output_size_def]  Definition

      |- (∀f a. output_size f (ESCo a) = 1 + escOutput_size a) ∧
         ∀f a. output_size f (SLo a) = 1 + f a

   [principal_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0.
                ∀'principal' .
                  (∀a0.
                     (∃a.
                        a0 =
                        (λa. ind_type$CONSTR 0 a (λn. ind_type$BOTTOM))
                          a) ⇒
                     'principal' a0) ⇒
                  'principal' a0) rep

   [principal_case_def]  Definition

      |- ∀a f. principal_CASE (SR a) f = f a

   [principal_size_def]  Definition

      |- ∀f a. principal_size f (SR a) = 1 + f a

   [state_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0.
                ∀'state' .
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
                     'state' a0) ⇒
                  'state' a0) rep

   [state_case_def]  Definition

      |- (∀a f f1. state_CASE (ESCs a) f f1 = f a) ∧
         ∀a f f1. state_CASE (SLs a) f f1 = f1 a

   [state_size_def]  Definition

      |- (∀f a. state_size f (ESCs a) = 1 + escState_size a) ∧
         ∀f a. state_size f (SLs a) = 1 + f a

   [command_11]  Theorem

      |- (∀a a'. (ESCc a = ESCc a') ⇔ (a = a')) ∧
         ∀a a'. (SLc a = SLc a') ⇔ (a = a')

   [command_Axiom]  Theorem

      |- ∀f0 f1. ∃fn. (∀a. fn (ESCc a) = f0 a) ∧ ∀a. fn (SLc a) = f1 a

   [command_case_cong]  Theorem

      |- ∀M M' f f1.
           (M = M') ∧ (∀a. (M' = ESCc a) ⇒ (f a = f' a)) ∧
           (∀a. (M' = SLc a) ⇒ (f1 a = f1' a)) ⇒
           (command_CASE M f f1 = command_CASE M' f' f1')

   [command_distinct]  Theorem

      |- ∀a' a. ESCc a ≠ SLc a'

   [command_distinct_clauses]  Theorem

      |- ∀a' a. ESCc a ≠ SLc a'

   [command_induction]  Theorem

      |- ∀P. (∀e. P (ESCc e)) ∧ (∀s. P (SLc s)) ⇒ ∀c. P c

   [command_nchotomy]  Theorem

      |- ∀cc. (∃e. cc = ESCc e) ∨ ∃s. cc = SLc s

   [command_one_one]  Theorem

      |- (∀a a'. (ESCc a = ESCc a') ⇔ (a = a')) ∧
         ∀a a'. (SLc a = SLc a') ⇔ (a = a')

   [datatype_command]  Theorem

      |- DATATYPE (command ESCc SLc)

   [datatype_escCommand]  Theorem

      |- DATATYPE
           (escCommand returnToBase changeMission resupply reactToContact)

   [datatype_escOutput]  Theorem

      |- DATATYPE
           (escOutput ReturnToBase ChangeMission Resupply ReactToContact)

   [datatype_escState]  Theorem

      |- DATATYPE (escState RTB CM RESUPPLY RTC)

   [datatype_output]  Theorem

      |- DATATYPE (output ESCo SLo)

   [datatype_principal]  Theorem

      |- DATATYPE (principal SR)

   [datatype_state]  Theorem

      |- DATATYPE (state ESCs SLs)

   [escCommand2num_11]  Theorem

      |- ∀a a'. (escCommand2num a = escCommand2num a') ⇔ (a = a')

   [escCommand2num_ONTO]  Theorem

      |- ∀r. r < 4 ⇔ ∃a. r = escCommand2num a

   [escCommand2num_num2escCommand]  Theorem

      |- ∀r. r < 4 ⇔ (escCommand2num (num2escCommand r) = r)

   [escCommand2num_thm]  Theorem

      |- (escCommand2num returnToBase = 0) ∧
         (escCommand2num changeMission = 1) ∧
         (escCommand2num resupply = 2) ∧
         (escCommand2num reactToContact = 3)

   [escCommand_Axiom]  Theorem

      |- ∀x0 x1 x2 x3.
           ∃f.
             (f returnToBase = x0) ∧ (f changeMission = x1) ∧
             (f resupply = x2) ∧ (f reactToContact = x3)

   [escCommand_EQ_escCommand]  Theorem

      |- ∀a a'. (a = a') ⇔ (escCommand2num a = escCommand2num a')

   [escCommand_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3.
           (M = M') ∧ ((M' = returnToBase) ⇒ (v0 = v0')) ∧
           ((M' = changeMission) ⇒ (v1 = v1')) ∧
           ((M' = resupply) ⇒ (v2 = v2')) ∧
           ((M' = reactToContact) ⇒ (v3 = v3')) ⇒
           ((case M of
               returnToBase => v0
             | changeMission => v1
             | resupply => v2
             | reactToContact => v3) =
            case M' of
              returnToBase => v0'
            | changeMission => v1'
            | resupply => v2'
            | reactToContact => v3')

   [escCommand_case_def]  Theorem

      |- (∀v0 v1 v2 v3.
            (case returnToBase of
               returnToBase => v0
             | changeMission => v1
             | resupply => v2
             | reactToContact => v3) =
            v0) ∧
         (∀v0 v1 v2 v3.
            (case changeMission of
               returnToBase => v0
             | changeMission => v1
             | resupply => v2
             | reactToContact => v3) =
            v1) ∧
         (∀v0 v1 v2 v3.
            (case resupply of
               returnToBase => v0
             | changeMission => v1
             | resupply => v2
             | reactToContact => v3) =
            v2) ∧
         ∀v0 v1 v2 v3.
           (case reactToContact of
              returnToBase => v0
            | changeMission => v1
            | resupply => v2
            | reactToContact => v3) =
           v3

   [escCommand_distinct]  Theorem

      |- returnToBase ≠ changeMission ∧ returnToBase ≠ resupply ∧
         returnToBase ≠ reactToContact ∧ changeMission ≠ resupply ∧
         changeMission ≠ reactToContact ∧ resupply ≠ reactToContact

   [escCommand_distinct_clauses]  Theorem

      |- returnToBase ≠ changeMission ∧ returnToBase ≠ resupply ∧
         returnToBase ≠ reactToContact ∧ changeMission ≠ resupply ∧
         changeMission ≠ reactToContact ∧ resupply ≠ reactToContact

   [escCommand_induction]  Theorem

      |- ∀P.
           P changeMission ∧ P reactToContact ∧ P resupply ∧
           P returnToBase ⇒
           ∀a. P a

   [escCommand_nchotomy]  Theorem

      |- ∀a.
           (a = returnToBase) ∨ (a = changeMission) ∨ (a = resupply) ∨
           (a = reactToContact)

   [escOutput2num_11]  Theorem

      |- ∀a a'. (escOutput2num a = escOutput2num a') ⇔ (a = a')

   [escOutput2num_ONTO]  Theorem

      |- ∀r. r < 4 ⇔ ∃a. r = escOutput2num a

   [escOutput2num_num2escOutput]  Theorem

      |- ∀r. r < 4 ⇔ (escOutput2num (num2escOutput r) = r)

   [escOutput2num_thm]  Theorem

      |- (escOutput2num ReturnToBase = 0) ∧
         (escOutput2num ChangeMission = 1) ∧ (escOutput2num Resupply = 2) ∧
         (escOutput2num ReactToContact = 3)

   [escOutput_Axiom]  Theorem

      |- ∀x0 x1 x2 x3.
           ∃f.
             (f ReturnToBase = x0) ∧ (f ChangeMission = x1) ∧
             (f Resupply = x2) ∧ (f ReactToContact = x3)

   [escOutput_EQ_escOutput]  Theorem

      |- ∀a a'. (a = a') ⇔ (escOutput2num a = escOutput2num a')

   [escOutput_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3.
           (M = M') ∧ ((M' = ReturnToBase) ⇒ (v0 = v0')) ∧
           ((M' = ChangeMission) ⇒ (v1 = v1')) ∧
           ((M' = Resupply) ⇒ (v2 = v2')) ∧
           ((M' = ReactToContact) ⇒ (v3 = v3')) ⇒
           ((case M of
               ReturnToBase => v0
             | ChangeMission => v1
             | Resupply => v2
             | ReactToContact => v3) =
            case M' of
              ReturnToBase => v0'
            | ChangeMission => v1'
            | Resupply => v2'
            | ReactToContact => v3')

   [escOutput_case_def]  Theorem

      |- (∀v0 v1 v2 v3.
            (case ReturnToBase of
               ReturnToBase => v0
             | ChangeMission => v1
             | Resupply => v2
             | ReactToContact => v3) =
            v0) ∧
         (∀v0 v1 v2 v3.
            (case ChangeMission of
               ReturnToBase => v0
             | ChangeMission => v1
             | Resupply => v2
             | ReactToContact => v3) =
            v1) ∧
         (∀v0 v1 v2 v3.
            (case Resupply of
               ReturnToBase => v0
             | ChangeMission => v1
             | Resupply => v2
             | ReactToContact => v3) =
            v2) ∧
         ∀v0 v1 v2 v3.
           (case ReactToContact of
              ReturnToBase => v0
            | ChangeMission => v1
            | Resupply => v2
            | ReactToContact => v3) =
           v3

   [escOutput_distinct]  Theorem

      |- ReturnToBase ≠ ChangeMission ∧ ReturnToBase ≠ Resupply ∧
         ReturnToBase ≠ ReactToContact ∧ ChangeMission ≠ Resupply ∧
         ChangeMission ≠ ReactToContact ∧ Resupply ≠ ReactToContact

   [escOutput_distinct_clauses]  Theorem

      |- ReturnToBase ≠ ChangeMission ∧ ReturnToBase ≠ Resupply ∧
         ReturnToBase ≠ ReactToContact ∧ ChangeMission ≠ Resupply ∧
         ChangeMission ≠ ReactToContact ∧ Resupply ≠ ReactToContact

   [escOutput_induction]  Theorem

      |- ∀P.
           P ChangeMission ∧ P ReactToContact ∧ P Resupply ∧
           P ReturnToBase ⇒
           ∀a. P a

   [escOutput_nchotomy]  Theorem

      |- ∀a.
           (a = ReturnToBase) ∨ (a = ChangeMission) ∨ (a = Resupply) ∨
           (a = ReactToContact)

   [escState2num_11]  Theorem

      |- ∀a a'. (escState2num a = escState2num a') ⇔ (a = a')

   [escState2num_ONTO]  Theorem

      |- ∀r. r < 4 ⇔ ∃a. r = escState2num a

   [escState2num_num2escState]  Theorem

      |- ∀r. r < 4 ⇔ (escState2num (num2escState r) = r)

   [escState2num_thm]  Theorem

      |- (escState2num RTB = 0) ∧ (escState2num CM = 1) ∧
         (escState2num RESUPPLY = 2) ∧ (escState2num RTC = 3)

   [escState_Axiom]  Theorem

      |- ∀x0 x1 x2 x3.
           ∃f.
             (f RTB = x0) ∧ (f CM = x1) ∧ (f RESUPPLY = x2) ∧ (f RTC = x3)

   [escState_EQ_escState]  Theorem

      |- ∀a a'. (a = a') ⇔ (escState2num a = escState2num a')

   [escState_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3.
           (M = M') ∧ ((M' = RTB) ⇒ (v0 = v0')) ∧
           ((M' = CM) ⇒ (v1 = v1')) ∧ ((M' = RESUPPLY) ⇒ (v2 = v2')) ∧
           ((M' = RTC) ⇒ (v3 = v3')) ⇒
           ((case M of RTB => v0 | CM => v1 | RESUPPLY => v2 | RTC => v3) =
            case M' of
              RTB => v0'
            | CM => v1'
            | RESUPPLY => v2'
            | RTC => v3')

   [escState_case_def]  Theorem

      |- (∀v0 v1 v2 v3.
            (case RTB of
               RTB => v0
             | CM => v1
             | RESUPPLY => v2
             | RTC => v3) =
            v0) ∧
         (∀v0 v1 v2 v3.
            (case CM of
               RTB => v0
             | CM => v1
             | RESUPPLY => v2
             | RTC => v3) =
            v1) ∧
         (∀v0 v1 v2 v3.
            (case RESUPPLY of
               RTB => v0
             | CM => v1
             | RESUPPLY => v2
             | RTC => v3) =
            v2) ∧
         ∀v0 v1 v2 v3.
           (case RTC of
              RTB => v0
            | CM => v1
            | RESUPPLY => v2
            | RTC => v3) =
           v3

   [escState_distinct]  Theorem

      |- RTB ≠ CM ∧ RTB ≠ RESUPPLY ∧ RTB ≠ RTC ∧ CM ≠ RESUPPLY ∧ CM ≠ RTC ∧
         RESUPPLY ≠ RTC

   [escState_distinct_clauses]  Theorem

      |- RTB ≠ CM ∧ RTB ≠ RESUPPLY ∧ RTB ≠ RTC ∧ CM ≠ RESUPPLY ∧ CM ≠ RTC ∧
         RESUPPLY ≠ RTC

   [escState_induction]  Theorem

      |- ∀P. P CM ∧ P RESUPPLY ∧ P RTB ∧ P RTC ⇒ ∀a. P a

   [escState_nchotomy]  Theorem

      |- ∀a. (a = RTB) ∨ (a = CM) ∨ (a = RESUPPLY) ∨ (a = RTC)

   [num2escCommand_11]  Theorem

      |- ∀r r'.
           r < 4 ⇒
           r' < 4 ⇒
           ((num2escCommand r = num2escCommand r') ⇔ (r = r'))

   [num2escCommand_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2escCommand r) ∧ r < 4

   [num2escCommand_escCommand2num]  Theorem

      |- ∀a. num2escCommand (escCommand2num a) = a

   [num2escCommand_thm]  Theorem

      |- (num2escCommand 0 = returnToBase) ∧
         (num2escCommand 1 = changeMission) ∧
         (num2escCommand 2 = resupply) ∧
         (num2escCommand 3 = reactToContact)

   [num2escOutput_11]  Theorem

      |- ∀r r'.
           r < 4 ⇒
           r' < 4 ⇒
           ((num2escOutput r = num2escOutput r') ⇔ (r = r'))

   [num2escOutput_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2escOutput r) ∧ r < 4

   [num2escOutput_escOutput2num]  Theorem

      |- ∀a. num2escOutput (escOutput2num a) = a

   [num2escOutput_thm]  Theorem

      |- (num2escOutput 0 = ReturnToBase) ∧
         (num2escOutput 1 = ChangeMission) ∧ (num2escOutput 2 = Resupply) ∧
         (num2escOutput 3 = ReactToContact)

   [num2escState_11]  Theorem

      |- ∀r r'.
           r < 4 ⇒ r' < 4 ⇒ ((num2escState r = num2escState r') ⇔ (r = r'))

   [num2escState_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2escState r) ∧ r < 4

   [num2escState_escState2num]  Theorem

      |- ∀a. num2escState (escState2num a) = a

   [num2escState_thm]  Theorem

      |- (num2escState 0 = RTB) ∧ (num2escState 1 = CM) ∧
         (num2escState 2 = RESUPPLY) ∧ (num2escState 3 = RTC)

   [output_11]  Theorem

      |- (∀a a'. (ESCo a = ESCo a') ⇔ (a = a')) ∧
         ∀a a'. (SLo a = SLo a') ⇔ (a = a')

   [output_Axiom]  Theorem

      |- ∀f0 f1. ∃fn. (∀a. fn (ESCo a) = f0 a) ∧ ∀a. fn (SLo a) = f1 a

   [output_case_cong]  Theorem

      |- ∀M M' f f1.
           (M = M') ∧ (∀a. (M' = ESCo a) ⇒ (f a = f' a)) ∧
           (∀a. (M' = SLo a) ⇒ (f1 a = f1' a)) ⇒
           (output_CASE M f f1 = output_CASE M' f' f1')

   [output_distinct]  Theorem

      |- ∀a' a. ESCo a ≠ SLo a'

   [output_distinct_clauses]  Theorem

      |- ∀a' a. ESCo a ≠ SLo a'

   [output_induction]  Theorem

      |- ∀P. (∀e. P (ESCo e)) ∧ (∀s. P (SLo s)) ⇒ ∀ $o. P $o

   [output_nchotomy]  Theorem

      |- ∀oo. (∃e. oo = ESCo e) ∨ ∃s. oo = SLo s

   [output_one_one]  Theorem

      |- (∀a a'. (ESCo a = ESCo a') ⇔ (a = a')) ∧
         ∀a a'. (SLo a = SLo a') ⇔ (a = a')

   [principal_11]  Theorem

      |- ∀a a'. (SR a = SR a') ⇔ (a = a')

   [principal_Axiom]  Theorem

      |- ∀f. ∃fn. ∀a. fn (SR a) = f a

   [principal_case_cong]  Theorem

      |- ∀M M' f.
           (M = M') ∧ (∀a. (M' = SR a) ⇒ (f a = f' a)) ⇒
           (principal_CASE M f = principal_CASE M' f')

   [principal_induction]  Theorem

      |- ∀P. (∀s. P (SR s)) ⇒ ∀p. P p

   [principal_nchotomy]  Theorem

      |- ∀pp. ∃s. pp = SR s

   [principal_one_one]  Theorem

      |- ∀a a'. (SR a = SR a') ⇔ (a = a')

   [state_11]  Theorem

      |- (∀a a'. (ESCs a = ESCs a') ⇔ (a = a')) ∧
         ∀a a'. (SLs a = SLs a') ⇔ (a = a')

   [state_Axiom]  Theorem

      |- ∀f0 f1. ∃fn. (∀a. fn (ESCs a) = f0 a) ∧ ∀a. fn (SLs a) = f1 a

   [state_case_cong]  Theorem

      |- ∀M M' f f1.
           (M = M') ∧ (∀a. (M' = ESCs a) ⇒ (f a = f' a)) ∧
           (∀a. (M' = SLs a) ⇒ (f1 a = f1' a)) ⇒
           (state_CASE M f f1 = state_CASE M' f' f1')

   [state_distinct]  Theorem

      |- ∀a' a. ESCs a ≠ SLs a'

   [state_distinct_clauses]  Theorem

      |- ∀a' a. ESCs a ≠ SLs a'

   [state_induction]  Theorem

      |- ∀P. (∀e. P (ESCs e)) ∧ (∀s. P (SLs s)) ⇒ ∀s. P s

   [state_nchotomy]  Theorem

      |- ∀ss. (∃e. ss = ESCs e) ∨ ∃s. ss = SLs s

   [state_one_one]  Theorem

      |- (∀a a'. (ESCs a = ESCs a') ⇔ (a = a')) ∧
         ∀a a'. (SLs a = SLs a') ⇔ (a = a')


*)
end
