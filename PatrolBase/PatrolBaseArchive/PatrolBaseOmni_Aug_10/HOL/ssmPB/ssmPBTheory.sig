signature ssmPBTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val authenticationTest_primitive_def : thm
    val secContext_def : thm
    val ssmPBStateInterp_def : thm

  (*  Theorems  *)
    val PBNS_def : thm
    val PBNS_ind : thm
    val PBOut_def : thm
    val PBOut_ind : thm
    val PlatoonLeader_exec_slCommand_justified_thm : thm
    val PlatoonLeader_slCommand_lemma : thm
    val authenticationTest_cmd_reject_lemma : thm
    val authenticationTest_def : thm
    val authenticationTest_ind : thm

  val ssmPB_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [OMNIType] Parent theory of "ssmPB"

   [PBType] Parent theory of "ssmPB"

   [ssm11] Parent theory of "ssmPB"

   [authenticationTest_primitive_def]  Definition

      |- authenticationTest =
         WFREC (@R. WF R)
           (λauthenticationTest a.
              case a of
                TT => I F
              | FF => I F
              | prop v33 => I F
              | notf v34 => I F
              | v35 andf v36 => I F
              | v37 orf v38 => I F
              | v39 impf v40 => I F
              | v41 eqf v42 => I F
              | v43 says TT => I F
              | v43 says FF => I F
              | Name v137 says prop cmd => I T
              | v138 meet v139 says prop cmd => I F
              | v140 quoting v141 says prop cmd => I F
              | v43 says notf v100 => I F
              | v43 says (v101 andf v102) => I F
              | v43 says (v103 orf v104) => I F
              | v43 says (v105 impf v106) => I F
              | v43 says (v107 eqf v108) => I F
              | v43 says v109 says v110 => I F
              | v43 says v111 speaks_for v112 => I F
              | v43 says v113 controls v114 => I F
              | v43 says reps v115 v116 v117 => I F
              | v43 says v118 domi v119 => I F
              | v43 says v120 eqi v121 => I F
              | v43 says v122 doms v123 => I F
              | v43 says v124 eqs v125 => I F
              | v43 says v126 eqn v127 => I F
              | v43 says v128 lte v129 => I F
              | v43 says v130 lt v131 => I F
              | v45 speaks_for v46 => I F
              | v47 controls v48 => I F
              | reps v49 v50 v51 => I F
              | v52 domi v53 => I F
              | v54 eqi v55 => I F
              | v56 doms v57 => I F
              | v58 eqs v59 => I F
              | v60 eqn v61 => I F
              | v62 lte v63 => I F
              | v64 lt v65 => I F)

   [secContext_def]  Definition

      |- ∀cmd.
           secContext cmd =
           [Name PlatoonLeader controls prop (SOME (SLc cmd))]

   [ssmPBStateInterp_def]  Definition

      |- ∀state. ssmPBStateInterp state = TT

   [PBNS_def]  Theorem

      |- (PBNS PLAN_PB (exec (SLc crossLD)) = MOVE_TO_ORP) ∧
         (PBNS PLAN_PB (exec (SLc incomplete)) = PLAN_PB) ∧
         (PBNS MOVE_TO_ORP (exec (SLc conductORP)) = CONDUCT_ORP) ∧
         (PBNS MOVE_TO_ORP (exec (SLc incomplete)) = MOVE_TO_ORP) ∧
         (PBNS CONDUCT_ORP (exec (SLc moveToPB)) = MOVE_TO_PB) ∧
         (PBNS CONDUCT_ORP (exec (SLc incomplete)) = CONDUCT_ORP) ∧
         (PBNS MOVE_TO_PB (exec (SLc conductPB)) = CONDUCT_PB) ∧
         (PBNS MOVE_TO_PB (exec (SLc incomplete)) = MOVE_TO_PB) ∧
         (PBNS CONDUCT_PB (exec (SLc completePB)) = COMPLETE_PB) ∧
         (PBNS CONDUCT_PB (exec (SLc incomplete)) = CONDUCT_PB) ∧
         (PBNS s (trap (SLc cmd)) = s) ∧ (PBNS s (discard (SLc cmd)) = s)

   [PBNS_ind]  Theorem

      |- ∀P.
           P PLAN_PB (exec (SLc crossLD)) ∧
           P PLAN_PB (exec (SLc incomplete)) ∧
           P MOVE_TO_ORP (exec (SLc conductORP)) ∧
           P MOVE_TO_ORP (exec (SLc incomplete)) ∧
           P CONDUCT_ORP (exec (SLc moveToPB)) ∧
           P CONDUCT_ORP (exec (SLc incomplete)) ∧
           P MOVE_TO_PB (exec (SLc conductPB)) ∧
           P MOVE_TO_PB (exec (SLc incomplete)) ∧
           P CONDUCT_PB (exec (SLc completePB)) ∧
           P CONDUCT_PB (exec (SLc incomplete)) ∧
           (∀s cmd. P s (trap (SLc cmd))) ∧
           (∀s cmd. P s (discard (SLc cmd))) ∧
           (∀s v6. P s (discard (ESCc v6))) ∧
           (∀s v9. P s (trap (ESCc v9))) ∧
           (∀v12. P PLAN_PB (exec (ESCc v12))) ∧
           P PLAN_PB (exec (SLc conductORP)) ∧
           P PLAN_PB (exec (SLc moveToPB)) ∧
           P PLAN_PB (exec (SLc conductPB)) ∧
           P PLAN_PB (exec (SLc completePB)) ∧
           (∀v15. P MOVE_TO_ORP (exec (ESCc v15))) ∧
           P MOVE_TO_ORP (exec (SLc crossLD)) ∧
           P MOVE_TO_ORP (exec (SLc moveToPB)) ∧
           P MOVE_TO_ORP (exec (SLc conductPB)) ∧
           P MOVE_TO_ORP (exec (SLc completePB)) ∧
           (∀v18. P CONDUCT_ORP (exec (ESCc v18))) ∧
           P CONDUCT_ORP (exec (SLc crossLD)) ∧
           P CONDUCT_ORP (exec (SLc conductORP)) ∧
           P CONDUCT_ORP (exec (SLc conductPB)) ∧
           P CONDUCT_ORP (exec (SLc completePB)) ∧
           (∀v21. P MOVE_TO_PB (exec (ESCc v21))) ∧
           P MOVE_TO_PB (exec (SLc crossLD)) ∧
           P MOVE_TO_PB (exec (SLc conductORP)) ∧
           P MOVE_TO_PB (exec (SLc moveToPB)) ∧
           P MOVE_TO_PB (exec (SLc completePB)) ∧
           (∀v24. P CONDUCT_PB (exec (ESCc v24))) ∧
           P CONDUCT_PB (exec (SLc crossLD)) ∧
           P CONDUCT_PB (exec (SLc conductORP)) ∧
           P CONDUCT_PB (exec (SLc moveToPB)) ∧
           P CONDUCT_PB (exec (SLc conductPB)) ∧
           (∀v26. P COMPLETE_PB (exec v26)) ⇒
           ∀v v1. P v v1

   [PBOut_def]  Theorem

      |- (PBOut PLAN_PB (exec (SLc crossLD)) = MoveToORP) ∧
         (PBOut PLAN_PB (exec (SLc incomplete)) = PlanPB) ∧
         (PBOut MOVE_TO_ORP (exec (SLc conductORP)) = ConductORP) ∧
         (PBOut MOVE_TO_ORP (exec (SLc incomplete)) = MoveToORP) ∧
         (PBOut CONDUCT_ORP (exec (SLc moveToPB)) = MoveToPB) ∧
         (PBOut CONDUCT_ORP (exec (SLc incomplete)) = ConductORP) ∧
         (PBOut MOVE_TO_PB (exec (SLc conductPB)) = ConductPB) ∧
         (PBOut MOVE_TO_PB (exec (SLc incomplete)) = MoveToPB) ∧
         (PBOut CONDUCT_PB (exec (SLc completePB)) = CompletePB) ∧
         (PBOut CONDUCT_PB (exec (SLc incomplete)) = ConductPB) ∧
         (PBOut s (trap (SLc cmd)) = unAuthorized) ∧
         (PBOut s (discard (SLc cmd)) = unAuthenticated)

   [PBOut_ind]  Theorem

      |- ∀P.
           P PLAN_PB (exec (SLc crossLD)) ∧
           P PLAN_PB (exec (SLc incomplete)) ∧
           P MOVE_TO_ORP (exec (SLc conductORP)) ∧
           P MOVE_TO_ORP (exec (SLc incomplete)) ∧
           P CONDUCT_ORP (exec (SLc moveToPB)) ∧
           P CONDUCT_ORP (exec (SLc incomplete)) ∧
           P MOVE_TO_PB (exec (SLc conductPB)) ∧
           P MOVE_TO_PB (exec (SLc incomplete)) ∧
           P CONDUCT_PB (exec (SLc completePB)) ∧
           P CONDUCT_PB (exec (SLc incomplete)) ∧
           (∀s cmd. P s (trap (SLc cmd))) ∧
           (∀s cmd. P s (discard (SLc cmd))) ∧
           (∀s v6. P s (discard (ESCc v6))) ∧
           (∀s v9. P s (trap (ESCc v9))) ∧
           (∀v12. P PLAN_PB (exec (ESCc v12))) ∧
           P PLAN_PB (exec (SLc conductORP)) ∧
           P PLAN_PB (exec (SLc moveToPB)) ∧
           P PLAN_PB (exec (SLc conductPB)) ∧
           P PLAN_PB (exec (SLc completePB)) ∧
           (∀v15. P MOVE_TO_ORP (exec (ESCc v15))) ∧
           P MOVE_TO_ORP (exec (SLc crossLD)) ∧
           P MOVE_TO_ORP (exec (SLc moveToPB)) ∧
           P MOVE_TO_ORP (exec (SLc conductPB)) ∧
           P MOVE_TO_ORP (exec (SLc completePB)) ∧
           (∀v18. P CONDUCT_ORP (exec (ESCc v18))) ∧
           P CONDUCT_ORP (exec (SLc crossLD)) ∧
           P CONDUCT_ORP (exec (SLc conductORP)) ∧
           P CONDUCT_ORP (exec (SLc conductPB)) ∧
           P CONDUCT_ORP (exec (SLc completePB)) ∧
           (∀v21. P MOVE_TO_PB (exec (ESCc v21))) ∧
           P MOVE_TO_PB (exec (SLc crossLD)) ∧
           P MOVE_TO_PB (exec (SLc conductORP)) ∧
           P MOVE_TO_PB (exec (SLc moveToPB)) ∧
           P MOVE_TO_PB (exec (SLc completePB)) ∧
           (∀v24. P CONDUCT_PB (exec (ESCc v24))) ∧
           P CONDUCT_PB (exec (SLc crossLD)) ∧
           P CONDUCT_PB (exec (SLc conductORP)) ∧
           P CONDUCT_PB (exec (SLc moveToPB)) ∧
           P CONDUCT_PB (exec (SLc conductPB)) ∧
           (∀v26. P COMPLETE_PB (exec v26)) ⇒
           ∀v v1. P v v1

   [PlatoonLeader_exec_slCommand_justified_thm]  Theorem

      |- ∀NS Out M Oi Os.
           TR (M,Oi,Os) (exec (SLc slCommand))
             (CFG authenticationTest ssmPBStateInterp
                (secContext slCommand)
                (Name PlatoonLeader says prop (SOME (SLc slCommand))::ins)
                s outs)
             (CFG authenticationTest ssmPBStateInterp
                (secContext slCommand) ins (NS s (exec (SLc slCommand)))
                (Out s (exec (SLc slCommand))::outs)) ⇔
           authenticationTest
             (Name PlatoonLeader says prop (SOME (SLc slCommand))) ∧
           CFGInterpret (M,Oi,Os)
             (CFG authenticationTest ssmPBStateInterp
                (secContext slCommand)
                (Name PlatoonLeader says prop (SOME (SLc slCommand))::ins)
                s outs) ∧ (M,Oi,Os) sat prop (SOME (SLc slCommand))

   [PlatoonLeader_slCommand_lemma]  Theorem

      |- CFGInterpret (M,Oi,Os)
           (CFG authenticationTest ssmPBStateInterp (secContext slCommand)
              (Name PlatoonLeader says prop (SOME (SLc slCommand))::ins) s
              outs) ⇒
         (M,Oi,Os) sat prop (SOME (SLc slCommand))

   [authenticationTest_cmd_reject_lemma]  Theorem

      |- ∀cmd. ¬authenticationTest (prop (SOME cmd))

   [authenticationTest_def]  Theorem

      |- (authenticationTest (Name PlatoonLeader says prop cmd) ⇔ T) ∧
         (authenticationTest TT ⇔ F) ∧ (authenticationTest FF ⇔ F) ∧
         (authenticationTest (prop v) ⇔ F) ∧
         (authenticationTest (notf v1) ⇔ F) ∧
         (authenticationTest (v2 andf v3) ⇔ F) ∧
         (authenticationTest (v4 orf v5) ⇔ F) ∧
         (authenticationTest (v6 impf v7) ⇔ F) ∧
         (authenticationTest (v8 eqf v9) ⇔ F) ∧
         (authenticationTest (v10 says TT) ⇔ F) ∧
         (authenticationTest (v10 says FF) ⇔ F) ∧
         (authenticationTest (v133 meet v134 says prop v66) ⇔ F) ∧
         (authenticationTest (v135 quoting v136 says prop v66) ⇔ F) ∧
         (authenticationTest (v10 says notf v67) ⇔ F) ∧
         (authenticationTest (v10 says (v68 andf v69)) ⇔ F) ∧
         (authenticationTest (v10 says (v70 orf v71)) ⇔ F) ∧
         (authenticationTest (v10 says (v72 impf v73)) ⇔ F) ∧
         (authenticationTest (v10 says (v74 eqf v75)) ⇔ F) ∧
         (authenticationTest (v10 says v76 says v77) ⇔ F) ∧
         (authenticationTest (v10 says v78 speaks_for v79) ⇔ F) ∧
         (authenticationTest (v10 says v80 controls v81) ⇔ F) ∧
         (authenticationTest (v10 says reps v82 v83 v84) ⇔ F) ∧
         (authenticationTest (v10 says v85 domi v86) ⇔ F) ∧
         (authenticationTest (v10 says v87 eqi v88) ⇔ F) ∧
         (authenticationTest (v10 says v89 doms v90) ⇔ F) ∧
         (authenticationTest (v10 says v91 eqs v92) ⇔ F) ∧
         (authenticationTest (v10 says v93 eqn v94) ⇔ F) ∧
         (authenticationTest (v10 says v95 lte v96) ⇔ F) ∧
         (authenticationTest (v10 says v97 lt v98) ⇔ F) ∧
         (authenticationTest (v12 speaks_for v13) ⇔ F) ∧
         (authenticationTest (v14 controls v15) ⇔ F) ∧
         (authenticationTest (reps v16 v17 v18) ⇔ F) ∧
         (authenticationTest (v19 domi v20) ⇔ F) ∧
         (authenticationTest (v21 eqi v22) ⇔ F) ∧
         (authenticationTest (v23 doms v24) ⇔ F) ∧
         (authenticationTest (v25 eqs v26) ⇔ F) ∧
         (authenticationTest (v27 eqn v28) ⇔ F) ∧
         (authenticationTest (v29 lte v30) ⇔ F) ∧
         (authenticationTest (v31 lt v32) ⇔ F)

   [authenticationTest_ind]  Theorem

      |- ∀P.
           (∀cmd. P (Name PlatoonLeader says prop cmd)) ∧ P TT ∧ P FF ∧
           (∀v. P (prop v)) ∧ (∀v1. P (notf v1)) ∧
           (∀v2 v3. P (v2 andf v3)) ∧ (∀v4 v5. P (v4 orf v5)) ∧
           (∀v6 v7. P (v6 impf v7)) ∧ (∀v8 v9. P (v8 eqf v9)) ∧
           (∀v10. P (v10 says TT)) ∧ (∀v10. P (v10 says FF)) ∧
           (∀v133 v134 v66. P (v133 meet v134 says prop v66)) ∧
           (∀v135 v136 v66. P (v135 quoting v136 says prop v66)) ∧
           (∀v10 v67. P (v10 says notf v67)) ∧
           (∀v10 v68 v69. P (v10 says (v68 andf v69))) ∧
           (∀v10 v70 v71. P (v10 says (v70 orf v71))) ∧
           (∀v10 v72 v73. P (v10 says (v72 impf v73))) ∧
           (∀v10 v74 v75. P (v10 says (v74 eqf v75))) ∧
           (∀v10 v76 v77. P (v10 says v76 says v77)) ∧
           (∀v10 v78 v79. P (v10 says v78 speaks_for v79)) ∧
           (∀v10 v80 v81. P (v10 says v80 controls v81)) ∧
           (∀v10 v82 v83 v84. P (v10 says reps v82 v83 v84)) ∧
           (∀v10 v85 v86. P (v10 says v85 domi v86)) ∧
           (∀v10 v87 v88. P (v10 says v87 eqi v88)) ∧
           (∀v10 v89 v90. P (v10 says v89 doms v90)) ∧
           (∀v10 v91 v92. P (v10 says v91 eqs v92)) ∧
           (∀v10 v93 v94. P (v10 says v93 eqn v94)) ∧
           (∀v10 v95 v96. P (v10 says v95 lte v96)) ∧
           (∀v10 v97 v98. P (v10 says v97 lt v98)) ∧
           (∀v12 v13. P (v12 speaks_for v13)) ∧
           (∀v14 v15. P (v14 controls v15)) ∧
           (∀v16 v17 v18. P (reps v16 v17 v18)) ∧
           (∀v19 v20. P (v19 domi v20)) ∧ (∀v21 v22. P (v21 eqi v22)) ∧
           (∀v23 v24. P (v23 doms v24)) ∧ (∀v25 v26. P (v25 eqs v26)) ∧
           (∀v27 v28. P (v27 eqn v28)) ∧ (∀v29 v30. P (v29 lte v30)) ∧
           (∀v31 v32. P (v31 lt v32)) ⇒
           ∀v. P v


*)
end
