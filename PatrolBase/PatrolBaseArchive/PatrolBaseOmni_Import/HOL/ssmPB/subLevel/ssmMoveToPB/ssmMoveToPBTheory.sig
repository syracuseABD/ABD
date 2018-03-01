signature ssmMoveToPBTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val authTestMoveToPB_primitive_def : thm
    val secContextMoveToPB_def : thm
    val ssmMoveToPBStateInterp_def : thm

  (*  Theorems  *)
    val PlatoonLeader_exec_slCommand_justified_thm : thm
    val PlatoonLeader_slCommand_lemma : thm
    val authTestMoveToPB_cmd_reject_lemma : thm
    val authTestMoveToPB_def : thm
    val authTestMoveToPB_ind : thm
    val moveToPBNS_def : thm
    val moveToPBNS_ind : thm
    val moveToPBOut_def : thm
    val moveToPBOut_ind : thm

  val ssmMoveToPB_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [MoveToPBType] Parent theory of "ssmMoveToPB"

   [OMNIType] Parent theory of "ssmMoveToPB"

   [ssm11] Parent theory of "ssmMoveToPB"

   [authTestMoveToPB_primitive_def]  Definition

      |- authTestMoveToPB =
         WFREC (@R. WF R)
           (λauthTestMoveToPB a.
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

   [secContextMoveToPB_def]  Definition

      |- ∀cmd.
           secContextMoveToPB cmd =
           [Name PlatoonLeader controls prop (SOME (SLc cmd))]

   [ssmMoveToPBStateInterp_def]  Definition

      |- ∀state. ssmMoveToPBStateInterp state = TT

   [PlatoonLeader_exec_slCommand_justified_thm]  Theorem

      |- ∀NS Out M Oi Os.
           TR (M,Oi,Os) (exec (SLc slCommand))
             (CFG authTestMoveToPB ssmMoveToPBStateInterp
                (secContextMoveToPB slCommand)
                (Name PlatoonLeader says prop (SOME (SLc slCommand))::ins)
                s outs)
             (CFG authTestMoveToPB ssmMoveToPBStateInterp
                (secContextMoveToPB slCommand) ins
                (NS s (exec (SLc slCommand)))
                (Out s (exec (SLc slCommand))::outs)) ⇔
           authTestMoveToPB
             (Name PlatoonLeader says prop (SOME (SLc slCommand))) ∧
           CFGInterpret (M,Oi,Os)
             (CFG authTestMoveToPB ssmMoveToPBStateInterp
                (secContextMoveToPB slCommand)
                (Name PlatoonLeader says prop (SOME (SLc slCommand))::ins)
                s outs) ∧ (M,Oi,Os) sat prop (SOME (SLc slCommand))

   [PlatoonLeader_slCommand_lemma]  Theorem

      |- CFGInterpret (M,Oi,Os)
           (CFG authTestMoveToPB ssmMoveToPBStateInterp
              (secContextMoveToPB slCommand)
              (Name PlatoonLeader says prop (SOME (SLc slCommand))::ins) s
              outs) ⇒
         (M,Oi,Os) sat prop (SOME (SLc slCommand))

   [authTestMoveToPB_cmd_reject_lemma]  Theorem

      |- ∀cmd. ¬authTestMoveToPB (prop (SOME cmd))

   [authTestMoveToPB_def]  Theorem

      |- (authTestMoveToPB (Name PlatoonLeader says prop cmd) ⇔ T) ∧
         (authTestMoveToPB TT ⇔ F) ∧ (authTestMoveToPB FF ⇔ F) ∧
         (authTestMoveToPB (prop v) ⇔ F) ∧
         (authTestMoveToPB (notf v1) ⇔ F) ∧
         (authTestMoveToPB (v2 andf v3) ⇔ F) ∧
         (authTestMoveToPB (v4 orf v5) ⇔ F) ∧
         (authTestMoveToPB (v6 impf v7) ⇔ F) ∧
         (authTestMoveToPB (v8 eqf v9) ⇔ F) ∧
         (authTestMoveToPB (v10 says TT) ⇔ F) ∧
         (authTestMoveToPB (v10 says FF) ⇔ F) ∧
         (authTestMoveToPB (v133 meet v134 says prop v66) ⇔ F) ∧
         (authTestMoveToPB (v135 quoting v136 says prop v66) ⇔ F) ∧
         (authTestMoveToPB (v10 says notf v67) ⇔ F) ∧
         (authTestMoveToPB (v10 says (v68 andf v69)) ⇔ F) ∧
         (authTestMoveToPB (v10 says (v70 orf v71)) ⇔ F) ∧
         (authTestMoveToPB (v10 says (v72 impf v73)) ⇔ F) ∧
         (authTestMoveToPB (v10 says (v74 eqf v75)) ⇔ F) ∧
         (authTestMoveToPB (v10 says v76 says v77) ⇔ F) ∧
         (authTestMoveToPB (v10 says v78 speaks_for v79) ⇔ F) ∧
         (authTestMoveToPB (v10 says v80 controls v81) ⇔ F) ∧
         (authTestMoveToPB (v10 says reps v82 v83 v84) ⇔ F) ∧
         (authTestMoveToPB (v10 says v85 domi v86) ⇔ F) ∧
         (authTestMoveToPB (v10 says v87 eqi v88) ⇔ F) ∧
         (authTestMoveToPB (v10 says v89 doms v90) ⇔ F) ∧
         (authTestMoveToPB (v10 says v91 eqs v92) ⇔ F) ∧
         (authTestMoveToPB (v10 says v93 eqn v94) ⇔ F) ∧
         (authTestMoveToPB (v10 says v95 lte v96) ⇔ F) ∧
         (authTestMoveToPB (v10 says v97 lt v98) ⇔ F) ∧
         (authTestMoveToPB (v12 speaks_for v13) ⇔ F) ∧
         (authTestMoveToPB (v14 controls v15) ⇔ F) ∧
         (authTestMoveToPB (reps v16 v17 v18) ⇔ F) ∧
         (authTestMoveToPB (v19 domi v20) ⇔ F) ∧
         (authTestMoveToPB (v21 eqi v22) ⇔ F) ∧
         (authTestMoveToPB (v23 doms v24) ⇔ F) ∧
         (authTestMoveToPB (v25 eqs v26) ⇔ F) ∧
         (authTestMoveToPB (v27 eqn v28) ⇔ F) ∧
         (authTestMoveToPB (v29 lte v30) ⇔ F) ∧
         (authTestMoveToPB (v31 lt v32) ⇔ F)

   [authTestMoveToPB_ind]  Theorem

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

   [moveToPBNS_def]  Theorem

      |- (moveToPBNS PLAN_PB (exec (SLc pltForm)) = PLT_FORM) ∧
         (moveToPBNS PLAN_PB (exec (SLc incomplete)) = PLAN_PB) ∧
         (moveToPBNS PLT_FORM (exec (SLc pltMove)) = PLT_MOVE) ∧
         (moveToPBNS PLT_FORM (exec (SLc incomplete)) = PLT_FORM) ∧
         (moveToPBNS PLT_MOVE (exec (SLc pltHalt)) = PLT_HALT) ∧
         (moveToPBNS PLT_MOVE (exec (SLc incomplete)) = PLT_MOVE) ∧
         (moveToPBNS PLT_HALT (exec (SLc complete)) = COMPLETE) ∧
         (moveToPBNS PLT_HALT (exec (SLc incomplete)) = PLT_HALT) ∧
         (moveToPBNS s (trap (SLc cmd)) = s) ∧
         (moveToPBNS s (discard (SLc cmd)) = s)

   [moveToPBNS_ind]  Theorem

      |- ∀P.
           P PLAN_PB (exec (SLc pltForm)) ∧
           P PLAN_PB (exec (SLc incomplete)) ∧
           P PLT_FORM (exec (SLc pltMove)) ∧
           P PLT_FORM (exec (SLc incomplete)) ∧
           P PLT_MOVE (exec (SLc pltHalt)) ∧
           P PLT_MOVE (exec (SLc incomplete)) ∧
           P PLT_HALT (exec (SLc complete)) ∧
           P PLT_HALT (exec (SLc incomplete)) ∧
           (∀s cmd. P s (trap (SLc cmd))) ∧
           (∀s cmd. P s (discard (SLc cmd))) ∧
           (∀s v6. P s (discard (ESCc v6))) ∧
           (∀s v9. P s (trap (ESCc v9))) ∧
           (∀v12. P PLAN_PB (exec (ESCc v12))) ∧
           P PLAN_PB (exec (SLc pltMove)) ∧
           P PLAN_PB (exec (SLc pltHalt)) ∧
           P PLAN_PB (exec (SLc complete)) ∧
           (∀v15. P PLT_FORM (exec (ESCc v15))) ∧
           P PLT_FORM (exec (SLc pltForm)) ∧
           P PLT_FORM (exec (SLc pltHalt)) ∧
           P PLT_FORM (exec (SLc complete)) ∧
           (∀v18. P PLT_MOVE (exec (ESCc v18))) ∧
           P PLT_MOVE (exec (SLc pltForm)) ∧
           P PLT_MOVE (exec (SLc pltMove)) ∧
           P PLT_MOVE (exec (SLc complete)) ∧
           (∀v21. P PLT_HALT (exec (ESCc v21))) ∧
           P PLT_HALT (exec (SLc pltForm)) ∧
           P PLT_HALT (exec (SLc pltMove)) ∧
           P PLT_HALT (exec (SLc pltHalt)) ∧
           (∀v23. P COMPLETE (exec v23)) ⇒
           ∀v v1. P v v1

   [moveToPBOut_def]  Theorem

      |- (moveToPBOut PLAN_PB (exec (SLc pltForm)) = PLTForm) ∧
         (moveToPBOut PLAN_PB (exec (SLc incomplete)) = PLTPlan) ∧
         (moveToPBOut PLT_FORM (exec (SLc pltMove)) = PLTMove) ∧
         (moveToPBOut PLT_FORM (exec (SLc incomplete)) = PLTForm) ∧
         (moveToPBOut PLT_MOVE (exec (SLc pltHalt)) = PLTHalt) ∧
         (moveToPBOut PLT_MOVE (exec (SLc incomplete)) = PLTMove) ∧
         (moveToPBOut PLT_HALT (exec (SLc complete)) = Complete) ∧
         (moveToPBOut PLT_HALT (exec (SLc incomplete)) = PLTHalt) ∧
         (moveToPBOut s (trap (SLc cmd)) = unAuthorized) ∧
         (moveToPBOut s (discard (SLc cmd)) = unAuthenticated)

   [moveToPBOut_ind]  Theorem

      |- ∀P.
           P PLAN_PB (exec (SLc pltForm)) ∧
           P PLAN_PB (exec (SLc incomplete)) ∧
           P PLT_FORM (exec (SLc pltMove)) ∧
           P PLT_FORM (exec (SLc incomplete)) ∧
           P PLT_MOVE (exec (SLc pltHalt)) ∧
           P PLT_MOVE (exec (SLc incomplete)) ∧
           P PLT_HALT (exec (SLc complete)) ∧
           P PLT_HALT (exec (SLc incomplete)) ∧
           (∀s cmd. P s (trap (SLc cmd))) ∧
           (∀s cmd. P s (discard (SLc cmd))) ∧
           (∀s v6. P s (discard (ESCc v6))) ∧
           (∀s v9. P s (trap (ESCc v9))) ∧
           (∀v12. P PLAN_PB (exec (ESCc v12))) ∧
           P PLAN_PB (exec (SLc pltMove)) ∧
           P PLAN_PB (exec (SLc pltHalt)) ∧
           P PLAN_PB (exec (SLc complete)) ∧
           (∀v15. P PLT_FORM (exec (ESCc v15))) ∧
           P PLT_FORM (exec (SLc pltForm)) ∧
           P PLT_FORM (exec (SLc pltHalt)) ∧
           P PLT_FORM (exec (SLc complete)) ∧
           (∀v18. P PLT_MOVE (exec (ESCc v18))) ∧
           P PLT_MOVE (exec (SLc pltForm)) ∧
           P PLT_MOVE (exec (SLc pltMove)) ∧
           P PLT_MOVE (exec (SLc complete)) ∧
           (∀v21. P PLT_HALT (exec (ESCc v21))) ∧
           P PLT_HALT (exec (SLc pltForm)) ∧
           P PLT_HALT (exec (SLc pltMove)) ∧
           P PLT_HALT (exec (SLc pltHalt)) ∧
           (∀v23. P COMPLETE (exec v23)) ⇒
           ∀v v1. P v v1


*)
end
