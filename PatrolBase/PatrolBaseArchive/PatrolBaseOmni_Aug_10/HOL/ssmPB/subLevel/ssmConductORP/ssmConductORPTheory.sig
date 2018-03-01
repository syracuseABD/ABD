signature ssmConductORPTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val authTestConductORP_primitive_def : thm
    val secContextConductORP_def : thm
    val ssmConductORPStateInterp_def : thm

  (*  Theorems  *)
    val PlatoonLeader_exec_plCommand_justified_thm : thm
    val PlatoonLeader_plCommand_lemma : thm
    val PlatoonSergeant_exec_psgCommand_justified_thm : thm
    val PlatoonSergeant_psgCommand_lemma : thm
    val authTestConductORP_cmd_reject_lemma : thm
    val authTestConductORP_def : thm
    val authTestConductORP_ind : thm
    val conductORPNS_def : thm
    val conductORPNS_ind : thm
    val conductORPOut_def : thm
    val conductORPOut_ind : thm

  val ssmConductORP_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [ConductORPType] Parent theory of "ssmConductORP"

   [OMNIType] Parent theory of "ssmConductORP"

   [ssm11] Parent theory of "ssmConductORP"

   [authTestConductORP_primitive_def]  Definition

      |- authTestConductORP =
         WFREC (@R. WF R)
           (λauthTestConductORP a.
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

   [secContextConductORP_def]  Definition

      |- ∀plcmd psgcmd incomplete.
           secContextConductORP plcmd psgcmd incomplete =
           [Name PlatoonLeader controls prop (SOME (SLc (PL plcmd)));
            Name PlatoonSergeant controls prop (SOME (SLc (PSG psgcmd)));
            Name PlatoonLeader says prop (SOME (SLc (PSG psgcmd))) impf
            prop NONE;
            Name PlatoonSergeant says prop (SOME (SLc (PL plcmd))) impf
            prop NONE]

   [ssmConductORPStateInterp_def]  Definition

      |- ∀slState. ssmConductORPStateInterp slState = TT

   [PlatoonLeader_exec_plCommand_justified_thm]  Theorem

      |- ∀NS Out M Oi Os.
           TR (M,Oi,Os) (exec (SLc (PL plCommand)))
             (CFG authTestConductORP ssmConductORPStateInterp
                (secContextConductORP plCommand psgCommand incomplete)
                (Name PlatoonLeader says prop (SOME (SLc (PL plCommand)))::
                     ins) s outs)
             (CFG authTestConductORP ssmConductORPStateInterp
                (secContextConductORP plCommand psgCommand incomplete) ins
                (NS s (exec (SLc (PL plCommand))))
                (Out s (exec (SLc (PL plCommand)))::outs)) ⇔
           authTestConductORP
             (Name PlatoonLeader says prop (SOME (SLc (PL plCommand)))) ∧
           CFGInterpret (M,Oi,Os)
             (CFG authTestConductORP ssmConductORPStateInterp
                (secContextConductORP plCommand psgCommand incomplete)
                (Name PlatoonLeader says prop (SOME (SLc (PL plCommand)))::
                     ins) s outs) ∧
           (M,Oi,Os) sat prop (SOME (SLc (PL plCommand)))

   [PlatoonLeader_plCommand_lemma]  Theorem

      |- CFGInterpret (M,Oi,Os)
           (CFG authTestConductORP ssmConductORPStateInterp
              (secContextConductORP plCommand psgCommand incomplete)
              (Name PlatoonLeader says prop (SOME (SLc (PL plCommand)))::
                   ins) s outs) ⇒
         (M,Oi,Os) sat prop (SOME (SLc (PL plCommand)))

   [PlatoonSergeant_exec_psgCommand_justified_thm]  Theorem

      |- ∀NS Out M Oi Os.
           TR (M,Oi,Os) (exec (SLc (PSG psgCommand)))
             (CFG authTestConductORP ssmConductORPStateInterp
                (secContextConductORP plCommand psgCommand incomplete)
                (Name PlatoonSergeant says
                 prop (SOME (SLc (PSG psgCommand)))::ins) s outs)
             (CFG authTestConductORP ssmConductORPStateInterp
                (secContextConductORP plCommand psgCommand incomplete) ins
                (NS s (exec (SLc (PSG psgCommand))))
                (Out s (exec (SLc (PSG psgCommand)))::outs)) ⇔
           authTestConductORP
             (Name PlatoonSergeant says
              prop (SOME (SLc (PSG psgCommand)))) ∧
           CFGInterpret (M,Oi,Os)
             (CFG authTestConductORP ssmConductORPStateInterp
                (secContextConductORP plCommand psgCommand incomplete)
                (Name PlatoonSergeant says
                 prop (SOME (SLc (PSG psgCommand)))::ins) s outs) ∧
           (M,Oi,Os) sat prop (SOME (SLc (PSG psgCommand)))

   [PlatoonSergeant_psgCommand_lemma]  Theorem

      |- CFGInterpret (M,Oi,Os)
           (CFG authTestConductORP ssmConductORPStateInterp
              (secContextConductORP plCommand psgCommand incomplete)
              (Name PlatoonSergeant says
               prop (SOME (SLc (PSG psgCommand)))::ins) s outs) ⇒
         (M,Oi,Os) sat prop (SOME (SLc (PSG psgCommand)))

   [authTestConductORP_cmd_reject_lemma]  Theorem

      |- ∀cmd. ¬authTestConductORP (prop (SOME cmd))

   [authTestConductORP_def]  Theorem

      |- (authTestConductORP (Name PlatoonLeader says prop cmd) ⇔ T) ∧
         (authTestConductORP (Name PlatoonSergeant says prop cmd) ⇔ T) ∧
         (authTestConductORP TT ⇔ F) ∧ (authTestConductORP FF ⇔ F) ∧
         (authTestConductORP (prop v) ⇔ F) ∧
         (authTestConductORP (notf v1) ⇔ F) ∧
         (authTestConductORP (v2 andf v3) ⇔ F) ∧
         (authTestConductORP (v4 orf v5) ⇔ F) ∧
         (authTestConductORP (v6 impf v7) ⇔ F) ∧
         (authTestConductORP (v8 eqf v9) ⇔ F) ∧
         (authTestConductORP (v10 says TT) ⇔ F) ∧
         (authTestConductORP (v10 says FF) ⇔ F) ∧
         (authTestConductORP (v133 meet v134 says prop v66) ⇔ F) ∧
         (authTestConductORP (v135 quoting v136 says prop v66) ⇔ F) ∧
         (authTestConductORP (v10 says notf v67) ⇔ F) ∧
         (authTestConductORP (v10 says (v68 andf v69)) ⇔ F) ∧
         (authTestConductORP (v10 says (v70 orf v71)) ⇔ F) ∧
         (authTestConductORP (v10 says (v72 impf v73)) ⇔ F) ∧
         (authTestConductORP (v10 says (v74 eqf v75)) ⇔ F) ∧
         (authTestConductORP (v10 says v76 says v77) ⇔ F) ∧
         (authTestConductORP (v10 says v78 speaks_for v79) ⇔ F) ∧
         (authTestConductORP (v10 says v80 controls v81) ⇔ F) ∧
         (authTestConductORP (v10 says reps v82 v83 v84) ⇔ F) ∧
         (authTestConductORP (v10 says v85 domi v86) ⇔ F) ∧
         (authTestConductORP (v10 says v87 eqi v88) ⇔ F) ∧
         (authTestConductORP (v10 says v89 doms v90) ⇔ F) ∧
         (authTestConductORP (v10 says v91 eqs v92) ⇔ F) ∧
         (authTestConductORP (v10 says v93 eqn v94) ⇔ F) ∧
         (authTestConductORP (v10 says v95 lte v96) ⇔ F) ∧
         (authTestConductORP (v10 says v97 lt v98) ⇔ F) ∧
         (authTestConductORP (v12 speaks_for v13) ⇔ F) ∧
         (authTestConductORP (v14 controls v15) ⇔ F) ∧
         (authTestConductORP (reps v16 v17 v18) ⇔ F) ∧
         (authTestConductORP (v19 domi v20) ⇔ F) ∧
         (authTestConductORP (v21 eqi v22) ⇔ F) ∧
         (authTestConductORP (v23 doms v24) ⇔ F) ∧
         (authTestConductORP (v25 eqs v26) ⇔ F) ∧
         (authTestConductORP (v27 eqn v28) ⇔ F) ∧
         (authTestConductORP (v29 lte v30) ⇔ F) ∧
         (authTestConductORP (v31 lt v32) ⇔ F)

   [authTestConductORP_ind]  Theorem

      |- ∀P.
           (∀cmd. P (Name PlatoonLeader says prop cmd)) ∧
           (∀cmd. P (Name PlatoonSergeant says prop cmd)) ∧ P TT ∧ P FF ∧
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

   [conductORPNS_def]  Theorem

      |- (conductORPNS CONDUCT_ORP (exec (PL secure)) = SECURE) ∧
         (conductORPNS CONDUCT_ORP (exec (PL plIncomplete)) =
          CONDUCT_ORP) ∧
         (conductORPNS SECURE (exec (PSG actionsIn)) = ACTIONS_IN) ∧
         (conductORPNS SECURE (exec (PSG psgIncomplete)) = SECURE) ∧
         (conductORPNS ACTIONS_IN (exec (PL withdraw)) = WITHDRAW) ∧
         (conductORPNS ACTIONS_IN (exec (PL plIncomplete)) = ACTIONS_IN) ∧
         (conductORPNS WITHDRAW (exec (PL complete)) = COMPLETE) ∧
         (conductORPNS WITHDRAW (exec (PL plIncomplete)) = WITHDRAW) ∧
         (conductORPNS s (trap (PL cmd')) = s) ∧
         (conductORPNS s (trap (PSG cmd)) = s) ∧
         (conductORPNS s (discard (PL cmd')) = s) ∧
         (conductORPNS s (discard (PSG cmd)) = s)

   [conductORPNS_ind]  Theorem

      |- ∀P.
           P CONDUCT_ORP (exec (PL secure)) ∧
           P CONDUCT_ORP (exec (PL plIncomplete)) ∧
           P SECURE (exec (PSG actionsIn)) ∧
           P SECURE (exec (PSG psgIncomplete)) ∧
           P ACTIONS_IN (exec (PL withdraw)) ∧
           P ACTIONS_IN (exec (PL plIncomplete)) ∧
           P WITHDRAW (exec (PL complete)) ∧
           P WITHDRAW (exec (PL plIncomplete)) ∧
           (∀s cmd. P s (trap (PL cmd))) ∧ (∀s cmd. P s (trap (PSG cmd))) ∧
           (∀s cmd. P s (discard (PL cmd))) ∧
           (∀s cmd. P s (discard (PSG cmd))) ∧
           P CONDUCT_ORP (exec (PL withdraw)) ∧
           P CONDUCT_ORP (exec (PL complete)) ∧
           (∀v11. P CONDUCT_ORP (exec (PSG v11))) ∧
           (∀v13. P SECURE (exec (PL v13))) ∧
           P ACTIONS_IN (exec (PL secure)) ∧
           P ACTIONS_IN (exec (PL complete)) ∧
           (∀v17. P ACTIONS_IN (exec (PSG v17))) ∧
           P WITHDRAW (exec (PL secure)) ∧
           P WITHDRAW (exec (PL withdraw)) ∧
           (∀v20. P WITHDRAW (exec (PSG v20))) ∧
           (∀v21. P COMPLETE (exec v21)) ⇒
           ∀v v1. P v v1

   [conductORPOut_def]  Theorem

      |- (conductORPOut CONDUCT_ORP (exec (PL secure)) = Secure) ∧
         (conductORPOut CONDUCT_ORP (exec (PL plIncomplete)) =
          ConductORP) ∧
         (conductORPOut SECURE (exec (PSG actionsIn)) = ActionsIn) ∧
         (conductORPOut SECURE (exec (PSG psgIncomplete)) = Secure) ∧
         (conductORPOut ACTIONS_IN (exec (PL withdraw)) = Withdraw) ∧
         (conductORPOut ACTIONS_IN (exec (PL plIncomplete)) = ActionsIn) ∧
         (conductORPOut WITHDRAW (exec (PL complete)) = Complete) ∧
         (conductORPOut WITHDRAW (exec (PL plIncomplete)) = Withdraw) ∧
         (conductORPOut s (trap (PL cmd')) = unAuthorized) ∧
         (conductORPOut s (trap (PSG cmd)) = unAuthorized) ∧
         (conductORPOut s (discard (PL cmd')) = unAuthenticated) ∧
         (conductORPOut s (discard (PSG cmd)) = unAuthenticated)

   [conductORPOut_ind]  Theorem

      |- ∀P.
           P CONDUCT_ORP (exec (PL secure)) ∧
           P CONDUCT_ORP (exec (PL plIncomplete)) ∧
           P SECURE (exec (PSG actionsIn)) ∧
           P SECURE (exec (PSG psgIncomplete)) ∧
           P ACTIONS_IN (exec (PL withdraw)) ∧
           P ACTIONS_IN (exec (PL plIncomplete)) ∧
           P WITHDRAW (exec (PL complete)) ∧
           P WITHDRAW (exec (PL plIncomplete)) ∧
           (∀s cmd. P s (trap (PL cmd))) ∧ (∀s cmd. P s (trap (PSG cmd))) ∧
           (∀s cmd. P s (discard (PL cmd))) ∧
           (∀s cmd. P s (discard (PSG cmd))) ∧
           P CONDUCT_ORP (exec (PL withdraw)) ∧
           P CONDUCT_ORP (exec (PL complete)) ∧
           (∀v11. P CONDUCT_ORP (exec (PSG v11))) ∧
           (∀v13. P SECURE (exec (PL v13))) ∧
           P ACTIONS_IN (exec (PL secure)) ∧
           P ACTIONS_IN (exec (PL complete)) ∧
           (∀v17. P ACTIONS_IN (exec (PSG v17))) ∧
           P WITHDRAW (exec (PL secure)) ∧
           P WITHDRAW (exec (PL withdraw)) ∧
           (∀v20. P WITHDRAW (exec (PSG v20))) ∧
           (∀v21. P COMPLETE (exec v21)) ⇒
           ∀v v1. P v v1


*)
end
