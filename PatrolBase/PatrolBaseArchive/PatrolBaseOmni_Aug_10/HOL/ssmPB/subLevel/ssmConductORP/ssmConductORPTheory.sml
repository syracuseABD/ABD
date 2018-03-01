structure ssmConductORPTheory :> ssmConductORPTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading ssmConductORPTheory ... " else ()
  open Type Term Thm
  infixr -->

  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  (*  Parents *)
  local open ConductORPTypeTheory OMNITypeTheory ssm11Theory
  in end;
  val _ = Theory.link_parents
          ("ssmConductORP",
          Arbnum.fromString "1500769213",
          Arbnum.fromString "98848")
          [("ConductORPType",
           Arbnum.fromString "1500769210",
           Arbnum.fromString "919246"),
           ("ssm11",
           Arbnum.fromString "1499652452",
           Arbnum.fromString "890464"),
           ("OMNIType",
           Arbnum.fromString "1499574745",
           Arbnum.fromString "168021")];
  val _ = Theory.incorporate_types "ssmConductORP" [];

  val idvector = 
    let fun ID(thy,oth) = {Thy = thy, Other = oth}
    in Vector.fromList
  [ID("min", "fun"), ID("aclfoundation", "Form"),
   ID("ConductORPType", "stateRole"), ID("ssm11", "order"),
   ID("OMNIType", "command"), ID("ConductORPType", "slCommand"),
   ID("ConductORPType", "slState"), ID("list", "list"),
   ID("ConductORPType", "psgCommand"), ID("ConductORPType", "plCommand"),
   ID("ConductORPType", "slOutput"), ID("ssm11", "trType"),
   ID("min", "bool"), ID("aclfoundation", "Kripke"),
   ID("aclfoundation", "po"), ID("OMNIType", "output"),
   ID("aclfoundation", "Princ"), ID("aclfoundation", "IntLevel"),
   ID("aclfoundation", "SecLevel"), ID("num", "num"), ID("bool", "!"),
   ID("pair", ","), ID("pair", "prod"), ID("bool", "/\\"), ID("min", "="),
   ID("min", "==>"), ID("min", "@"), ID("ConductORPType", "ACTIONS_IN"),
   ID("ConductORPType", "ActionsIn"), ID("ssm11", "CFG"),
   ID("ssm11", "configuration"), ID("ssm11", "CFGInterpret"),
   ID("ConductORPType", "COMPLETE"), ID("ConductORPType", "CONDUCT_ORP"),
   ID("list", "CONS"), ID("ConductORPType", "Complete"),
   ID("ConductORPType", "ConductORP"), ID("bool", "F"),
   ID("aclfoundation", "FF"), ID("aclfoundation", "Form_CASE"),
   ID("combin", "I"), ID("list", "NIL"), ID("ssm11", "NONE"),
   ID("aclfoundation", "Name"), ID("ConductORPType", "PL"),
   ID("ConductORPType", "PSG"), ID("ConductORPType", "PlatoonLeader"),
   ID("ConductORPType", "PlatoonSergeant"),
   ID("aclfoundation", "Princ_CASE"), ID("ConductORPType", "SECURE"),
   ID("OMNIType", "SLc"), ID("ssm11", "SOME"),
   ID("ConductORPType", "Secure"), ID("bool", "T"), ID("ssm11", "TR"),
   ID("aclfoundation", "TT"), ID("relation", "WF"),
   ID("relation", "WFREC"), ID("ConductORPType", "WITHDRAW"),
   ID("ConductORPType", "Withdraw"), ID("ConductORPType", "actionsIn"),
   ID("aclfoundation", "andf"), ID("ssmConductORP", "authTestConductORP"),
   ID("ConductORPType", "complete"), ID("ssmConductORP", "conductORPNS"),
   ID("ssmConductORP", "conductORPOut"), ID("aclfoundation", "controls"),
   ID("ssm11", "discard"), ID("aclfoundation", "domi"),
   ID("aclfoundation", "doms"), ID("aclfoundation", "eqf"),
   ID("aclfoundation", "eqi"), ID("aclfoundation", "eqn"),
   ID("aclfoundation", "eqs"), ID("ssm11", "exec"),
   ID("aclfoundation", "impf"), ID("aclfoundation", "lt"),
   ID("aclfoundation", "lte"), ID("aclfoundation", "meet"),
   ID("aclfoundation", "notf"), ID("aclfoundation", "orf"),
   ID("ConductORPType", "plIncomplete"), ID("aclfoundation", "prop"),
   ID("ConductORPType", "psgIncomplete"), ID("aclfoundation", "quoting"),
   ID("aclfoundation", "reps"), ID("aclrules", "sat"),
   ID("aclfoundation", "says"),
   ID("ssmConductORP", "secContextConductORP"),
   ID("ConductORPType", "secure"), ID("aclfoundation", "speaks_for"),
   ID("ssmConductORP", "ssmConductORPStateInterp"), ID("ssm11", "trap"),
   ID("ConductORPType", "unAuthenticated"),
   ID("ConductORPType", "unAuthorized"), ID("ConductORPType", "withdraw"),
   ID("bool", "~")]
  end;
  local open SharingTables
  in
  val tyvector = build_type_vector idvector
  [TYV "'e", TYV "'d", TYOP [2], TYOP [5], TYOP [4, 3], TYOP [3, 4],
   TYOP [1, 5, 2, 1, 0], TYOP [6], TYOP [0, 7, 6], TYOP [7, 6],
   TYOP [0, 3, 9], TYOP [8], TYOP [0, 11, 10], TYOP [9], TYOP [0, 13, 12],
   TYOP [10], TYOP [11, 3], TYOP [0, 16, 15], TYOP [0, 7, 17],
   TYOP [0, 16, 7], TYOP [0, 7, 19], TYOP [12], TYOP [0, 6, 21], TYV "'b",
   TYOP [13, 5, 23, 2, 1, 0], TYOP [11, 4], TYOP [0, 25, 7],
   TYOP [0, 7, 26], TYOP [14, 1], TYOP [14, 0], TYOP [15, 15],
   TYOP [0, 25, 30], TYOP [0, 7, 31], TYOP [0, 16, 21], TYOP [0, 7, 33],
   TYOP [0, 6, 22], TYOP [7, 30], TYOP [16, 2], TYOP [17, 2, 1],
   TYOP [18, 2, 0], TYOP [19], TYOP [0, 22, 21], TYOP [0, 38, 21],
   TYOP [0, 42, 21], TYOP [0, 24, 21], TYOP [0, 44, 21], TYOP [0, 37, 21],
   TYOP [0, 46, 21], TYOP [0, 39, 21], TYOP [0, 48, 21], TYOP [0, 4, 21],
   TYOP [0, 50, 21], TYOP [0, 41, 21], TYOP [0, 32, 21], TYOP [0, 53, 21],
   TYOP [0, 27, 21], TYOP [0, 55, 21], TYOP [0, 34, 21], TYOP [0, 57, 21],
   TYOP [0, 40, 21], TYOP [0, 59, 21], TYOP [0, 5, 21], TYOP [0, 61, 21],
   TYOP [0, 13, 21], TYOP [0, 63, 21], TYOP [0, 28, 21], TYOP [0, 65, 21],
   TYOP [0, 29, 21], TYOP [0, 67, 21], TYOP [0, 11, 21], TYOP [0, 69, 21],
   TYOP [0, 3, 21], TYOP [0, 71, 21], TYOP [0, 7, 21], TYOP [0, 73, 21],
   TYOP [0, 33, 21], TYOP [22, 28, 29], TYOP [22, 24, 76],
   TYOP [0, 76, 77], TYOP [0, 24, 78], TYOP [0, 29, 76], TYOP [0, 28, 80],
   TYOP [0, 21, 21], TYOP [0, 21, 82], TYOP [0, 22, 41], TYOP [0, 9, 21],
   TYOP [0, 9, 85], TYOP [0, 15, 21], TYOP [0, 15, 87], TYOP [0, 7, 73],
   TYOP [0, 35, 21], TYOP [0, 90, 35], TYOP [30, 4, 1, 0, 30, 2, 7],
   TYOP [0, 36, 92], TYOP [0, 7, 93], TYOP [0, 9, 94], TYOP [0, 9, 95],
   TYOP [0, 8, 96], TYOP [0, 22, 97], TYOP [0, 92, 21], TYOP [0, 77, 99],
   TYOP [0, 9, 9], TYOP [0, 6, 101], TYOP [0, 36, 36], TYOP [0, 30, 103],
   TYOP [0, 40, 59], TYOP [0, 105, 21], TYOP [0, 105, 106],
   TYOP [0, 105, 107], TYOP [0, 39, 48], TYOP [0, 109, 108],
   TYOP [0, 109, 110], TYOP [0, 38, 42], TYOP [0, 112, 111],
   TYOP [0, 112, 113], TYOP [0, 37, 22], TYOP [0, 37, 115],
   TYOP [0, 116, 114], TYOP [0, 115, 117], TYOP [0, 37, 46],
   TYOP [0, 119, 118], TYOP [0, 115, 120], TYOP [0, 35, 121],
   TYOP [0, 35, 122], TYOP [0, 35, 123], TYOP [0, 35, 124],
   TYOP [0, 22, 125], TYOP [0, 61, 126], TYOP [0, 21, 127],
   TYOP [0, 21, 128], TYOP [0, 6, 129], TYOP [0, 2, 37], TYOP [0, 13, 3],
   TYOP [0, 11, 3], TYOP [0, 119, 21], TYOP [0, 119, 134], TYOP [0, 2, 21],
   TYOP [0, 136, 135], TYOP [0, 37, 137], TYOP [0, 3, 4], TYOP [0, 4, 5],
   TYOP [0, 92, 99], TYOP [0, 25, 141], TYOP [0, 77, 142],
   TYOP [0, 22, 22], TYOP [0, 144, 22], TYOP [0, 35, 145], TYOP [0, 6, 6],
   TYOP [0, 6, 147], TYOP [0, 37, 147], TYOP [0, 3, 16], TYOP [0, 38, 6],
   TYOP [0, 38, 151], TYOP [0, 39, 6], TYOP [0, 39, 153], TYOP [0, 40, 6],
   TYOP [0, 40, 155], TYOP [0, 4, 25], TYOP [0, 37, 37], TYOP [0, 37, 158],
   TYOP [0, 5, 6], TYOP [0, 37, 149], TYOP [0, 77, 22], TYOP [0, 37, 6],
   TYOP [0, 37, 163]]
  end
  val _ = Theory.incorporate_consts "ssmConductORP" tyvector
     [("ssmConductORPStateInterp", 8), ("secContextConductORP", 14),
      ("conductORPOut", 18), ("conductORPNS", 20),
      ("authTestConductORP", 22)];

  local open SharingTables
  in
  val tmvector = build_term_vector idvector tyvector
  [TMV("M", 24), TMV("NS", 27), TMV("Oi", 28), TMV("Os", 29),
   TMV("Out", 32), TMV("P", 22), TMV("P", 34), TMV("R", 35), TMV("a", 6),
   TMV("authTestConductORP", 22), TMV("cmd", 4), TMV("cmd", 5),
   TMV("cmd", 13), TMV("cmd", 11), TMV("cmd'", 13), TMV("incomplete", 3),
   TMV("ins", 9), TMV("outs", 36), TMV("plCommand", 13), TMV("plcmd", 13),
   TMV("psgCommand", 11), TMV("psgcmd", 11), TMV("s", 7),
   TMV("slState", 7), TMV("v", 6), TMV("v", 5), TMV("v", 7), TMV("v1", 6),
   TMV("v1", 16), TMV("v10", 37), TMV("v100", 6), TMV("v101", 6),
   TMV("v102", 6), TMV("v103", 6), TMV("v104", 6), TMV("v105", 6),
   TMV("v106", 6), TMV("v107", 6), TMV("v108", 6), TMV("v109", 37),
   TMV("v11", 11), TMV("v110", 6), TMV("v111", 37), TMV("v112", 37),
   TMV("v113", 37), TMV("v114", 6), TMV("v115", 37), TMV("v116", 37),
   TMV("v117", 6), TMV("v118", 38), TMV("v119", 38), TMV("v12", 37),
   TMV("v120", 38), TMV("v121", 38), TMV("v122", 39), TMV("v123", 39),
   TMV("v124", 39), TMV("v125", 39), TMV("v126", 40), TMV("v127", 40),
   TMV("v128", 40), TMV("v129", 40), TMV("v13", 37), TMV("v13", 13),
   TMV("v130", 40), TMV("v131", 40), TMV("v133", 37), TMV("v134", 37),
   TMV("v135", 37), TMV("v136", 37), TMV("v137", 2), TMV("v138", 37),
   TMV("v139", 37), TMV("v14", 37), TMV("v140", 37), TMV("v141", 37),
   TMV("v15", 6), TMV("v16", 37), TMV("v17", 37), TMV("v17", 11),
   TMV("v18", 6), TMV("v19", 38), TMV("v2", 6), TMV("v20", 38),
   TMV("v20", 11), TMV("v21", 38), TMV("v21", 3), TMV("v22", 38),
   TMV("v23", 39), TMV("v24", 39), TMV("v25", 39), TMV("v26", 39),
   TMV("v27", 40), TMV("v28", 40), TMV("v29", 40), TMV("v3", 6),
   TMV("v30", 40), TMV("v31", 40), TMV("v32", 40), TMV("v33", 5),
   TMV("v34", 6), TMV("v35", 6), TMV("v36", 6), TMV("v37", 6),
   TMV("v38", 6), TMV("v39", 6), TMV("v4", 6), TMV("v40", 6),
   TMV("v41", 6), TMV("v42", 6), TMV("v43", 37), TMV("v44", 6),
   TMV("v45", 37), TMV("v46", 37), TMV("v47", 37), TMV("v48", 6),
   TMV("v49", 37), TMV("v5", 6), TMV("v50", 37), TMV("v51", 6),
   TMV("v52", 38), TMV("v53", 38), TMV("v54", 38), TMV("v55", 38),
   TMV("v56", 39), TMV("v57", 39), TMV("v58", 39), TMV("v59", 39),
   TMV("v6", 6), TMV("v60", 40), TMV("v61", 40), TMV("v62", 40),
   TMV("v63", 40), TMV("v64", 40), TMV("v65", 40), TMV("v66", 5),
   TMV("v67", 6), TMV("v68", 6), TMV("v69", 6), TMV("v7", 6),
   TMV("v70", 6), TMV("v71", 6), TMV("v72", 6), TMV("v73", 6),
   TMV("v74", 6), TMV("v75", 6), TMV("v76", 37), TMV("v77", 6),
   TMV("v78", 37), TMV("v79", 37), TMV("v8", 6), TMV("v80", 37),
   TMV("v81", 6), TMV("v82", 37), TMV("v83", 37), TMV("v84", 6),
   TMV("v85", 38), TMV("v86", 38), TMV("v87", 38), TMV("v88", 38),
   TMV("v89", 39), TMV("v9", 6), TMV("v90", 39), TMV("v91", 39),
   TMV("v92", 39), TMV("v93", 40), TMV("v94", 40), TMV("v95", 40),
   TMV("v96", 40), TMV("v97", 40), TMV("v98", 40), TMC(20, 41),
   TMC(20, 43), TMC(20, 45), TMC(20, 47), TMC(20, 49), TMC(20, 51),
   TMC(20, 52), TMC(20, 54), TMC(20, 56), TMC(20, 58), TMC(20, 60),
   TMC(20, 62), TMC(20, 64), TMC(20, 66), TMC(20, 68), TMC(20, 70),
   TMC(20, 72), TMC(20, 74), TMC(20, 75), TMC(21, 79), TMC(21, 81),
   TMC(23, 83), TMC(24, 35), TMC(24, 83), TMC(24, 84), TMC(24, 86),
   TMC(24, 88), TMC(24, 89), TMC(25, 83), TMC(26, 91), TMC(27, 7),
   TMC(28, 15), TMC(29, 98), TMC(31, 100), TMC(32, 7), TMC(33, 7),
   TMC(34, 102), TMC(34, 104), TMC(35, 15), TMC(36, 15), TMC(37, 21),
   TMC(38, 6), TMC(39, 130), TMC(40, 82), TMC(41, 9), TMC(42, 5),
   TMC(43, 131), TMC(44, 132), TMC(45, 133), TMC(46, 2), TMC(47, 2),
   TMC(48, 138), TMC(49, 7), TMC(50, 139), TMC(51, 140), TMC(52, 15),
   TMC(53, 21), TMC(54, 143), TMC(55, 6), TMC(56, 90), TMC(57, 146),
   TMC(58, 7), TMC(59, 15), TMC(60, 11), TMC(61, 148), TMC(62, 22),
   TMC(63, 13), TMC(64, 20), TMC(65, 18), TMC(66, 149), TMC(67, 150),
   TMC(68, 152), TMC(69, 154), TMC(70, 148), TMC(71, 152), TMC(72, 156),
   TMC(73, 154), TMC(74, 157), TMC(74, 150), TMC(75, 148), TMC(76, 156),
   TMC(77, 156), TMC(78, 159), TMC(79, 147), TMC(80, 148), TMC(81, 13),
   TMC(82, 160), TMC(83, 11), TMC(84, 159), TMC(85, 161), TMC(86, 162),
   TMC(87, 149), TMC(88, 14), TMC(89, 13), TMC(90, 164), TMC(91, 8),
   TMC(92, 150), TMC(93, 15), TMC(94, 15), TMC(95, 13), TMC(96, 82)]
  end
  structure ThmBind = struct
    val DT = Thm.disk_thm
    val read = Term.read_raw tmvector
  end
  fun op authTestConductORP_primitive_def x = x
    val op authTestConductORP_primitive_def =
    ThmBind.DT(((("ssmConductORP",8),[]),[]),
               [ThmBind.read"%195%236@%231%200%7%230$0@|@2%9%8%213$0@%214%211@2%214%211@2%99%214%211@|@%100%214%211@|@%101%102%214%211@||@%103%104%214%211@||@%105%107%214%211@||@%108%109%214%211@||@%110%111%213$0@%214%211@2%214%211@2%11%222$2@%70%214%227@|@%71%72%214%211@||@%74%75%214%211@||@|@%30%214%211@|@%31%32%214%211@||@%33%34%214%211@||@%35%36%214%211@||@%37%38%214%211@||@%39%41%214%211@||@%42%43%214%211@||@%44%45%214%211@||@%46%47%48%214%211@|||@%49%50%214%211@||@%52%53%214%211@||@%54%55%214%211@||@%56%57%214%211@||@%58%59%214%211@||@%60%61%214%211@||@%64%65%214%211@||@||@%112%113%214%211@||@%114%115%214%211@||@%116%118%119%214%211@|||@%120%121%214%211@||@%122%123%214%211@||@%124%125%214%211@||@%126%127%214%211@||@%129%130%214%211@||@%131%132%214%211@||@%133%134%214%211@||@||@2"])
  fun op ssmConductORPStateInterp_def x = x
    val op ssmConductORPStateInterp_def =
    ThmBind.DT(((("ssmConductORP",11),[]),[]),
               [ThmBind.read"%188%23%193%266$0@2%229@|@"])
  fun op secContextConductORP_def x = x
    val op secContextConductORP_def =
    ThmBind.DT(((("ssmConductORP",13),[]),[]),
               [ThmBind.read"%183%19%186%21%187%15%196%263$2@$1@$0@2%207%240%217%220@2%257%225%224%218$2@6%207%240%217%221@2%257%225%224%219$1@6%207%250%262%217%220@2%257%225%224%219$1@6%257%216@3%207%250%262%217%221@2%257%225%224%218$2@6%257%216@3%215@5|@|@|@"])
  fun op conductORPNS_ind x = x
    val op conductORPNS_ind =
    ThmBind.DT(((("ssmConductORP",2),
                [("ConductORPType",[21,44,60,87]),
                 ("bool",[25,26,46,47,52,53,57,62,71,75,76,77,79]),
                 ("pair",[5,16]),("relation",[101,107]),
                 ("sat",[1,3,5,6,7,11,12,13,14,15]),
                 ("ssm11",[31])]),["DISK_THM"]),
               [ThmBind.read"%180%6%199%192$0%206@%249%218%264@4%192$0%206@%249%218%256@4%192$0%223@%249%219%234@4%192$0%223@%249%219%258@4%192$0%201@%249%218%270@4%192$0%201@%249%218%256@4%192$0%232@%249%218%237@4%192$0%232@%249%218%256@4%192%188%22%183%12$2$1@%267%218$0@3|@|@2%192%188%22%186%13$2$1@%267%219$0@3|@|@2%192%188%22%183%12$2$1@%241%218$0@3|@|@2%192%188%22%186%13$2$1@%241%219$0@3|@|@2%192$0%206@%249%218%270@4%192$0%206@%249%218%237@4%192%186%40$1%206@%249%219$0@3|@2%192%183%63$1%223@%249%218$0@3|@2%192$0%201@%249%218%264@4%192$0%201@%249%218%237@4%192%186%79$1%201@%249%219$0@3|@2%192$0%232@%249%218%264@4%192$0%232@%249%218%270@4%192%186%84$1%232@%249%219$0@3|@2%187%86$1%205@%249$0@2|@24%188%26%189%28$2$1@$0@|@|@2|@"])
  fun op conductORPNS_def x = x
    val op conductORPNS_def =
    ThmBind.DT(((("ssmConductORP",3),
                [("ConductORPType",[17,40,54,83]),("bool",[15,57]),
                 ("combin",[19]),("pair",[49]),("relation",[107,126]),
                 ("ssm11",[25]),("ssmConductORP",[0,1])]),["DISK_THM"]),
               [ThmBind.read"%192%198%238%206@%249%218%264@4%223@2%192%198%238%206@%249%218%256@4%206@2%192%198%238%223@%249%219%234@4%201@2%192%198%238%223@%249%219%258@4%223@2%192%198%238%201@%249%218%270@4%232@2%192%198%238%201@%249%218%256@4%201@2%192%198%238%232@%249%218%237@4%205@2%192%198%238%232@%249%218%256@4%232@2%192%198%238%22@%267%218%14@4%22@2%192%198%238%22@%267%219%13@4%22@2%192%198%238%22@%241%218%14@4%22@2%198%238%22@%241%219%13@4%22@12"])
  fun op conductORPOut_ind x = x
    val op conductORPOut_ind =
    ThmBind.DT(((("ssmConductORP",6),
                [("ConductORPType",[21,44,60,87]),
                 ("bool",[25,26,46,47,52,53,57,62,71,75,76,77,79]),
                 ("pair",[5,16]),("relation",[101,107]),
                 ("sat",[1,3,5,6,7,11,12,13,14,15]),
                 ("ssm11",[31])]),["DISK_THM"]),
               [ThmBind.read"%180%6%199%192$0%206@%249%218%264@4%192$0%206@%249%218%256@4%192$0%223@%249%219%234@4%192$0%223@%249%219%258@4%192$0%201@%249%218%270@4%192$0%201@%249%218%256@4%192$0%232@%249%218%237@4%192$0%232@%249%218%256@4%192%188%22%183%12$2$1@%267%218$0@3|@|@2%192%188%22%186%13$2$1@%267%219$0@3|@|@2%192%188%22%183%12$2$1@%241%218$0@3|@|@2%192%188%22%186%13$2$1@%241%219$0@3|@|@2%192$0%206@%249%218%270@4%192$0%206@%249%218%237@4%192%186%40$1%206@%249%219$0@3|@2%192%183%63$1%223@%249%218$0@3|@2%192$0%201@%249%218%264@4%192$0%201@%249%218%237@4%192%186%79$1%201@%249%219$0@3|@2%192$0%232@%249%218%264@4%192$0%232@%249%218%270@4%192%186%84$1%232@%249%219$0@3|@2%187%86$1%205@%249$0@2|@24%188%26%189%28$2$1@$0@|@|@2|@"])
  fun op conductORPOut_def x = x
    val op conductORPOut_def =
    ThmBind.DT(((("ssmConductORP",7),
                [("ConductORPType",[17,40,54,83]),("bool",[15,57]),
                 ("combin",[19]),("pair",[49]),("relation",[107,126]),
                 ("ssm11",[25]),("ssmConductORP",[4,5])]),["DISK_THM"]),
               [ThmBind.read"%192%197%239%206@%249%218%264@4%226@2%192%197%239%206@%249%218%256@4%210@2%192%197%239%223@%249%219%234@4%202@2%192%197%239%223@%249%219%258@4%226@2%192%197%239%201@%249%218%270@4%233@2%192%197%239%201@%249%218%256@4%202@2%192%197%239%232@%249%218%237@4%209@2%192%197%239%232@%249%218%256@4%233@2%192%197%239%22@%267%218%14@4%269@2%192%197%239%22@%267%219%13@4%269@2%192%197%239%22@%241%218%14@4%268@2%197%239%22@%241%219%13@4%268@12"])
  fun op authTestConductORP_ind x = x
    val op authTestConductORP_ind =
    ThmBind.DT(((("ssmConductORP",9),
                [("ConductORPType",[138]),("aclfoundation",[55,116]),
                 ("bool",[25,26,46,47,52,53,57,62,71,75,76,77,79]),
                 ("relation",[101,107]),
                 ("sat",[1,3,5,6,7,11,12,13,14,15])]),["DISK_THM"]),
               [ThmBind.read"%177%5%199%192%182%11$1%262%217%220@2%257$0@3|@2%192%182%11$1%262%217%221@2%257$0@3|@2%192$0%229@2%192$0%212@2%192%182%25$1%257$0@2|@2%192%171%27$1%254$0@2|@2%192%171%82%171%95$2%235$1@$0@2|@|@2%192%171%106%171%117$2%255$1@$0@2|@|@2%192%171%128%171%139$2%250$1@$0@2|@|@2%192%171%150%171%161$2%244$1@$0@2|@|@2%192%174%29$1%262$0@%229@2|@2%192%174%29$1%262$0@%212@2|@2%192%174%66%174%67%182%135$3%262%253$2@$1@2%257$0@3|@|@|@2%192%174%68%174%69%182%135$3%262%259$2@$1@2%257$0@3|@|@|@2%192%174%29%171%136$2%262$1@%254$0@3|@|@2%192%174%29%171%137%171%138$3%262$2@%235$1@$0@3|@|@|@2%192%174%29%171%140%171%141$3%262$2@%255$1@$0@3|@|@|@2%192%174%29%171%142%171%143$3%262$2@%250$1@$0@3|@|@|@2%192%174%29%171%144%171%145$3%262$2@%244$1@$0@3|@|@|@2%192%174%29%174%146%171%147$3%262$2@%262$1@$0@3|@|@|@2%192%174%29%174%148%174%149$3%262$2@%265$1@$0@3|@|@|@2%192%174%29%174%151%171%152$3%262$2@%240$1@$0@3|@|@|@2%192%174%29%174%153%174%154%171%155$4%262$3@%260$2@$1@$0@3|@|@|@|@2%192%174%29%172%156%172%157$3%262$2@%242$1@$0@3|@|@|@2%192%174%29%172%158%172%159$3%262$2@%245$1@$0@3|@|@|@2%192%174%29%175%160%175%162$3%262$2@%243$1@$0@3|@|@|@2%192%174%29%175%163%175%164$3%262$2@%247$1@$0@3|@|@|@2%192%174%29%181%165%181%166$3%262$2@%246$1@$0@3|@|@|@2%192%174%29%181%167%181%168$3%262$2@%252$1@$0@3|@|@|@2%192%174%29%181%169%181%170$3%262$2@%251$1@$0@3|@|@|@2%192%174%51%174%62$2%265$1@$0@2|@|@2%192%174%73%171%76$2%240$1@$0@2|@|@2%192%174%77%174%78%171%80$3%260$2@$1@$0@2|@|@|@2%192%172%81%172%83$2%242$1@$0@2|@|@2%192%172%85%172%87$2%245$1@$0@2|@|@2%192%175%88%175%89$2%243$1@$0@2|@|@2%192%175%90%175%91$2%247$1@$0@2|@|@2%192%181%92%181%93$2%246$1@$0@2|@|@2%192%181%94%181%96$2%252$1@$0@2|@|@2%181%97%181%98$2%251$1@$0@2|@|@41%171%24$1$0@|@2|@"])
  fun op authTestConductORP_def x = x
    val op authTestConductORP_def =
    ThmBind.DT(((("ssmConductORP",10),
                [("aclfoundation",[33,110]),("bool",[15]),("combin",[19]),
                 ("relation",[107,126]),
                 ("ssmConductORP",[8])]),["DISK_THM"]),
               [ThmBind.read"%192%194%236%262%217%220@2%257%11@4%227@2%192%194%236%262%217%221@2%257%11@4%227@2%192%194%236%229@2%211@2%192%194%236%212@2%211@2%192%194%236%257%25@3%211@2%192%194%236%254%27@3%211@2%192%194%236%235%82@%95@3%211@2%192%194%236%255%106@%117@3%211@2%192%194%236%250%128@%139@3%211@2%192%194%236%244%150@%161@3%211@2%192%194%236%262%29@%229@3%211@2%192%194%236%262%29@%212@3%211@2%192%194%236%262%253%66@%67@2%257%135@4%211@2%192%194%236%262%259%68@%69@2%257%135@4%211@2%192%194%236%262%29@%254%136@4%211@2%192%194%236%262%29@%235%137@%138@4%211@2%192%194%236%262%29@%255%140@%141@4%211@2%192%194%236%262%29@%250%142@%143@4%211@2%192%194%236%262%29@%244%144@%145@4%211@2%192%194%236%262%29@%262%146@%147@4%211@2%192%194%236%262%29@%265%148@%149@4%211@2%192%194%236%262%29@%240%151@%152@4%211@2%192%194%236%262%29@%260%153@%154@%155@4%211@2%192%194%236%262%29@%242%156@%157@4%211@2%192%194%236%262%29@%245%158@%159@4%211@2%192%194%236%262%29@%243%160@%162@4%211@2%192%194%236%262%29@%247%163@%164@4%211@2%192%194%236%262%29@%246%165@%166@4%211@2%192%194%236%262%29@%252%167@%168@4%211@2%192%194%236%262%29@%251%169@%170@4%211@2%192%194%236%265%51@%62@3%211@2%192%194%236%240%73@%76@3%211@2%192%194%236%260%77@%78@%80@3%211@2%192%194%236%242%81@%83@3%211@2%192%194%236%245%85@%87@3%211@2%192%194%236%243%88@%89@3%211@2%192%194%236%247%90@%91@3%211@2%192%194%236%246%92@%93@3%211@2%192%194%236%252%94@%96@3%211@2%194%236%251%97@%98@3%211@40"])
  fun op authTestConductORP_cmd_reject_lemma x = x
    val op authTestConductORP_cmd_reject_lemma =
    ThmBind.DT(((("ssmConductORP",12),
                [("aclfoundation",[33,110]),
                 ("bool",[15,25,26,46,47,52,53,62,70,72]),("combin",[19]),
                 ("relation",[107,126]),("sat",[1,3,5,6,7,11,14,15]),
                 ("ssmConductORP",[8])]),["DISK_THM"]),
               [ThmBind.read"%176%10%271%236%257%225$0@4|@"])
  fun op PlatoonLeader_plCommand_lemma x = x
    val op PlatoonLeader_plCommand_lemma =
    ThmBind.DT(((("ssmConductORP",14),
                [("aclDrules",[3]),("aclrules",[63]),
                 ("bool",[25,26,46,47,50,52,53,62,92,93,95]),
                 ("sat",[1,3,5,6,7,11,12,13,14,15]),("satList",[1,3]),
                 ("ssm11",[52]),("ssmConductORP",[11,13])]),["DISK_THM"]),
               [ThmBind.read"%199%204%190%0@%191%2@%3@3%203%236@%266@%263%18@%20@%15@2%207%262%217%220@2%257%225%224%218%18@6%16@2%22@%17@3%261%190%0@%191%2@%3@3%257%225%224%218%18@6"])
  fun op PlatoonLeader_exec_plCommand_justified_thm x = x
    val op PlatoonLeader_exec_plCommand_justified_thm =
    ThmBind.DT(((("ssmConductORP",15),
                [("aclDrules",[3]),("aclrules",[63]),
                 ("bool",
                 [25,26,35,42,46,47,50,52,53,55,57,62,70,76,83,92,93,95,
                  145]),("combin",[19]),("sat",[1,3,5,6,7,11,12,13,14,15]),
                 ("satList",[1,3]),("ssm11",[52,62]),
                 ("ssmConductORP",[11,13])]),["DISK_THM"]),
               [ThmBind.read"%179%1%178%4%173%0%184%2%185%3%194%228%190$2@%191$1@$0@3%248%224%218%18@4%203%236@%266@%263%18@%20@%15@2%207%262%217%220@2%257%225%224%218%18@6%16@2%22@%17@2%203%236@%266@%263%18@%20@%15@2%16@$4%22@%248%224%218%18@5%208$3%22@%248%224%218%18@5%17@4%192%236%262%217%220@2%257%225%224%218%18@7%192%204%190$2@%191$1@$0@3%203%236@%266@%263%18@%20@%15@2%207%262%217%220@2%257%225%224%218%18@6%16@2%22@%17@3%261%190$2@%191$1@$0@3%257%225%224%218%18@8|@|@|@|@|@"])
  fun op PlatoonSergeant_psgCommand_lemma x = x
    val op PlatoonSergeant_psgCommand_lemma =
    ThmBind.DT(((("ssmConductORP",16),
                [("aclDrules",[3]),("aclrules",[63]),
                 ("bool",[25,26,46,47,50,52,53,62,92,93,95]),
                 ("sat",[1,3,5,6,7,11,12,13,14,15]),("satList",[1,3]),
                 ("ssm11",[52]),("ssmConductORP",[11,13])]),["DISK_THM"]),
               [ThmBind.read"%199%204%190%0@%191%2@%3@3%203%236@%266@%263%18@%20@%15@2%207%262%217%221@2%257%225%224%219%20@6%16@2%22@%17@3%261%190%0@%191%2@%3@3%257%225%224%219%20@6"])
  fun op PlatoonSergeant_exec_psgCommand_justified_thm x = x
    val op PlatoonSergeant_exec_psgCommand_justified_thm =
    ThmBind.DT(((("ssmConductORP",17),
                [("aclDrules",[3]),("aclrules",[63]),
                 ("bool",
                 [25,26,35,42,46,47,50,52,53,55,57,62,70,76,83,92,93,95,
                  145]),("combin",[19]),("sat",[1,3,5,6,7,11,12,13,14,15]),
                 ("satList",[1,3]),("ssm11",[52,62]),
                 ("ssmConductORP",[11,13])]),["DISK_THM"]),
               [ThmBind.read"%179%1%178%4%173%0%184%2%185%3%194%228%190$2@%191$1@$0@3%248%224%219%20@4%203%236@%266@%263%18@%20@%15@2%207%262%217%221@2%257%225%224%219%20@6%16@2%22@%17@2%203%236@%266@%263%18@%20@%15@2%16@$4%22@%248%224%219%20@5%208$3%22@%248%224%219%20@5%17@4%192%236%262%217%221@2%257%225%224%219%20@7%192%204%190$2@%191$1@$0@3%203%236@%266@%263%18@%20@%15@2%207%262%217%221@2%257%225%224%219%20@6%16@2%22@%17@3%261%190$2@%191$1@$0@3%257%225%224%219%20@8|@|@|@|@|@"])

  val _ = DB.bindl "ssmConductORP"
  [("authTestConductORP_primitive_def",
    authTestConductORP_primitive_def,
    DB.Def),
   ("ssmConductORPStateInterp_def",ssmConductORPStateInterp_def,DB.Def),
   ("secContextConductORP_def",secContextConductORP_def,DB.Def),
   ("conductORPNS_ind",conductORPNS_ind,DB.Thm),
   ("conductORPNS_def",conductORPNS_def,DB.Thm),
   ("conductORPOut_ind",conductORPOut_ind,DB.Thm),
   ("conductORPOut_def",conductORPOut_def,DB.Thm),
   ("authTestConductORP_ind",authTestConductORP_ind,DB.Thm),
   ("authTestConductORP_def",authTestConductORP_def,DB.Thm),
   ("authTestConductORP_cmd_reject_lemma",
    authTestConductORP_cmd_reject_lemma,
    DB.Thm),
   ("PlatoonLeader_plCommand_lemma",PlatoonLeader_plCommand_lemma,DB.Thm),
   ("PlatoonLeader_exec_plCommand_justified_thm",
    PlatoonLeader_exec_plCommand_justified_thm,
    DB.Thm),
   ("PlatoonSergeant_psgCommand_lemma",
    PlatoonSergeant_psgCommand_lemma,
    DB.Thm),
   ("PlatoonSergeant_exec_psgCommand_justified_thm",
    PlatoonSergeant_exec_psgCommand_justified_thm,
    DB.Thm)]

  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "ssmConductORP",
    thydataty = "compute",
    read = ThmBind.read,
    data =
        "ssmConductORP.conductORPNS_def ssmConductORP.conductORPOut_def ssmConductORP.secContextConductORP_def ssmConductORP.ssmConductORPStateInterp_def ssmConductORP.authTestConductORP_def"
  }
  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "ssmConductORP",
    thydataty = "TermGrammarDeltas",
    read = ThmBind.read,
    data =
        "OO12.conductORPNS4.%238OO13.conductORPOut4.%239OO18.authTestConductORP4.%236OO24.ssmConductORPStateInterp4.%266OO20.secContextConductORP4.%263"
  }
  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val ssmConductORP_grammars = merge_grammars ["ConductORPType", "ssm11",
                                               "OMNIType"]
  local
  val (tyUDs, tmUDs) = GrammarDeltas.thy_deltas{thyname="ssmConductORP"}
  val addtmUDs = term_grammar.add_deltas tmUDs
  val addtyUDs = type_grammar.apply_deltas tyUDs
  in
  val ssmConductORP_grammars = 
    Portable.## (addtyUDs,addtmUDs) ssmConductORP_grammars
  val _ = Parse.grammarDB_insert("ssmConductORP",ssmConductORP_grammars)
  val _ = Parse.temp_set_grammars (addtyUDs (Parse.type_grammar()), addtmUDs (Parse.term_grammar()))
  end (* addUDs local *)
  end

val _ = if !Globals.print_thy_loads then print "done\n" else ()
val _ = Theory.load_complete "ssmConductORP"
end
