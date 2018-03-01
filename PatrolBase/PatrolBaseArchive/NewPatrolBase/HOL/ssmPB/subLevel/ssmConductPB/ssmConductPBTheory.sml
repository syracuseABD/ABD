structure ssmConductPBTheory :> ssmConductPBTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading ssmConductPBTheory ... " else ()
  open Type Term Thm
  infixr -->

  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  (*  Parents *)
  local open ConductPBTypeTheory OMNITypeTheory ssm11Theory
  in end;
  val _ = Theory.link_parents
          ("ssmConductPB",
          Arbnum.fromString "1500771745",
          Arbnum.fromString "469302")
          [("ConductPBType",
           Arbnum.fromString "1500771743",
           Arbnum.fromString "102237"),
           ("ssm11",
           Arbnum.fromString "1499652452",
           Arbnum.fromString "890464"),
           ("OMNIType",
           Arbnum.fromString "1499574745",
           Arbnum.fromString "168021")];
  val _ = Theory.incorporate_types "ssmConductPB" [];

  val idvector = 
    let fun ID(thy,oth) = {Thy = thy, Other = oth}
    in Vector.fromList
  [ID("min", "fun"), ID("aclfoundation", "Form"),
   ID("ConductPBType", "stateRole"), ID("ssm11", "order"),
   ID("OMNIType", "command"), ID("ConductPBType", "slCommand"),
   ID("ConductPBType", "slState"), ID("list", "list"),
   ID("ConductPBType", "psgCommandPB"), ID("ConductPBType", "plCommandPB"),
   ID("ConductPBType", "slOutput"), ID("ssm11", "trType"),
   ID("min", "bool"), ID("aclfoundation", "Kripke"),
   ID("aclfoundation", "po"), ID("OMNIType", "output"),
   ID("aclfoundation", "Princ"), ID("aclfoundation", "IntLevel"),
   ID("aclfoundation", "SecLevel"), ID("num", "num"), ID("bool", "!"),
   ID("pair", ","), ID("pair", "prod"), ID("bool", "/\\"), ID("min", "="),
   ID("min", "==>"), ID("min", "@"), ID("ConductPBType", "ACTIONS_IN_PB"),
   ID("ConductPBType", "ActionsInPB"), ID("ssm11", "CFG"),
   ID("ssm11", "configuration"), ID("ssm11", "CFGInterpret"),
   ID("ConductPBType", "COMPLETE_PB"), ID("ConductPBType", "CONDUCT_PB"),
   ID("list", "CONS"), ID("ConductPBType", "ConductPB"), ID("bool", "F"),
   ID("aclfoundation", "FF"), ID("aclfoundation", "Form_CASE"),
   ID("combin", "I"), ID("list", "NIL"), ID("ssm11", "NONE"),
   ID("aclfoundation", "Name"), ID("ConductPBType", "PL"),
   ID("ConductPBType", "PSG"), ID("ConductPBType", "PlatoonLeader"),
   ID("ConductPBType", "PlatoonSergeant"),
   ID("aclfoundation", "Princ_CASE"), ID("ConductPBType", "SECURE_PB"),
   ID("OMNIType", "SLc"), ID("ssm11", "SOME"),
   ID("ConductPBType", "SecurePB"), ID("bool", "T"), ID("ssm11", "TR"),
   ID("aclfoundation", "TT"), ID("relation", "WF"),
   ID("relation", "WFREC"), ID("ConductPBType", "WITHDRAW_PB"),
   ID("ConductPBType", "WithdrawPB"), ID("ConductPBType", "actionsInPB"),
   ID("aclfoundation", "andf"), ID("ssmConductPB", "authTestConductPB"),
   ID("ConductPBType", "completePB"), ID("ssmConductPB", "conductPBNS"),
   ID("ssmConductPB", "conductPBOut"), ID("aclfoundation", "controls"),
   ID("ssm11", "discard"), ID("aclfoundation", "domi"),
   ID("aclfoundation", "doms"), ID("aclfoundation", "eqf"),
   ID("aclfoundation", "eqi"), ID("aclfoundation", "eqn"),
   ID("aclfoundation", "eqs"), ID("ssm11", "exec"),
   ID("aclfoundation", "impf"), ID("aclfoundation", "lt"),
   ID("aclfoundation", "lte"), ID("aclfoundation", "meet"),
   ID("aclfoundation", "notf"), ID("aclfoundation", "orf"),
   ID("ConductPBType", "plIncompletePB"), ID("aclfoundation", "prop"),
   ID("ConductPBType", "psgIncompletePB"), ID("aclfoundation", "quoting"),
   ID("aclfoundation", "reps"), ID("aclrules", "sat"),
   ID("aclfoundation", "says"), ID("ssmConductPB", "secContextConductPB"),
   ID("ConductPBType", "securePB"), ID("aclfoundation", "speaks_for"),
   ID("ssmConductPB", "ssmConductPBStateInterp"), ID("ssm11", "trap"),
   ID("ConductPBType", "unAuthenticated"),
   ID("ConductPBType", "unAuthorized"), ID("ConductPBType", "withdrawPB"),
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
  val _ = Theory.incorporate_consts "ssmConductPB" tyvector
     [("ssmConductPBStateInterp", 8), ("secContextConductPB", 14),
      ("conductPBOut", 18), ("conductPBNS", 20),
      ("authTestConductPB", 22)];

  local open SharingTables
  in
  val tmvector = build_term_vector idvector tyvector
  [TMV("M", 24), TMV("NS", 27), TMV("Oi", 28), TMV("Os", 29),
   TMV("Out", 32), TMV("P", 22), TMV("P", 34), TMV("R", 35), TMV("a", 6),
   TMV("authTestConductPB", 22), TMV("cmd", 4), TMV("cmd", 5),
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
   TMC(34, 102), TMC(34, 104), TMC(35, 15), TMC(36, 21), TMC(37, 6),
   TMC(38, 130), TMC(39, 82), TMC(40, 9), TMC(41, 5), TMC(42, 131),
   TMC(43, 132), TMC(44, 133), TMC(45, 2), TMC(46, 2), TMC(47, 138),
   TMC(48, 7), TMC(49, 139), TMC(50, 140), TMC(51, 15), TMC(52, 21),
   TMC(53, 143), TMC(54, 6), TMC(55, 90), TMC(56, 146), TMC(57, 7),
   TMC(58, 15), TMC(59, 11), TMC(60, 148), TMC(61, 22), TMC(62, 13),
   TMC(63, 20), TMC(64, 18), TMC(65, 149), TMC(66, 150), TMC(67, 152),
   TMC(68, 154), TMC(69, 148), TMC(70, 152), TMC(71, 156), TMC(72, 154),
   TMC(73, 157), TMC(73, 150), TMC(74, 148), TMC(75, 156), TMC(76, 156),
   TMC(77, 159), TMC(78, 147), TMC(79, 148), TMC(80, 13), TMC(81, 160),
   TMC(82, 11), TMC(83, 159), TMC(84, 161), TMC(85, 162), TMC(86, 149),
   TMC(87, 14), TMC(88, 13), TMC(89, 164), TMC(90, 8), TMC(91, 150),
   TMC(92, 15), TMC(93, 15), TMC(94, 13), TMC(95, 82)]
  end
  structure ThmBind = struct
    val DT = Thm.disk_thm
    val read = Term.read_raw tmvector
  end
  fun op authTestConductPB_primitive_def x = x
    val op authTestConductPB_primitive_def =
    ThmBind.DT(((("ssmConductPB",8),[]),[]),
               [ThmBind.read"%195%235@%230%200%7%229$0@|@2%9%8%212$0@%213%210@2%213%210@2%99%213%210@|@%100%213%210@|@%101%102%213%210@||@%103%104%213%210@||@%105%107%213%210@||@%108%109%213%210@||@%110%111%212$0@%213%210@2%213%210@2%11%221$2@%70%213%226@|@%71%72%213%210@||@%74%75%213%210@||@|@%30%213%210@|@%31%32%213%210@||@%33%34%213%210@||@%35%36%213%210@||@%37%38%213%210@||@%39%41%213%210@||@%42%43%213%210@||@%44%45%213%210@||@%46%47%48%213%210@|||@%49%50%213%210@||@%52%53%213%210@||@%54%55%213%210@||@%56%57%213%210@||@%58%59%213%210@||@%60%61%213%210@||@%64%65%213%210@||@||@%112%113%213%210@||@%114%115%213%210@||@%116%118%119%213%210@|||@%120%121%213%210@||@%122%123%213%210@||@%124%125%213%210@||@%126%127%213%210@||@%129%130%213%210@||@%131%132%213%210@||@%133%134%213%210@||@||@2"])
  fun op ssmConductPBStateInterp_def x = x
    val op ssmConductPBStateInterp_def =
    ThmBind.DT(((("ssmConductPB",11),[]),[]),
               [ThmBind.read"%188%23%193%265$0@2%228@|@"])
  fun op secContextConductPB_def x = x
    val op secContextConductPB_def =
    ThmBind.DT(((("ssmConductPB",13),[]),[]),
               [ThmBind.read"%183%19%186%21%187%15%196%262$2@$1@$0@2%207%239%216%219@2%256%224%223%217$2@6%207%239%216%220@2%256%224%223%218$1@6%207%249%261%216%219@2%256%224%223%218$1@6%256%215@3%207%249%261%216%220@2%256%224%223%217$2@6%256%215@3%214@5|@|@|@"])
  fun op conductPBNS_ind x = x
    val op conductPBNS_ind =
    ThmBind.DT(((("ssmConductPB",2),
                [("ConductPBType",[21,44,60,87]),
                 ("bool",[25,26,46,47,52,53,57,62,71,75,76,77,79]),
                 ("pair",[5,16]),("relation",[101,107]),
                 ("sat",[1,3,5,6,7,11,12,13,14,15]),
                 ("ssm11",[31])]),["DISK_THM"]),
               [ThmBind.read"%180%6%199%192$0%206@%248%217%263@4%192$0%206@%248%217%255@4%192$0%222@%248%218%233@4%192$0%222@%248%218%257@4%192$0%201@%248%217%269@4%192$0%201@%248%217%255@4%192$0%231@%248%217%236@4%192$0%231@%248%217%255@4%192%188%22%183%12$2$1@%266%217$0@3|@|@2%192%188%22%186%13$2$1@%266%218$0@3|@|@2%192%188%22%183%12$2$1@%240%217$0@3|@|@2%192%188%22%186%13$2$1@%240%218$0@3|@|@2%192$0%206@%248%217%269@4%192$0%206@%248%217%236@4%192%186%40$1%206@%248%218$0@3|@2%192%183%63$1%222@%248%217$0@3|@2%192$0%201@%248%217%263@4%192$0%201@%248%217%236@4%192%186%79$1%201@%248%218$0@3|@2%192$0%231@%248%217%263@4%192$0%231@%248%217%269@4%192%186%84$1%231@%248%218$0@3|@2%187%86$1%205@%248$0@2|@24%188%26%189%28$2$1@$0@|@|@2|@"])
  fun op conductPBNS_def x = x
    val op conductPBNS_def =
    ThmBind.DT(((("ssmConductPB",3),
                [("ConductPBType",[17,40,54,83]),("bool",[15,57]),
                 ("combin",[19]),("pair",[49]),("relation",[107,126]),
                 ("ssm11",[25]),("ssmConductPB",[0,1])]),["DISK_THM"]),
               [ThmBind.read"%192%198%237%206@%248%217%263@4%222@2%192%198%237%206@%248%217%255@4%206@2%192%198%237%222@%248%218%233@4%201@2%192%198%237%222@%248%218%257@4%222@2%192%198%237%201@%248%217%269@4%231@2%192%198%237%201@%248%217%255@4%201@2%192%198%237%231@%248%217%236@4%205@2%192%198%237%231@%248%217%255@4%231@2%192%198%237%22@%266%217%14@4%22@2%192%198%237%22@%266%218%13@4%22@2%192%198%237%22@%240%217%14@4%22@2%198%237%22@%240%218%13@4%22@12"])
  fun op conductPBOut_ind x = x
    val op conductPBOut_ind =
    ThmBind.DT(((("ssmConductPB",6),
                [("ConductPBType",[21,44,60,87]),
                 ("bool",[25,26,46,47,52,53,57,62,71,75,76,77,79]),
                 ("pair",[5,16]),("relation",[101,107]),
                 ("sat",[1,3,5,6,7,11,12,13,14,15]),
                 ("ssm11",[31])]),["DISK_THM"]),
               [ThmBind.read"%180%6%199%192$0%206@%248%217%263@4%192$0%206@%248%217%255@4%192$0%222@%248%218%233@4%192$0%222@%248%218%257@4%192$0%201@%248%217%269@4%192$0%201@%248%217%255@4%192$0%231@%248%217%236@4%192$0%231@%248%217%255@4%192%188%22%183%12$2$1@%266%217$0@3|@|@2%192%188%22%186%13$2$1@%266%218$0@3|@|@2%192%188%22%183%12$2$1@%240%217$0@3|@|@2%192%188%22%186%13$2$1@%240%218$0@3|@|@2%192$0%206@%248%217%269@4%192$0%206@%248%217%236@4%192%186%40$1%206@%248%218$0@3|@2%192%183%63$1%222@%248%217$0@3|@2%192$0%201@%248%217%263@4%192$0%201@%248%217%236@4%192%186%79$1%201@%248%218$0@3|@2%192$0%231@%248%217%263@4%192$0%231@%248%217%269@4%192%186%84$1%231@%248%218$0@3|@2%187%86$1%205@%248$0@2|@24%188%26%189%28$2$1@$0@|@|@2|@"])
  fun op conductPBOut_def x = x
    val op conductPBOut_def =
    ThmBind.DT(((("ssmConductPB",7),
                [("ConductPBType",[17,54,83]),("bool",[15,57]),
                 ("combin",[19]),("pair",[49]),("relation",[107,126]),
                 ("ssm11",[25]),("ssmConductPB",[4,5])]),["DISK_THM"]),
               [ThmBind.read"%192%197%238%206@%248%217%263@4%209@2%192%197%238%206@%248%217%255@4%209@2%192%197%238%222@%248%218%233@4%225@2%192%197%238%222@%248%218%257@4%225@2%192%197%238%201@%248%217%269@4%202@2%192%197%238%201@%248%217%255@4%202@2%192%197%238%231@%248%217%236@4%232@2%192%197%238%231@%248%217%255@4%232@2%192%197%238%22@%266%217%14@4%268@2%192%197%238%22@%266%218%13@4%268@2%192%197%238%22@%240%217%14@4%267@2%197%238%22@%240%218%13@4%267@12"])
  fun op authTestConductPB_ind x = x
    val op authTestConductPB_ind =
    ThmBind.DT(((("ssmConductPB",9),
                [("ConductPBType",[138]),("aclfoundation",[55,116]),
                 ("bool",[25,26,46,47,52,53,57,62,71,75,76,77,79]),
                 ("relation",[101,107]),
                 ("sat",[1,3,5,6,7,11,12,13,14,15])]),["DISK_THM"]),
               [ThmBind.read"%177%5%199%192%182%11$1%261%216%219@2%256$0@3|@2%192%182%11$1%261%216%220@2%256$0@3|@2%192$0%228@2%192$0%211@2%192%182%25$1%256$0@2|@2%192%171%27$1%253$0@2|@2%192%171%82%171%95$2%234$1@$0@2|@|@2%192%171%106%171%117$2%254$1@$0@2|@|@2%192%171%128%171%139$2%249$1@$0@2|@|@2%192%171%150%171%161$2%243$1@$0@2|@|@2%192%174%29$1%261$0@%228@2|@2%192%174%29$1%261$0@%211@2|@2%192%174%66%174%67%182%135$3%261%252$2@$1@2%256$0@3|@|@|@2%192%174%68%174%69%182%135$3%261%258$2@$1@2%256$0@3|@|@|@2%192%174%29%171%136$2%261$1@%253$0@3|@|@2%192%174%29%171%137%171%138$3%261$2@%234$1@$0@3|@|@|@2%192%174%29%171%140%171%141$3%261$2@%254$1@$0@3|@|@|@2%192%174%29%171%142%171%143$3%261$2@%249$1@$0@3|@|@|@2%192%174%29%171%144%171%145$3%261$2@%243$1@$0@3|@|@|@2%192%174%29%174%146%171%147$3%261$2@%261$1@$0@3|@|@|@2%192%174%29%174%148%174%149$3%261$2@%264$1@$0@3|@|@|@2%192%174%29%174%151%171%152$3%261$2@%239$1@$0@3|@|@|@2%192%174%29%174%153%174%154%171%155$4%261$3@%259$2@$1@$0@3|@|@|@|@2%192%174%29%172%156%172%157$3%261$2@%241$1@$0@3|@|@|@2%192%174%29%172%158%172%159$3%261$2@%244$1@$0@3|@|@|@2%192%174%29%175%160%175%162$3%261$2@%242$1@$0@3|@|@|@2%192%174%29%175%163%175%164$3%261$2@%246$1@$0@3|@|@|@2%192%174%29%181%165%181%166$3%261$2@%245$1@$0@3|@|@|@2%192%174%29%181%167%181%168$3%261$2@%251$1@$0@3|@|@|@2%192%174%29%181%169%181%170$3%261$2@%250$1@$0@3|@|@|@2%192%174%51%174%62$2%264$1@$0@2|@|@2%192%174%73%171%76$2%239$1@$0@2|@|@2%192%174%77%174%78%171%80$3%259$2@$1@$0@2|@|@|@2%192%172%81%172%83$2%241$1@$0@2|@|@2%192%172%85%172%87$2%244$1@$0@2|@|@2%192%175%88%175%89$2%242$1@$0@2|@|@2%192%175%90%175%91$2%246$1@$0@2|@|@2%192%181%92%181%93$2%245$1@$0@2|@|@2%192%181%94%181%96$2%251$1@$0@2|@|@2%181%97%181%98$2%250$1@$0@2|@|@41%171%24$1$0@|@2|@"])
  fun op authTestConductPB_def x = x
    val op authTestConductPB_def =
    ThmBind.DT(((("ssmConductPB",10),
                [("aclfoundation",[33,110]),("bool",[15]),("combin",[19]),
                 ("relation",[107,126]),
                 ("ssmConductPB",[8])]),["DISK_THM"]),
               [ThmBind.read"%192%194%235%261%216%219@2%256%11@4%226@2%192%194%235%261%216%220@2%256%11@4%226@2%192%194%235%228@2%210@2%192%194%235%211@2%210@2%192%194%235%256%25@3%210@2%192%194%235%253%27@3%210@2%192%194%235%234%82@%95@3%210@2%192%194%235%254%106@%117@3%210@2%192%194%235%249%128@%139@3%210@2%192%194%235%243%150@%161@3%210@2%192%194%235%261%29@%228@3%210@2%192%194%235%261%29@%211@3%210@2%192%194%235%261%252%66@%67@2%256%135@4%210@2%192%194%235%261%258%68@%69@2%256%135@4%210@2%192%194%235%261%29@%253%136@4%210@2%192%194%235%261%29@%234%137@%138@4%210@2%192%194%235%261%29@%254%140@%141@4%210@2%192%194%235%261%29@%249%142@%143@4%210@2%192%194%235%261%29@%243%144@%145@4%210@2%192%194%235%261%29@%261%146@%147@4%210@2%192%194%235%261%29@%264%148@%149@4%210@2%192%194%235%261%29@%239%151@%152@4%210@2%192%194%235%261%29@%259%153@%154@%155@4%210@2%192%194%235%261%29@%241%156@%157@4%210@2%192%194%235%261%29@%244%158@%159@4%210@2%192%194%235%261%29@%242%160@%162@4%210@2%192%194%235%261%29@%246%163@%164@4%210@2%192%194%235%261%29@%245%165@%166@4%210@2%192%194%235%261%29@%251%167@%168@4%210@2%192%194%235%261%29@%250%169@%170@4%210@2%192%194%235%264%51@%62@3%210@2%192%194%235%239%73@%76@3%210@2%192%194%235%259%77@%78@%80@3%210@2%192%194%235%241%81@%83@3%210@2%192%194%235%244%85@%87@3%210@2%192%194%235%242%88@%89@3%210@2%192%194%235%246%90@%91@3%210@2%192%194%235%245%92@%93@3%210@2%192%194%235%251%94@%96@3%210@2%194%235%250%97@%98@3%210@40"])
  fun op authTestConductPB_cmd_reject_lemma x = x
    val op authTestConductPB_cmd_reject_lemma =
    ThmBind.DT(((("ssmConductPB",12),
                [("aclfoundation",[33,110]),
                 ("bool",[15,25,26,46,47,52,53,62,70,72]),("combin",[19]),
                 ("relation",[107,126]),("sat",[1,3,5,6,7,11,14,15]),
                 ("ssmConductPB",[8])]),["DISK_THM"]),
               [ThmBind.read"%176%10%270%235%256%224$0@4|@"])
  fun op PlatoonLeader_plCommandPB_lemma x = x
    val op PlatoonLeader_plCommandPB_lemma =
    ThmBind.DT(((("ssmConductPB",14),
                [("aclDrules",[3]),("aclrules",[63]),
                 ("bool",[25,26,46,47,50,52,53,62,92,93,95]),
                 ("sat",[1,3,5,6,7,11,12,13,14,15]),("satList",[1,3]),
                 ("ssm11",[52]),("ssmConductPB",[11,13])]),["DISK_THM"]),
               [ThmBind.read"%199%204%190%0@%191%2@%3@3%203%235@%265@%262%18@%20@%15@2%207%261%216%219@2%256%224%223%217%18@6%16@2%22@%17@3%260%190%0@%191%2@%3@3%256%224%223%217%18@6"])
  fun op PlatoonLeader_exec_plCommandPB_justified_thm x = x
    val op PlatoonLeader_exec_plCommandPB_justified_thm =
    ThmBind.DT(((("ssmConductPB",15),
                [("aclDrules",[3]),("aclrules",[63]),
                 ("bool",
                 [25,26,35,42,46,47,50,52,53,55,57,62,70,76,83,92,93,95,
                  145]),("combin",[19]),("sat",[1,3,5,6,7,11,12,13,14,15]),
                 ("satList",[1,3]),("ssm11",[52,62]),
                 ("ssmConductPB",[11,13])]),["DISK_THM"]),
               [ThmBind.read"%179%1%178%4%173%0%184%2%185%3%194%227%190$2@%191$1@$0@3%247%223%217%18@4%203%235@%265@%262%18@%20@%15@2%207%261%216%219@2%256%224%223%217%18@6%16@2%22@%17@2%203%235@%265@%262%18@%20@%15@2%16@$4%22@%247%223%217%18@5%208$3%22@%247%223%217%18@5%17@4%192%235%261%216%219@2%256%224%223%217%18@7%192%204%190$2@%191$1@$0@3%203%235@%265@%262%18@%20@%15@2%207%261%216%219@2%256%224%223%217%18@6%16@2%22@%17@3%260%190$2@%191$1@$0@3%256%224%223%217%18@8|@|@|@|@|@"])
  fun op PlatoonSergeant_psgCommandPB_lemma x = x
    val op PlatoonSergeant_psgCommandPB_lemma =
    ThmBind.DT(((("ssmConductPB",16),
                [("aclDrules",[3]),("aclrules",[63]),
                 ("bool",[25,26,46,47,50,52,53,62,92,93,95]),
                 ("sat",[1,3,5,6,7,11,12,13,14,15]),("satList",[1,3]),
                 ("ssm11",[52]),("ssmConductPB",[11,13])]),["DISK_THM"]),
               [ThmBind.read"%199%204%190%0@%191%2@%3@3%203%235@%265@%262%18@%20@%15@2%207%261%216%220@2%256%224%223%218%20@6%16@2%22@%17@3%260%190%0@%191%2@%3@3%256%224%223%218%20@6"])
  fun op PlatoonSergeant_exec_psgCommandPB_justified_thm x = x
    val op PlatoonSergeant_exec_psgCommandPB_justified_thm =
    ThmBind.DT(((("ssmConductPB",17),
                [("aclDrules",[3]),("aclrules",[63]),
                 ("bool",
                 [25,26,35,42,46,47,50,52,53,55,57,62,70,76,83,92,93,95,
                  145]),("combin",[19]),("sat",[1,3,5,6,7,11,12,13,14,15]),
                 ("satList",[1,3]),("ssm11",[52,62]),
                 ("ssmConductPB",[11,13])]),["DISK_THM"]),
               [ThmBind.read"%179%1%178%4%173%0%184%2%185%3%194%227%190$2@%191$1@$0@3%247%223%218%20@4%203%235@%265@%262%18@%20@%15@2%207%261%216%220@2%256%224%223%218%20@6%16@2%22@%17@2%203%235@%265@%262%18@%20@%15@2%16@$4%22@%247%223%218%20@5%208$3%22@%247%223%218%20@5%17@4%192%235%261%216%220@2%256%224%223%218%20@7%192%204%190$2@%191$1@$0@3%203%235@%265@%262%18@%20@%15@2%207%261%216%220@2%256%224%223%218%20@6%16@2%22@%17@3%260%190$2@%191$1@$0@3%256%224%223%218%20@8|@|@|@|@|@"])

  val _ = DB.bindl "ssmConductPB"
  [("authTestConductPB_primitive_def",
    authTestConductPB_primitive_def,
    DB.Def),
   ("ssmConductPBStateInterp_def",ssmConductPBStateInterp_def,DB.Def),
   ("secContextConductPB_def",secContextConductPB_def,DB.Def),
   ("conductPBNS_ind",conductPBNS_ind,DB.Thm),
   ("conductPBNS_def",conductPBNS_def,DB.Thm),
   ("conductPBOut_ind",conductPBOut_ind,DB.Thm),
   ("conductPBOut_def",conductPBOut_def,DB.Thm),
   ("authTestConductPB_ind",authTestConductPB_ind,DB.Thm),
   ("authTestConductPB_def",authTestConductPB_def,DB.Thm),
   ("authTestConductPB_cmd_reject_lemma",
    authTestConductPB_cmd_reject_lemma,
    DB.Thm),
   ("PlatoonLeader_plCommandPB_lemma",
    PlatoonLeader_plCommandPB_lemma,
    DB.Thm),
   ("PlatoonLeader_exec_plCommandPB_justified_thm",
    PlatoonLeader_exec_plCommandPB_justified_thm,
    DB.Thm),
   ("PlatoonSergeant_psgCommandPB_lemma",
    PlatoonSergeant_psgCommandPB_lemma,
    DB.Thm),
   ("PlatoonSergeant_exec_psgCommandPB_justified_thm",
    PlatoonSergeant_exec_psgCommandPB_justified_thm,
    DB.Thm)]

  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "ssmConductPB",
    thydataty = "compute",
    read = ThmBind.read,
    data =
        "ssmConductPB.conductPBNS_def ssmConductPB.conductPBOut_def ssmConductPB.secContextConductPB_def ssmConductPB.ssmConductPBStateInterp_def ssmConductPB.authTestConductPB_def"
  }
  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "ssmConductPB",
    thydataty = "TermGrammarDeltas",
    read = ThmBind.read,
    data =
        "OO11.conductPBNS4.%237OO12.conductPBOut4.%238OO17.authTestConductPB4.%235OO23.ssmConductPBStateInterp4.%265OO19.secContextConductPB4.%262"
  }
  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val ssmConductPB_grammars = merge_grammars ["ConductPBType", "ssm11",
                                              "OMNIType"]
  local
  val (tyUDs, tmUDs) = GrammarDeltas.thy_deltas{thyname="ssmConductPB"}
  val addtmUDs = term_grammar.add_deltas tmUDs
  val addtyUDs = type_grammar.apply_deltas tyUDs
  in
  val ssmConductPB_grammars = 
    Portable.## (addtyUDs,addtmUDs) ssmConductPB_grammars
  val _ = Parse.grammarDB_insert("ssmConductPB",ssmConductPB_grammars)
  val _ = Parse.temp_set_grammars (addtyUDs (Parse.type_grammar()), addtmUDs (Parse.term_grammar()))
  end (* addUDs local *)
  end

val _ = if !Globals.print_thy_loads then print "done\n" else ()
val _ = Theory.load_complete "ssmConductPB"
end
