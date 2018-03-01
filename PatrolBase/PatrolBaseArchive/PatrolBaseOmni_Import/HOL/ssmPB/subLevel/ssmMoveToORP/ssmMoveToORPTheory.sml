structure ssmMoveToORPTheory :> ssmMoveToORPTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading ssmMoveToORPTheory ... " else ()
  open Type Term Thm
  infixr -->

  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  (*  Parents *)
  local open MoveToORPTypeTheory OMNITypeTheory ssm11Theory
  in end;
  val _ = Theory.link_parents
          ("ssmMoveToORP",
          Arbnum.fromString "1500249363",
          Arbnum.fromString "589565")
          [("MoveToORPType",
           Arbnum.fromString "1500249361",
           Arbnum.fromString "444727"),
           ("ssm11",
           Arbnum.fromString "1499652452",
           Arbnum.fromString "890464"),
           ("OMNIType",
           Arbnum.fromString "1499574745",
           Arbnum.fromString "168021")];
  val _ = Theory.incorporate_types "ssmMoveToORP" [];

  val idvector = 
    let fun ID(thy,oth) = {Thy = thy, Other = oth}
    in Vector.fromList
  [ID("min", "fun"), ID("aclfoundation", "Form"),
   ID("MoveToORPType", "stateRole"), ID("ssm11", "order"),
   ID("OMNIType", "command"), ID("MoveToORPType", "slCommand"),
   ID("OMNIType", "state"), ID("MoveToORPType", "slState"),
   ID("list", "list"), ID("MoveToORPType", "slOutput"),
   ID("ssm11", "trType"), ID("min", "bool"), ID("aclfoundation", "Kripke"),
   ID("aclfoundation", "po"), ID("OMNIType", "output"),
   ID("aclfoundation", "Princ"), ID("aclfoundation", "IntLevel"),
   ID("OMNIType", "escCommand"), ID("aclfoundation", "SecLevel"),
   ID("num", "num"), ID("bool", "!"), ID("pair", ","), ID("pair", "prod"),
   ID("bool", "/\\"), ID("min", "="), ID("min", "==>"), ID("min", "@"),
   ID("ssm11", "CFG"), ID("ssm11", "configuration"),
   ID("ssm11", "CFGInterpret"), ID("MoveToORPType", "COMPLETE"),
   ID("list", "CONS"), ID("MoveToORPType", "Complete"),
   ID("OMNIType", "ESCc"), ID("bool", "F"), ID("aclfoundation", "FF"),
   ID("aclfoundation", "Form_CASE"), ID("combin", "I"), ID("list", "NIL"),
   ID("aclfoundation", "Name"), ID("MoveToORPType", "PLAN_PB"),
   ID("MoveToORPType", "PLTForm"), ID("MoveToORPType", "PLTMove"),
   ID("MoveToORPType", "PLTPlan"), ID("MoveToORPType", "PLTSecureHalt"),
   ID("MoveToORPType", "PLT_FORM"), ID("MoveToORPType", "PLT_MOVE"),
   ID("MoveToORPType", "PLT_SECURE_HALT"),
   ID("MoveToORPType", "PlatoonLeader"), ID("aclfoundation", "Princ_CASE"),
   ID("OMNIType", "SLc"), ID("ssm11", "SOME"), ID("bool", "T"),
   ID("ssm11", "TR"), ID("aclfoundation", "TT"), ID("relation", "WF"),
   ID("relation", "WFREC"), ID("aclfoundation", "andf"),
   ID("ssmMoveToORP", "authTestMoveToORP"),
   ID("MoveToORPType", "complete"), ID("aclfoundation", "controls"),
   ID("ssm11", "discard"), ID("aclfoundation", "domi"),
   ID("aclfoundation", "doms"), ID("aclfoundation", "eqf"),
   ID("aclfoundation", "eqi"), ID("aclfoundation", "eqn"),
   ID("aclfoundation", "eqs"), ID("ssm11", "exec"),
   ID("aclfoundation", "impf"), ID("MoveToORPType", "incomplete"),
   ID("aclfoundation", "lt"), ID("aclfoundation", "lte"),
   ID("aclfoundation", "meet"), ID("ssmMoveToORP", "moveToORPNS"),
   ID("ssmMoveToORP", "moveToORPOut"), ID("aclfoundation", "notf"),
   ID("aclfoundation", "orf"), ID("MoveToORPType", "pltForm"),
   ID("MoveToORPType", "pltMove"), ID("MoveToORPType", "pltSecureHalt"),
   ID("aclfoundation", "prop"), ID("aclfoundation", "quoting"),
   ID("aclfoundation", "reps"), ID("aclrules", "sat"),
   ID("aclfoundation", "says"), ID("ssmMoveToORP", "secContextMoveToORP"),
   ID("aclfoundation", "speaks_for"),
   ID("ssmMoveToORP", "ssmMoveToORPStateInterp"), ID("ssm11", "trap"),
   ID("MoveToORPType", "unAuthenticated"),
   ID("MoveToORPType", "unAuthorized"), ID("bool", "~")]
  end;
  local open SharingTables
  in
  val tyvector = build_type_vector idvector
  [TYV "'e", TYV "'d", TYOP [2], TYOP [5], TYOP [4, 3], TYOP [3, 4],
   TYOP [1, 5, 2, 1, 0], TYOP [7], TYOP [6, 7], TYOP [0, 8, 6],
   TYOP [8, 6], TYOP [0, 3, 10], TYOP [9], TYOP [10, 4], TYOP [0, 13, 12],
   TYOP [0, 7, 14], TYOP [0, 13, 7], TYOP [0, 7, 16], TYOP [11],
   TYOP [0, 6, 18], TYV "'b", TYOP [12, 5, 20, 2, 1, 0], TYOP [0, 13, 8],
   TYOP [0, 8, 22], TYOP [13, 1], TYOP [13, 0], TYOP [14, 12],
   TYOP [0, 13, 26], TYOP [0, 8, 27], TYOP [0, 13, 18], TYOP [0, 7, 29],
   TYOP [0, 6, 19], TYOP [8, 26], TYOP [15, 2], TYOP [16, 2, 1], TYOP [17],
   TYOP [18, 2, 0], TYOP [19], TYOP [0, 19, 18], TYOP [0, 34, 18],
   TYOP [0, 39, 18], TYOP [0, 21, 18], TYOP [0, 41, 18], TYOP [0, 33, 18],
   TYOP [0, 43, 18], TYOP [0, 36, 18], TYOP [0, 45, 18], TYOP [0, 4, 18],
   TYOP [0, 47, 18], TYOP [0, 35, 18], TYOP [0, 49, 18], TYOP [0, 38, 18],
   TYOP [0, 30, 18], TYOP [0, 52, 18], TYOP [0, 28, 18], TYOP [0, 54, 18],
   TYOP [0, 23, 18], TYOP [0, 56, 18], TYOP [0, 37, 18], TYOP [0, 58, 18],
   TYOP [0, 5, 18], TYOP [0, 60, 18], TYOP [0, 24, 18], TYOP [0, 62, 18],
   TYOP [0, 25, 18], TYOP [0, 64, 18], TYOP [0, 3, 18], TYOP [0, 66, 18],
   TYOP [0, 7, 18], TYOP [0, 68, 18], TYOP [0, 8, 18], TYOP [0, 70, 18],
   TYOP [0, 29, 18], TYOP [22, 24, 25], TYOP [22, 21, 73],
   TYOP [0, 73, 74], TYOP [0, 21, 75], TYOP [0, 25, 73], TYOP [0, 24, 77],
   TYOP [0, 18, 18], TYOP [0, 18, 79], TYOP [0, 19, 38], TYOP [0, 10, 18],
   TYOP [0, 10, 82], TYOP [0, 12, 18], TYOP [0, 12, 84], TYOP [0, 7, 68],
   TYOP [0, 31, 18], TYOP [0, 87, 31], TYOP [28, 4, 1, 0, 26, 2, 8],
   TYOP [0, 32, 89], TYOP [0, 8, 90], TYOP [0, 10, 91], TYOP [0, 10, 92],
   TYOP [0, 9, 93], TYOP [0, 19, 94], TYOP [0, 89, 18], TYOP [0, 74, 96],
   TYOP [0, 10, 10], TYOP [0, 6, 98], TYOP [0, 32, 32], TYOP [0, 26, 100],
   TYOP [0, 35, 4], TYOP [0, 37, 58], TYOP [0, 103, 18],
   TYOP [0, 103, 104], TYOP [0, 103, 105], TYOP [0, 36, 45],
   TYOP [0, 107, 106], TYOP [0, 107, 108], TYOP [0, 34, 39],
   TYOP [0, 110, 109], TYOP [0, 110, 111], TYOP [0, 33, 19],
   TYOP [0, 33, 113], TYOP [0, 114, 112], TYOP [0, 113, 115],
   TYOP [0, 33, 43], TYOP [0, 117, 116], TYOP [0, 113, 118],
   TYOP [0, 31, 119], TYOP [0, 31, 120], TYOP [0, 31, 121],
   TYOP [0, 31, 122], TYOP [0, 19, 123], TYOP [0, 60, 124],
   TYOP [0, 18, 125], TYOP [0, 18, 126], TYOP [0, 6, 127], TYOP [0, 2, 33],
   TYOP [0, 117, 18], TYOP [0, 117, 130], TYOP [0, 2, 18],
   TYOP [0, 132, 131], TYOP [0, 33, 133], TYOP [0, 3, 4], TYOP [0, 4, 5],
   TYOP [0, 89, 96], TYOP [0, 13, 137], TYOP [0, 74, 138],
   TYOP [0, 19, 19], TYOP [0, 140, 19], TYOP [0, 31, 141], TYOP [0, 6, 6],
   TYOP [0, 6, 143], TYOP [0, 33, 143], TYOP [0, 4, 13], TYOP [0, 34, 6],
   TYOP [0, 34, 147], TYOP [0, 36, 6], TYOP [0, 36, 149], TYOP [0, 37, 6],
   TYOP [0, 37, 151], TYOP [0, 33, 33], TYOP [0, 33, 153], TYOP [0, 5, 6],
   TYOP [0, 33, 145], TYOP [0, 74, 19], TYOP [0, 33, 6], TYOP [0, 33, 158]]
  end
  val _ = Theory.incorporate_consts "ssmMoveToORP" tyvector
     [("ssmMoveToORPStateInterp", 9), ("secContextMoveToORP", 11),
      ("moveToORPOut", 15), ("moveToORPNS", 17),
      ("authTestMoveToORP", 19)];

  local open SharingTables
  in
  val tmvector = build_term_vector idvector tyvector
  [TMV("M", 21), TMV("NS", 23), TMV("Oi", 24), TMV("Os", 25),
   TMV("Out", 28), TMV("P", 19), TMV("P", 30), TMV("R", 31), TMV("a", 6),
   TMV("authTestMoveToORP", 19), TMV("cmd", 4), TMV("cmd", 5),
   TMV("cmd", 3), TMV("ins", 10), TMV("outs", 32), TMV("s", 7),
   TMV("s", 8), TMV("slCommand", 3), TMV("state", 8), TMV("v", 6),
   TMV("v", 5), TMV("v", 7), TMV("v1", 6), TMV("v1", 13), TMV("v10", 33),
   TMV("v100", 6), TMV("v101", 6), TMV("v102", 6), TMV("v103", 6),
   TMV("v104", 6), TMV("v105", 6), TMV("v106", 6), TMV("v107", 6),
   TMV("v108", 6), TMV("v109", 33), TMV("v110", 6), TMV("v111", 33),
   TMV("v112", 33), TMV("v113", 33), TMV("v114", 6), TMV("v115", 33),
   TMV("v116", 33), TMV("v117", 6), TMV("v118", 34), TMV("v119", 34),
   TMV("v12", 33), TMV("v12", 35), TMV("v120", 34), TMV("v121", 34),
   TMV("v122", 36), TMV("v123", 36), TMV("v124", 36), TMV("v125", 36),
   TMV("v126", 37), TMV("v127", 37), TMV("v128", 37), TMV("v129", 37),
   TMV("v13", 33), TMV("v130", 37), TMV("v131", 37), TMV("v133", 33),
   TMV("v134", 33), TMV("v135", 33), TMV("v136", 33), TMV("v137", 2),
   TMV("v138", 33), TMV("v139", 33), TMV("v14", 33), TMV("v140", 33),
   TMV("v141", 33), TMV("v15", 6), TMV("v15", 35), TMV("v16", 33),
   TMV("v17", 33), TMV("v18", 6), TMV("v18", 35), TMV("v19", 34),
   TMV("v2", 6), TMV("v20", 34), TMV("v21", 34), TMV("v21", 35),
   TMV("v22", 34), TMV("v23", 36), TMV("v23", 4), TMV("v24", 36),
   TMV("v25", 36), TMV("v26", 36), TMV("v27", 37), TMV("v28", 37),
   TMV("v29", 37), TMV("v3", 6), TMV("v30", 37), TMV("v31", 37),
   TMV("v32", 37), TMV("v33", 5), TMV("v34", 6), TMV("v35", 6),
   TMV("v36", 6), TMV("v37", 6), TMV("v38", 6), TMV("v39", 6),
   TMV("v4", 6), TMV("v40", 6), TMV("v41", 6), TMV("v42", 6),
   TMV("v43", 33), TMV("v44", 6), TMV("v45", 33), TMV("v46", 33),
   TMV("v47", 33), TMV("v48", 6), TMV("v49", 33), TMV("v5", 6),
   TMV("v50", 33), TMV("v51", 6), TMV("v52", 34), TMV("v53", 34),
   TMV("v54", 34), TMV("v55", 34), TMV("v56", 36), TMV("v57", 36),
   TMV("v58", 36), TMV("v59", 36), TMV("v6", 6), TMV("v6", 35),
   TMV("v60", 37), TMV("v61", 37), TMV("v62", 37), TMV("v63", 37),
   TMV("v64", 37), TMV("v65", 37), TMV("v66", 5), TMV("v67", 6),
   TMV("v68", 6), TMV("v69", 6), TMV("v7", 6), TMV("v70", 6),
   TMV("v71", 6), TMV("v72", 6), TMV("v73", 6), TMV("v74", 6),
   TMV("v75", 6), TMV("v76", 33), TMV("v77", 6), TMV("v78", 33),
   TMV("v79", 33), TMV("v8", 6), TMV("v80", 33), TMV("v81", 6),
   TMV("v82", 33), TMV("v83", 33), TMV("v84", 6), TMV("v85", 34),
   TMV("v86", 34), TMV("v87", 34), TMV("v88", 34), TMV("v89", 36),
   TMV("v9", 6), TMV("v9", 35), TMV("v90", 36), TMV("v91", 36),
   TMV("v92", 36), TMV("v93", 37), TMV("v94", 37), TMV("v95", 37),
   TMV("v96", 37), TMV("v97", 37), TMV("v98", 37), TMC(20, 38),
   TMC(20, 40), TMC(20, 42), TMC(20, 44), TMC(20, 46), TMC(20, 48),
   TMC(20, 50), TMC(20, 51), TMC(20, 53), TMC(20, 55), TMC(20, 57),
   TMC(20, 59), TMC(20, 61), TMC(20, 63), TMC(20, 65), TMC(20, 67),
   TMC(20, 69), TMC(20, 71), TMC(20, 72), TMC(21, 76), TMC(21, 78),
   TMC(23, 80), TMC(24, 31), TMC(24, 80), TMC(24, 81), TMC(24, 83),
   TMC(24, 85), TMC(24, 86), TMC(25, 80), TMC(26, 88), TMC(27, 95),
   TMC(29, 97), TMC(30, 7), TMC(31, 99), TMC(31, 101), TMC(32, 12),
   TMC(33, 102), TMC(34, 18), TMC(35, 6), TMC(36, 128), TMC(37, 79),
   TMC(38, 10), TMC(39, 129), TMC(40, 7), TMC(41, 12), TMC(42, 12),
   TMC(43, 12), TMC(44, 12), TMC(45, 7), TMC(46, 7), TMC(47, 7),
   TMC(48, 2), TMC(49, 134), TMC(50, 135), TMC(51, 136), TMC(52, 18),
   TMC(53, 139), TMC(54, 6), TMC(55, 87), TMC(56, 142), TMC(57, 144),
   TMC(58, 19), TMC(59, 3), TMC(60, 145), TMC(61, 146), TMC(62, 148),
   TMC(63, 150), TMC(64, 144), TMC(65, 148), TMC(66, 152), TMC(67, 150),
   TMC(68, 146), TMC(69, 144), TMC(70, 3), TMC(71, 152), TMC(72, 152),
   TMC(73, 154), TMC(74, 17), TMC(75, 15), TMC(76, 143), TMC(77, 144),
   TMC(78, 3), TMC(79, 3), TMC(80, 3), TMC(81, 155), TMC(82, 154),
   TMC(83, 156), TMC(84, 157), TMC(85, 145), TMC(86, 11), TMC(87, 159),
   TMC(88, 9), TMC(89, 146), TMC(90, 12), TMC(91, 12), TMC(92, 79)]
  end
  structure ThmBind = struct
    val DT = Thm.disk_thm
    val read = Term.read_raw tmvector
  end
  fun op authTestMoveToORP_primitive_def x = x
    val op authTestMoveToORP_primitive_def =
    ThmBind.DT(((("ssmMoveToORP",8),[]),[]),
               [ThmBind.read"%192%229@%227%197%7%226$0@|@2%9%8%207$0@%208%205@2%208%205@2%94%208%205@|@%95%208%205@|@%96%97%208%205@||@%98%99%208%205@||@%100%102%208%205@||@%103%104%208%205@||@%105%106%207$0@%208%205@2%208%205@2%11%220$2@%64%208%223@|@%65%66%208%205@||@%68%69%208%205@||@|@%25%208%205@|@%26%27%208%205@||@%28%29%208%205@||@%30%31%208%205@||@%32%33%208%205@||@%34%35%208%205@||@%36%37%208%205@||@%38%39%208%205@||@%40%41%42%208%205@|||@%43%44%208%205@||@%47%48%208%205@||@%49%50%208%205@||@%51%52%208%205@||@%53%54%208%205@||@%55%56%208%205@||@%58%59%208%205@||@||@%107%108%208%205@||@%109%110%208%205@||@%111%113%114%208%205@|||@%115%116%208%205@||@%117%118%208%205@||@%119%120%208%205@||@%121%122%208%205@||@%125%126%208%205@||@%127%128%208%205@||@%129%130%208%205@||@||@2"])
  fun op ssmMoveToORPStateInterp_def x = x
    val op ssmMoveToORPStateInterp_def =
    ThmBind.DT(((("ssmMoveToORP",11),[]),[]),
               [ThmBind.read"%185%18%190%259$0@2%225@|@"])
  fun op secContextMoveToORP_def x = x
    val op secContextMoveToORP_def =
    ThmBind.DT(((("ssmMoveToORP",13),[]),[]),
               [ThmBind.read"%183%12%193%257$0@2%201%231%210%219@2%252%222%221$0@5%209@2|@"])
  fun op moveToORPNS_ind x = x
    val op moveToORPNS_ind =
    ThmBind.DT(((("ssmMoveToORP",2),
                [("MoveToORPType",[22,48]),("OMNIType",[36]),
                 ("bool",[25,26,46,47,52,53,57,62,71,75,76,77,79]),
                 ("pair",[5,16]),("relation",[101,107]),
                 ("sat",[1,3,5,6,7,11,12,13,14,15]),
                 ("ssm11",[31])]),["DISK_THM"]),
               [ThmBind.read"%176%6%196%189$0%211@%239%221%249@4%189$0%211@%239%221%241@4%189$0%216@%239%221%250@4%189$0%216@%239%221%241@4%189$0%217@%239%221%251@4%189$0%217@%239%221%241@4%189$0%218@%239%221%230@4%189$0%218@%239%221%241@4%189%184%15%183%12$2$1@%260%221$0@3|@|@2%189%184%15%183%12$2$1@%232%221$0@3|@|@2%189%184%15%174%124$2$1@%232%204$0@3|@|@2%189%184%15%174%158$2$1@%260%204$0@3|@|@2%189%174%46$1%211@%239%204$0@3|@2%189$0%211@%239%221%250@4%189$0%211@%239%221%251@4%189$0%211@%239%221%230@4%189%174%71$1%216@%239%204$0@3|@2%189$0%216@%239%221%249@4%189$0%216@%239%221%251@4%189$0%216@%239%221%230@4%189%174%75$1%217@%239%204$0@3|@2%189$0%217@%239%221%249@4%189$0%217@%239%221%250@4%189$0%217@%239%221%230@4%189%174%80$1%218@%239%204$0@3|@2%189$0%218@%239%221%249@4%189$0%218@%239%221%250@4%189$0%218@%239%221%251@4%173%83$1%200@%239$0@2|@30%184%21%186%23$2$1@$0@|@|@2|@"])
  fun op moveToORPNS_def x = x
    val op moveToORPNS_def =
    ThmBind.DT(((("ssmMoveToORP",3),
                [("MoveToORPType",[18,44]),("OMNIType",[30]),
                 ("bool",[15,57]),("combin",[19]),("pair",[49]),
                 ("relation",[107,126]),("ssm11",[25]),
                 ("ssmMoveToORP",[0,1])]),["DISK_THM"]),
               [ThmBind.read"%189%195%245%211@%239%221%249@4%216@2%189%195%245%211@%239%221%241@4%211@2%189%195%245%216@%239%221%250@4%217@2%189%195%245%216@%239%221%241@4%216@2%189%195%245%217@%239%221%251@4%218@2%189%195%245%217@%239%221%241@4%217@2%189%195%245%218@%239%221%230@4%200@2%189%195%245%218@%239%221%241@4%218@2%189%195%245%15@%260%221%12@4%15@2%195%245%15@%232%221%12@4%15@10"])
  fun op moveToORPOut_ind x = x
    val op moveToORPOut_ind =
    ThmBind.DT(((("ssmMoveToORP",6),
                [("MoveToORPType",[22,48]),("OMNIType",[36]),
                 ("bool",[25,26,46,47,52,53,57,62,71,75,76,77,79]),
                 ("pair",[5,16]),("relation",[101,107]),
                 ("sat",[1,3,5,6,7,11,12,13,14,15]),
                 ("ssm11",[31])]),["DISK_THM"]),
               [ThmBind.read"%176%6%196%189$0%211@%239%221%249@4%189$0%211@%239%221%241@4%189$0%216@%239%221%250@4%189$0%216@%239%221%241@4%189$0%217@%239%221%251@4%189$0%217@%239%221%241@4%189$0%218@%239%221%230@4%189$0%218@%239%221%241@4%189%184%15%183%12$2$1@%260%221$0@3|@|@2%189%184%15%183%12$2$1@%232%221$0@3|@|@2%189%184%15%174%124$2$1@%232%204$0@3|@|@2%189%184%15%174%158$2$1@%260%204$0@3|@|@2%189%174%46$1%211@%239%204$0@3|@2%189$0%211@%239%221%250@4%189$0%211@%239%221%251@4%189$0%211@%239%221%230@4%189%174%71$1%216@%239%204$0@3|@2%189$0%216@%239%221%249@4%189$0%216@%239%221%251@4%189$0%216@%239%221%230@4%189%174%75$1%217@%239%204$0@3|@2%189$0%217@%239%221%249@4%189$0%217@%239%221%250@4%189$0%217@%239%221%230@4%189%174%80$1%218@%239%204$0@3|@2%189$0%218@%239%221%249@4%189$0%218@%239%221%250@4%189$0%218@%239%221%251@4%173%83$1%200@%239$0@2|@30%184%21%186%23$2$1@$0@|@|@2|@"])
  fun op moveToORPOut_def x = x
    val op moveToORPOut_def =
    ThmBind.DT(((("ssmMoveToORP",7),
                [("MoveToORPType",[18,44]),("OMNIType",[30]),
                 ("bool",[15,57]),("combin",[19]),("pair",[49]),
                 ("relation",[107,126]),("ssm11",[25]),
                 ("ssmMoveToORP",[4,5])]),["DISK_THM"]),
               [ThmBind.read"%189%194%246%211@%239%221%249@4%212@2%189%194%246%211@%239%221%241@4%214@2%189%194%246%216@%239%221%250@4%213@2%189%194%246%216@%239%221%241@4%212@2%189%194%246%217@%239%221%251@4%215@2%189%194%246%217@%239%221%241@4%213@2%189%194%246%218@%239%221%230@4%203@2%189%194%246%218@%239%221%241@4%215@2%189%194%246%15@%260%221%12@4%262@2%194%246%15@%232%221%12@4%261@10"])
  fun op authTestMoveToORP_ind x = x
    val op authTestMoveToORP_ind =
    ThmBind.DT(((("ssmMoveToORP",9),
                [("MoveToORPType",[97]),("aclfoundation",[55,116]),
                 ("bool",[25,26,46,47,52,53,57,62,71,75,76,77,79]),
                 ("relation",[101,107]),
                 ("sat",[1,3,5,6,7,11,12,13,14,15])]),["DISK_THM"]),
               [ThmBind.read"%175%5%196%189%180%11$1%256%210%219@2%252$0@3|@2%189$0%225@2%189$0%206@2%189%180%20$1%252$0@2|@2%189%168%22$1%247$0@2|@2%189%168%77%168%90$2%228$1@$0@2|@|@2%189%168%101%168%112$2%248$1@$0@2|@|@2%189%168%123%168%135$2%240$1@$0@2|@|@2%189%168%146%168%157$2%235$1@$0@2|@|@2%189%171%24$1%256$0@%225@2|@2%189%171%24$1%256$0@%206@2|@2%189%171%60%171%61%180%131$3%256%244$2@$1@2%252$0@3|@|@|@2%189%171%62%171%63%180%131$3%256%253$2@$1@2%252$0@3|@|@|@2%189%171%24%168%132$2%256$1@%247$0@3|@|@2%189%171%24%168%133%168%134$3%256$2@%228$1@$0@3|@|@|@2%189%171%24%168%136%168%137$3%256$2@%248$1@$0@3|@|@|@2%189%171%24%168%138%168%139$3%256$2@%240$1@$0@3|@|@|@2%189%171%24%168%140%168%141$3%256$2@%235$1@$0@3|@|@|@2%189%171%24%171%142%168%143$3%256$2@%256$1@$0@3|@|@|@2%189%171%24%171%144%171%145$3%256$2@%258$1@$0@3|@|@|@2%189%171%24%171%147%168%148$3%256$2@%231$1@$0@3|@|@|@2%189%171%24%171%149%171%150%168%151$4%256$3@%254$2@$1@$0@3|@|@|@|@2%189%171%24%169%152%169%153$3%256$2@%233$1@$0@3|@|@|@2%189%171%24%169%154%169%155$3%256$2@%236$1@$0@3|@|@|@2%189%171%24%172%156%172%159$3%256$2@%234$1@$0@3|@|@|@2%189%171%24%172%160%172%161$3%256$2@%238$1@$0@3|@|@|@2%189%171%24%179%162%179%163$3%256$2@%237$1@$0@3|@|@|@2%189%171%24%179%164%179%165$3%256$2@%243$1@$0@3|@|@|@2%189%171%24%179%166%179%167$3%256$2@%242$1@$0@3|@|@|@2%189%171%45%171%57$2%258$1@$0@2|@|@2%189%171%67%168%70$2%231$1@$0@2|@|@2%189%171%72%171%73%168%74$3%254$2@$1@$0@2|@|@|@2%189%169%76%169%78$2%233$1@$0@2|@|@2%189%169%79%169%81$2%236$1@$0@2|@|@2%189%172%82%172%84$2%234$1@$0@2|@|@2%189%172%85%172%86$2%238$1@$0@2|@|@2%189%179%87%179%88$2%237$1@$0@2|@|@2%189%179%89%179%91$2%243$1@$0@2|@|@2%179%92%179%93$2%242$1@$0@2|@|@40%168%19$1$0@|@2|@"])
  fun op authTestMoveToORP_def x = x
    val op authTestMoveToORP_def =
    ThmBind.DT(((("ssmMoveToORP",10),
                [("aclfoundation",[33,110]),("bool",[15]),("combin",[19]),
                 ("relation",[107,126]),
                 ("ssmMoveToORP",[8])]),["DISK_THM"]),
               [ThmBind.read"%189%191%229%256%210%219@2%252%11@4%223@2%189%191%229%225@2%205@2%189%191%229%206@2%205@2%189%191%229%252%20@3%205@2%189%191%229%247%22@3%205@2%189%191%229%228%77@%90@3%205@2%189%191%229%248%101@%112@3%205@2%189%191%229%240%123@%135@3%205@2%189%191%229%235%146@%157@3%205@2%189%191%229%256%24@%225@3%205@2%189%191%229%256%24@%206@3%205@2%189%191%229%256%244%60@%61@2%252%131@4%205@2%189%191%229%256%253%62@%63@2%252%131@4%205@2%189%191%229%256%24@%247%132@4%205@2%189%191%229%256%24@%228%133@%134@4%205@2%189%191%229%256%24@%248%136@%137@4%205@2%189%191%229%256%24@%240%138@%139@4%205@2%189%191%229%256%24@%235%140@%141@4%205@2%189%191%229%256%24@%256%142@%143@4%205@2%189%191%229%256%24@%258%144@%145@4%205@2%189%191%229%256%24@%231%147@%148@4%205@2%189%191%229%256%24@%254%149@%150@%151@4%205@2%189%191%229%256%24@%233%152@%153@4%205@2%189%191%229%256%24@%236%154@%155@4%205@2%189%191%229%256%24@%234%156@%159@4%205@2%189%191%229%256%24@%238%160@%161@4%205@2%189%191%229%256%24@%237%162@%163@4%205@2%189%191%229%256%24@%243%164@%165@4%205@2%189%191%229%256%24@%242%166@%167@4%205@2%189%191%229%258%45@%57@3%205@2%189%191%229%231%67@%70@3%205@2%189%191%229%254%72@%73@%74@3%205@2%189%191%229%233%76@%78@3%205@2%189%191%229%236%79@%81@3%205@2%189%191%229%234%82@%84@3%205@2%189%191%229%238%85@%86@3%205@2%189%191%229%237%87@%88@3%205@2%189%191%229%243%89@%91@3%205@2%191%229%242%92@%93@3%205@39"])
  fun op authTestMoveToORP_cmd_reject_lemma x = x
    val op authTestMoveToORP_cmd_reject_lemma =
    ThmBind.DT(((("ssmMoveToORP",12),
                [("aclfoundation",[33,110]),
                 ("bool",[15,25,26,46,47,52,53,62,70,72]),("combin",[19]),
                 ("relation",[107,126]),("sat",[1,3,5,6,7,11,14,15]),
                 ("ssmMoveToORP",[8])]),["DISK_THM"]),
               [ThmBind.read"%173%10%263%229%252%222$0@4|@"])
  fun op PlatoonLeader_slCommand_lemma x = x
    val op PlatoonLeader_slCommand_lemma =
    ThmBind.DT(((("ssmMoveToORP",14),
                [("aclDrules",[3]),("aclrules",[63]),
                 ("bool",[25,26,46,47,50,52,53,62,92,93,95]),
                 ("sat",[1,3,5,6,7,11,12,13,14,15]),("satList",[1,3]),
                 ("ssm11",[52]),("ssmMoveToORP",[11,13])]),["DISK_THM"]),
               [ThmBind.read"%196%199%187%0@%188%2@%3@3%198%229@%259@%257%17@2%201%256%210%219@2%252%222%221%17@5%13@2%16@%14@3%255%187%0@%188%2@%3@3%252%222%221%17@5"])
  fun op PlatoonLeader_exec_slCommand_justified_thm x = x
    val op PlatoonLeader_exec_slCommand_justified_thm =
    ThmBind.DT(((("ssmMoveToORP",15),
                [("aclDrules",[3]),("aclrules",[63]),
                 ("bool",
                 [25,26,35,42,46,47,50,52,53,55,57,62,70,76,83,92,93,95,
                  145]),("combin",[19]),("sat",[1,3,5,6,7,11,12,13,14,15]),
                 ("satList",[1,3]),("ssm11",[52,62]),
                 ("ssmMoveToORP",[11,13])]),["DISK_THM"]),
               [ThmBind.read"%178%1%177%4%170%0%181%2%182%3%191%224%187$2@%188$1@$0@3%239%221%17@3%198%229@%259@%257%17@2%201%256%210%219@2%252%222%221%17@5%13@2%16@%14@2%198%229@%259@%257%17@2%13@$4%16@%239%221%17@4%202$3%16@%239%221%17@4%14@4%189%229%256%210%219@2%252%222%221%17@6%189%199%187$2@%188$1@$0@3%198%229@%259@%257%17@2%201%256%210%219@2%252%222%221%17@5%13@2%16@%14@3%255%187$2@%188$1@$0@3%252%222%221%17@7|@|@|@|@|@"])

  val _ = DB.bindl "ssmMoveToORP"
  [("authTestMoveToORP_primitive_def",
    authTestMoveToORP_primitive_def,
    DB.Def),
   ("ssmMoveToORPStateInterp_def",ssmMoveToORPStateInterp_def,DB.Def),
   ("secContextMoveToORP_def",secContextMoveToORP_def,DB.Def),
   ("moveToORPNS_ind",moveToORPNS_ind,DB.Thm),
   ("moveToORPNS_def",moveToORPNS_def,DB.Thm),
   ("moveToORPOut_ind",moveToORPOut_ind,DB.Thm),
   ("moveToORPOut_def",moveToORPOut_def,DB.Thm),
   ("authTestMoveToORP_ind",authTestMoveToORP_ind,DB.Thm),
   ("authTestMoveToORP_def",authTestMoveToORP_def,DB.Thm),
   ("authTestMoveToORP_cmd_reject_lemma",
    authTestMoveToORP_cmd_reject_lemma,
    DB.Thm),
   ("PlatoonLeader_slCommand_lemma",PlatoonLeader_slCommand_lemma,DB.Thm),
   ("PlatoonLeader_exec_slCommand_justified_thm",
    PlatoonLeader_exec_slCommand_justified_thm,
    DB.Thm)]

  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "ssmMoveToORP",
    thydataty = "compute",
    read = ThmBind.read,
    data =
        "ssmMoveToORP.moveToORPNS_def ssmMoveToORP.moveToORPOut_def ssmMoveToORP.secContextMoveToORP_def ssmMoveToORP.ssmMoveToORPStateInterp_def ssmMoveToORP.authTestMoveToORP_def"
  }
  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "ssmMoveToORP",
    thydataty = "TermGrammarDeltas",
    read = ThmBind.read,
    data =
        "OO11.moveToORPNS4.%245OO12.moveToORPOut4.%246OO17.authTestMoveToORP4.%229OO23.ssmMoveToORPStateInterp4.%259OO19.secContextMoveToORP4.%257"
  }
  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val ssmMoveToORP_grammars = merge_grammars ["MoveToORPType", "ssm11",
                                              "OMNIType"]
  local
  val (tyUDs, tmUDs) = GrammarDeltas.thy_deltas{thyname="ssmMoveToORP"}
  val addtmUDs = term_grammar.add_deltas tmUDs
  val addtyUDs = type_grammar.apply_deltas tyUDs
  in
  val ssmMoveToORP_grammars = 
    Portable.## (addtyUDs,addtmUDs) ssmMoveToORP_grammars
  val _ = Parse.grammarDB_insert("ssmMoveToORP",ssmMoveToORP_grammars)
  val _ = Parse.temp_set_grammars (addtyUDs (Parse.type_grammar()), addtmUDs (Parse.term_grammar()))
  end (* addUDs local *)
  end

val _ = if !Globals.print_thy_loads then print "done\n" else ()
val _ = Theory.load_complete "ssmMoveToORP"
end
