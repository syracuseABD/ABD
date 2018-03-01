structure ConductORPTypeTheory :> ConductORPTypeTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading ConductORPTypeTheory ... " else ()
  open Type Term Thm
  infixr -->

  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  (*  Parents *)
  local open indexedListsTheory patternMatchesTheory
  in end;
  val _ = Theory.link_parents
          ("ConductORPType",
          Arbnum.fromString "1500769210",
          Arbnum.fromString "919246")
          [("indexedLists",
           Arbnum.fromString "1480536572",
           Arbnum.fromString "423707"),
           ("patternMatches",
           Arbnum.fromString "1480536620",
           Arbnum.fromString "572815")];
  val _ = Theory.incorporate_types "ConductORPType"
       [("stateRole", 0), ("slState", 0), ("slOutput", 0),
        ("slCommand", 0), ("psgCommand", 0), ("plCommand", 0)];

  val idvector = 
    let fun ID(thy,oth) = {Thy = thy, Other = oth}
    in Vector.fromList
  [ID("ConductORPType", "plCommand"), ID("ConductORPType", "slOutput"),
   ID("min", "fun"), ID("num", "num"), ID("ConductORPType", "stateRole"),
   ID("ConductORPType", "slState"), ID("ConductORPType", "slCommand"),
   ID("ConductORPType", "psgCommand"), ID("min", "bool"),
   ID("ind_type", "recspace"), ID("pair", "prod"), ID("bool", "!"),
   ID("arithmetic", "+"), ID("pair", ","), ID("bool", "/\\"),
   ID("num", "0"), ID("prim_rec", "<"), ID("min", "="), ID("min", "==>"),
   ID("bool", "?"), ID("ConductORPType", "ACTIONS_IN"), ID("bool", "ARB"),
   ID("ConductORPType", "ActionsIn"), ID("arithmetic", "BIT1"),
   ID("arithmetic", "BIT2"), ID("ind_type", "BOTTOM"),
   ID("ConductORPType", "COMPLETE"), ID("bool", "COND"),
   ID("ConductORPType", "CONDUCT_ORP"), ID("ind_type", "CONSTR"),
   ID("ConductORPType", "Complete"), ID("ConductORPType", "ConductORP"),
   ID("bool", "DATATYPE"), ID("arithmetic", "NUMERAL"),
   ID("ConductORPType", "PL"), ID("ConductORPType", "PSG"),
   ID("ConductORPType", "PlatoonLeader"),
   ID("ConductORPType", "PlatoonSergeant"), ID("ConductORPType", "SECURE"),
   ID("num", "SUC"), ID("ConductORPType", "Secure"),
   ID("bool", "TYPE_DEFINITION"), ID("ConductORPType", "WITHDRAW"),
   ID("ConductORPType", "Withdraw"), ID("arithmetic", "ZERO"),
   ID("bool", "\\/"), ID("ConductORPType", "actionsIn"),
   ID("ConductORPType", "complete"), ID("ConductORPType", "num2plCommand"),
   ID("ConductORPType", "num2psgCommand"),
   ID("ConductORPType", "num2slOutput"),
   ID("ConductORPType", "num2slState"),
   ID("ConductORPType", "num2stateRole"),
   ID("ConductORPType", "plCommand2num"),
   ID("ConductORPType", "plCommand_CASE"),
   ID("ConductORPType", "plCommand_size"),
   ID("ConductORPType", "plIncomplete"),
   ID("ConductORPType", "psgCommand2num"),
   ID("ConductORPType", "psgCommand_CASE"),
   ID("ConductORPType", "psgCommand_size"),
   ID("ConductORPType", "psgIncomplete"), ID("ConductORPType", "secure"),
   ID("ConductORPType", "slCommand_CASE"),
   ID("ConductORPType", "slCommand_size"),
   ID("ConductORPType", "slOutput2num"),
   ID("ConductORPType", "slOutput_CASE"),
   ID("ConductORPType", "slOutput_size"),
   ID("ConductORPType", "slState2num"),
   ID("ConductORPType", "slState_CASE"),
   ID("ConductORPType", "slState_size"),
   ID("ConductORPType", "stateRole2num"),
   ID("ConductORPType", "stateRole_CASE"),
   ID("ConductORPType", "stateRole_size"),
   ID("ConductORPType", "unAuthenticated"),
   ID("ConductORPType", "unAuthorized"), ID("ConductORPType", "withdraw"),
   ID("bool", "~")]
  end;
  local open SharingTables
  in
  val tyvector = build_type_vector idvector
  [TYOP [0], TYOP [1], TYOP [3], TYOP [4], TYOP [2, 3, 2], TYV "'a",
   TYOP [2, 5, 5], TYOP [2, 5, 6], TYOP [2, 3, 7], TYOP [5],
   TYOP [2, 9, 2], TYOP [2, 5, 7], TYOP [2, 5, 11], TYOP [2, 5, 12],
   TYOP [2, 9, 13], TYOP [2, 1, 2], TYOP [2, 5, 13], TYOP [2, 5, 16],
   TYOP [2, 1, 17], TYOP [6], TYOP [2, 19, 2], TYOP [7], TYOP [2, 21, 5],
   TYOP [2, 22, 5], TYOP [2, 0, 5], TYOP [2, 24, 23], TYOP [2, 19, 25],
   TYOP [2, 21, 2], TYOP [2, 21, 7], TYOP [2, 0, 2], TYOP [2, 0, 12],
   TYOP [2, 2, 3], TYOP [2, 2, 9], TYOP [2, 2, 1], TYOP [2, 2, 21],
   TYOP [2, 2, 0], TYOP [2, 21, 19], TYOP [2, 0, 19], TYOP [8],
   TYOP [10, 0, 21], TYOP [9, 39], TYOP [2, 40, 38], TYOP [2, 0, 38],
   TYOP [2, 21, 38], TYOP [2, 19, 38], TYOP [2, 1, 38], TYOP [2, 9, 38],
   TYOP [2, 3, 38], TYOP [2, 1, 5], TYOP [2, 9, 5], TYOP [2, 3, 5],
   TYOP [2, 19, 5], TYOP [2, 0, 42], TYOP [2, 0, 52], TYOP [2, 0, 53],
   TYOP [2, 21, 43], TYOP [2, 19, 40], TYOP [2, 36, 38], TYOP [2, 37, 57],
   TYOP [2, 1, 45], TYOP [2, 1, 59], TYOP [2, 1, 60], TYOP [2, 1, 61],
   TYOP [2, 1, 62], TYOP [2, 1, 63], TYOP [2, 9, 46], TYOP [2, 9, 65],
   TYOP [2, 9, 66], TYOP [2, 9, 67], TYOP [2, 3, 47], TYOP [2, 5, 38],
   TYOP [2, 70, 38], TYOP [2, 24, 38], TYOP [2, 72, 38], TYOP [2, 42, 38],
   TYOP [2, 74, 38], TYOP [2, 22, 38], TYOP [2, 76, 38], TYOP [2, 43, 38],
   TYOP [2, 78, 38], TYOP [2, 41, 38], TYOP [2, 80, 38], TYOP [2, 44, 38],
   TYOP [2, 82, 38], TYOP [2, 45, 38], TYOP [2, 84, 38], TYOP [2, 46, 38],
   TYOP [2, 86, 38], TYOP [2, 47, 38], TYOP [2, 88, 38], TYOP [2, 2, 38],
   TYOP [2, 90, 38], TYOP [2, 2, 2], TYOP [2, 2, 92], TYOP [2, 21, 39],
   TYOP [2, 0, 94], TYOP [2, 38, 38], TYOP [2, 38, 96], TYOP [2, 2, 90],
   TYOP [2, 5, 70], TYOP [2, 40, 41], TYOP [2, 19, 44], TYOP [2, 29, 38],
   TYOP [2, 102, 38], TYOP [2, 27, 38], TYOP [2, 104, 38],
   TYOP [2, 51, 38], TYOP [2, 106, 38], TYOP [2, 56, 38],
   TYOP [2, 108, 38], TYOP [2, 48, 38], TYOP [2, 110, 38],
   TYOP [2, 15, 38], TYOP [2, 112, 38], TYOP [2, 49, 38],
   TYOP [2, 114, 38], TYOP [2, 10, 38], TYOP [2, 116, 38],
   TYOP [2, 50, 38], TYOP [2, 118, 38], TYOP [2, 4, 38], TYOP [2, 120, 38],
   TYOP [2, 38, 7], TYOP [2, 2, 40], TYOP [2, 123, 40], TYOP [2, 39, 124],
   TYOP [2, 2, 125], TYOP [2, 90, 102], TYOP [2, 90, 104],
   TYOP [2, 90, 112], TYOP [2, 90, 116], TYOP [2, 90, 120],
   TYOP [2, 41, 108]]
  end
  val _ = Theory.incorporate_consts "ConductORPType" tyvector
     [("withdraw", 0), ("unAuthorized", 1), ("unAuthenticated", 1),
      ("stateRole_size", 4), ("stateRole_CASE", 8), ("stateRole2num", 4),
      ("slState_size", 10), ("slState_CASE", 14), ("slState2num", 10),
      ("slOutput_size", 15), ("slOutput_CASE", 18), ("slOutput2num", 15),
      ("slCommand_size", 20), ("slCommand_CASE", 26), ("secure", 0),
      ("psgIncomplete", 21), ("psgCommand_size", 27),
      ("psgCommand_CASE", 28), ("psgCommand2num", 27), ("plIncomplete", 0),
      ("plCommand_size", 29), ("plCommand_CASE", 30),
      ("plCommand2num", 29), ("num2stateRole", 31), ("num2slState", 32),
      ("num2slOutput", 33), ("num2psgCommand", 34), ("num2plCommand", 35),
      ("complete", 0), ("actionsIn", 21), ("Withdraw", 1), ("WITHDRAW", 9),
      ("Secure", 1), ("SECURE", 9), ("PlatoonSergeant", 3),
      ("PlatoonLeader", 3), ("PSG", 36), ("PL", 37), ("ConductORP", 1),
      ("Complete", 1), ("CONDUCT_ORP", 9), ("COMPLETE", 9),
      ("ActionsIn", 1), ("ACTIONS_IN", 9)];

  local open SharingTables
  in
  val tmvector = build_term_vector idvector tyvector
  [TMV("'slCommand'", 41), TMV("M", 0), TMV("M", 21), TMV("M", 19),
   TMV("M", 1), TMV("M", 9), TMV("M", 3), TMV("M'", 0), TMV("M'", 21),
   TMV("M'", 19), TMV("M'", 1), TMV("M'", 9), TMV("M'", 3), TMV("P", 42),
   TMV("P", 43), TMV("P", 44), TMV("P", 45), TMV("P", 46), TMV("P", 47),
   TMV("a", 0), TMV("a", 21), TMV("a", 1), TMV("a", 9), TMV("a", 3),
   TMV("a'", 0), TMV("a'", 21), TMV("a'", 1), TMV("a'", 9), TMV("a'", 3),
   TMV("a0", 40), TMV("f", 24), TMV("f", 22), TMV("f", 48), TMV("f", 49),
   TMV("f", 50), TMV("f'", 24), TMV("f0", 24), TMV("f1", 22),
   TMV("f1'", 22), TMV("fn", 51), TMV("m", 2), TMV("n", 2), TMV("p", 0),
   TMV("p", 21), TMV("plCommand", 54), TMV("psgCommand", 55), TMV("r", 2),
   TMV("r'", 2), TMV("rep", 29), TMV("rep", 27), TMV("rep", 56),
   TMV("rep", 15), TMV("rep", 10), TMV("rep", 4), TMV("s", 19),
   TMV("slCommand", 58), TMV("slOutput", 64), TMV("slState", 68),
   TMV("ss", 19), TMV("stateRole", 69), TMV("v0", 5), TMV("v0'", 5),
   TMV("v1", 5), TMV("v1'", 5), TMV("v2", 5), TMV("v2'", 5), TMV("v3", 5),
   TMV("v3'", 5), TMV("v4", 5), TMV("v4'", 5), TMV("v5", 5), TMV("v5'", 5),
   TMV("v6", 5), TMV("v6'", 5), TMV("x", 0), TMV("x", 21), TMV("x", 1),
   TMV("x", 9), TMV("x", 3), TMV("x0", 5), TMV("x1", 5), TMV("x2", 5),
   TMV("x3", 5), TMV("x4", 5), TMV("x5", 5), TMV("x6", 5), TMC(11, 71),
   TMC(11, 73), TMC(11, 75), TMC(11, 77), TMC(11, 79), TMC(11, 81),
   TMC(11, 83), TMC(11, 85), TMC(11, 87), TMC(11, 89), TMC(11, 91),
   TMC(11, 74), TMC(11, 78), TMC(11, 80), TMC(11, 82), TMC(11, 84),
   TMC(11, 86), TMC(11, 88), TMC(12, 93), TMC(13, 95), TMC(14, 97),
   TMC(15, 2), TMC(16, 98), TMC(17, 99), TMC(17, 97), TMC(17, 98),
   TMC(17, 52), TMC(17, 55), TMC(17, 100), TMC(17, 101), TMC(17, 59),
   TMC(17, 65), TMC(17, 69), TMC(18, 97), TMC(19, 73), TMC(19, 103),
   TMC(19, 77), TMC(19, 105), TMC(19, 107), TMC(19, 109), TMC(19, 111),
   TMC(19, 113), TMC(19, 115), TMC(19, 117), TMC(19, 119), TMC(19, 121),
   TMC(19, 91), TMC(19, 74), TMC(19, 78), TMC(19, 84), TMC(19, 86),
   TMC(19, 88), TMC(20, 9), TMC(21, 0), TMC(21, 21), TMC(22, 1),
   TMC(23, 92), TMC(24, 92), TMC(25, 40), TMC(26, 9), TMC(27, 122),
   TMC(28, 9), TMC(29, 126), TMC(30, 1), TMC(31, 1), TMC(32, 96),
   TMC(33, 92), TMC(34, 37), TMC(35, 36), TMC(36, 3), TMC(37, 3),
   TMC(38, 9), TMC(39, 92), TMC(40, 1), TMC(41, 127), TMC(41, 128),
   TMC(41, 129), TMC(41, 130), TMC(41, 131), TMC(41, 132), TMC(42, 9),
   TMC(43, 1), TMC(44, 2), TMC(45, 97), TMC(46, 21), TMC(47, 0),
   TMC(48, 35), TMC(49, 34), TMC(50, 33), TMC(51, 32), TMC(52, 31),
   TMC(53, 29), TMC(54, 30), TMC(55, 29), TMC(56, 0), TMC(57, 27),
   TMC(58, 28), TMC(59, 27), TMC(60, 21), TMC(61, 0), TMC(62, 26),
   TMC(63, 20), TMC(64, 15), TMC(65, 18), TMC(66, 15), TMC(67, 10),
   TMC(68, 14), TMC(69, 10), TMC(70, 4), TMC(71, 8), TMC(72, 4),
   TMC(73, 1), TMC(74, 1), TMC(75, 0), TMC(76, 96)]
  end
  structure ThmBind = struct
    val DT = Thm.disk_thm
    val read = Term.read_raw tmvector
  end
  fun op plCommand_TY_DEF x = x
    val op plCommand_TY_DEF =
    ThmBind.DT(((("ConductORPType",0),
                [("bool",[25]),("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%121%48%160%41%108$0@%152%143%142%168@4|@$0@|@"])
  fun op plCommand_BIJ x = x
    val op plCommand_BIJ =
    ThmBind.DT(((("ConductORPType",1),
                [("ConductORPType",[0]),("bool",[116])]),["DISK_THM"]),
               [ThmBind.read"%106%97%19%112%172%177$0@3$0@|@2%96%46%110%41%108$0@%152%143%142%168@4|$0@2%111%177%172$0@3$0@2|@2"])




  fun op plCommand_size_def x = x
    val op plCommand_size_def =
    ThmBind.DT(((("ConductORPType",15),[]),[]),
               [ThmBind.read"%97%74%111%179$0@2%107@|@"])
  fun op plCommand_CASE x = x
    val op plCommand_CASE =
    ThmBind.DT(((("ConductORPType",16),[]),[]),
               [ThmBind.read"%97%74%86%60%86%62%86%64%86%66%109%178$4@$3@$2@$1@$0@2%40%146%108$0@%152%142%168@4$4@%146%108$0@%152%143%168@4$3@%146%111$0@%152%143%168@4$2@$1@3|%177$4@3|@|@|@|@|@"])
  fun op psgCommand_TY_DEF x = x
    val op psgCommand_TY_DEF =
    ThmBind.DT(((("ConductORPType",25),
                [("bool",[25]),("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%123%49%161%41%108$0@%152%143%168@3|@$0@|@"])
  fun op psgCommand_BIJ x = x
    val op psgCommand_BIJ =
    ThmBind.DT(((("ConductORPType",26),
                [("ConductORPType",[25]),("bool",[116])]),["DISK_THM"]),
               [ThmBind.read"%106%98%20%113%173%181$0@3$0@|@2%96%46%110%41%108$0@%152%143%168@3|$0@2%111%181%173$0@3$0@2|@2"])


  fun op psgCommand_size_def x = x
    val op psgCommand_size_def =
    ThmBind.DT(((("ConductORPType",38),[]),[]),
               [ThmBind.read"%98%75%111%183$0@2%107@|@"])
  fun op psgCommand_CASE x = x
    val op psgCommand_CASE =
    ThmBind.DT(((("ConductORPType",39),[]),[]),
               [ThmBind.read"%98%75%86%60%86%62%109%182$2@$1@$0@2%40%146%111$0@%107@2$2@$1@|%181$2@3|@|@|@"])
  fun op slCommand_TY_DEF x = x
    val op slCommand_TY_DEF =
    ThmBind.DT(((("ConductORPType",48),[("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%125%50%165%29%91%0%119%99%29%119%169%133%19%114$1@%19%148%107@%105$0@%140@2%41%144|@|$0@2|@2%134%20%114$1@%20%148%158%107@2%105%139@$0@2%41%144|@|$0@2|@3$1$0@2|@2$0$1@2|@|@$0@|@"])
  fun op slCommand_case_def x = x
    val op slCommand_case_def =
    ThmBind.DT(((("ConductORPType",54),
                [("ConductORPType",[49,50,51,52,53]),("bool",[26,180]),
                 ("ind_type",[33,34]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%106%97%19%87%30%89%37%109%186%153$2@2$1@$0@2$1$2@2|@|@|@2%98%20%87%30%89%37%109%186%154$2@2$1@$0@2$0$2@2|@|@|@2"])
  fun op slCommand_size_def x = x
    val op slCommand_size_def =
    ThmBind.DT(((("ConductORPType",55),
                [("ConductORPType",[49,50,51,52,53]),("bool",[26,180]),
                 ("ind_type",[33,34]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%106%97%19%111%187%153$0@3%104%152%142%168@3%179$0@3|@2%98%20%111%187%154$0@3%104%152%142%168@3%183$0@3|@2"])
  fun op slState_TY_DEF x = x
    val op slState_TY_DEF =
    ThmBind.DT(((("ConductORPType",65),
                [("bool",[25]),("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%129%52%163%41%108$0@%152%142%143%168@4|@$0@|@"])
  fun op slState_BIJ x = x
    val op slState_BIJ =
    ThmBind.DT(((("ConductORPType",66),
                [("ConductORPType",[65]),("bool",[116])]),["DISK_THM"]),
               [ThmBind.read"%106%102%22%117%175%191$0@3$0@|@2%96%46%110%41%108$0@%152%142%143%168@4|$0@2%111%191%175$0@3$0@2|@2"])





  fun op slState_size_def x = x
    val op slState_size_def =
    ThmBind.DT(((("ConductORPType",81),[]),[]),
               [ThmBind.read"%102%77%111%193$0@2%107@|@"])
  fun op slState_CASE x = x
    val op slState_CASE =
    ThmBind.DT(((("ConductORPType",82),[]),[]),
               [ThmBind.read"%102%77%86%60%86%62%86%64%86%66%86%68%109%192$5@$4@$3@$2@$1@$0@2%40%146%108$0@%152%143%168@4%146%111$0@%107@2$5@$4@2%146%108$0@%152%142%142%168@5$3@%146%111$0@%152%142%142%168@5$2@$1@3|%191$5@3|@|@|@|@|@|@"])
  fun op slOutput_TY_DEF x = x
    val op slOutput_TY_DEF =
    ThmBind.DT(((("ConductORPType",91),
                [("bool",[25]),("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%127%51%162%41%108$0@%152%142%142%142%168@5|@$0@|@"])
  fun op slOutput_BIJ x = x
    val op slOutput_BIJ =
    ThmBind.DT(((("ConductORPType",92),
                [("ConductORPType",[91]),("bool",[116])]),["DISK_THM"]),
               [ThmBind.read"%106%101%21%116%174%188$0@3$0@|@2%96%46%110%41%108$0@%152%142%142%142%168@5|$0@2%111%188%174$0@3$0@2|@2"])







  fun op slOutput_size_def x = x
    val op slOutput_size_def =
    ThmBind.DT(((("ConductORPType",109),[]),[]),
               [ThmBind.read"%101%76%111%190$0@2%107@|@"])
  fun op slOutput_CASE x = x
    val op slOutput_CASE =
    ThmBind.DT(((("ConductORPType",110),[]),[]),
               [ThmBind.read"%101%76%86%60%86%62%86%64%86%66%86%68%86%70%86%72%109%189$7@$6@$5@$4@$3@$2@$1@$0@2%40%146%108$0@%152%142%142%168@5%146%108$0@%152%142%168@4$7@%146%111$0@%152%142%168@4$6@$5@3%146%108$0@%152%143%142%168@5$4@%146%108$0@%152%142%143%168@5$3@%146%111$0@%152%142%143%168@5$2@$1@4|%188$7@3|@|@|@|@|@|@|@|@"])
  fun op stateRole_TY_DEF x = x
    val op stateRole_TY_DEF =
    ThmBind.DT(((("ConductORPType",119),
                [("bool",[25]),("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%131%53%164%41%108$0@%152%143%168@3|@$0@|@"])
  fun op stateRole_BIJ x = x
    val op stateRole_BIJ =
    ThmBind.DT(((("ConductORPType",120),
                [("ConductORPType",[119]),("bool",[116])]),["DISK_THM"]),
               [ThmBind.read"%106%103%23%118%176%194$0@3$0@|@2%96%46%110%41%108$0@%152%143%168@3|$0@2%111%194%176$0@3$0@2|@2"])


  fun op stateRole_size_def x = x
    val op stateRole_size_def =
    ThmBind.DT(((("ConductORPType",132),[]),[]),
               [ThmBind.read"%103%78%111%196$0@2%107@|@"])
  fun op stateRole_CASE x = x
    val op stateRole_CASE =
    ThmBind.DT(((("ConductORPType",133),[]),[]),
               [ThmBind.read"%103%78%86%60%86%62%109%195$2@$1@$0@2%40%146%111$0@%107@2$2@$1@|%194$2@3|@|@|@"])
  fun op num2plCommand_plCommand2num x = x
    val op num2plCommand_plCommand2num =
    ThmBind.DT(((("ConductORPType",2),
                [("ConductORPType",[1])]),["DISK_THM"]),
               [ThmBind.read"%97%19%112%172%177$0@3$0@|@"])
  fun op plCommand2num_num2plCommand x = x
    val op plCommand2num_num2plCommand =
    ThmBind.DT(((("ConductORPType",3),
                [("ConductORPType",[1])]),["DISK_THM"]),
               [ThmBind.read"%96%46%110%108$0@%152%143%142%168@5%111%177%172$0@3$0@2|@"])
  fun op num2plCommand_11 x = x
    val op num2plCommand_11 =
    ThmBind.DT(((("ConductORPType",4),
                [("ConductORPType",[1]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%96%46%96%47%119%108$1@%152%143%142%168@5%119%108$0@%152%143%142%168@5%110%112%172$1@2%172$0@3%111$1@$0@4|@|@"])
  fun op plCommand2num_11 x = x
    val op plCommand2num_11 =
    ThmBind.DT(((("ConductORPType",5),
                [("ConductORPType",[1]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%97%19%97%24%110%111%177$1@2%177$0@3%112$1@$0@2|@|@"])
  fun op num2plCommand_ONTO x = x
    val op num2plCommand_ONTO =
    ThmBind.DT(((("ConductORPType",6),
                [("ConductORPType",[1]),("bool",[25,62])]),["DISK_THM"]),
               [ThmBind.read"%97%19%132%46%106%112$1@%172$0@3%108$0@%152%143%142%168@5|@|@"])
  fun op plCommand2num_ONTO x = x
    val op plCommand2num_ONTO =
    ThmBind.DT(((("ConductORPType",7),
                [("ConductORPType",[1]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%96%46%110%108$0@%152%143%142%168@5%133%19%111$1@%177$0@2|@2|@"])
  fun op num2plCommand_thm x = x
    val op num2plCommand_thm =
    ThmBind.DT(((("ConductORPType",12),
                [("ConductORPType",[8,9,10,11])]),[]),
               [ThmBind.read"%106%112%172%107@2%185@2%106%112%172%152%142%168@4%199@2%106%112%172%152%143%168@4%171@2%112%172%152%142%142%168@5%180@4"])
  fun op plCommand2num_thm x = x
    val op plCommand2num_thm =
    ThmBind.DT(((("ConductORPType",13),
                [("ConductORPType",[3,8,9,10,11]),("bool",[25,53]),
                 ("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%106%111%177%185@2%107@2%106%111%177%199@2%152%142%168@4%106%111%177%171@2%152%143%168@4%111%177%180@2%152%142%142%168@7"])
  fun op plCommand_EQ_plCommand x = x
    val op plCommand_EQ_plCommand =
    ThmBind.DT(((("ConductORPType",14),
                [("ConductORPType",[5]),("bool",[57])]),["DISK_THM"]),
               [ThmBind.read"%97%19%97%24%110%112$1@$0@2%111%177$1@2%177$0@3|@|@"])
  fun op plCommand_case_def x = x
    val op plCommand_case_def =
    ThmBind.DT(((("ConductORPType",17),
                [("ConductORPType",[13,16]),("bool",[53,55,63]),
                 ("numeral",[3,6,7])]),["DISK_THM"]),
               [ThmBind.read"%106%86%60%86%62%86%64%86%66%109%178%185@$3@$2@$1@$0@2$3@|@|@|@|@2%106%86%60%86%62%86%64%86%66%109%178%199@$3@$2@$1@$0@2$2@|@|@|@|@2%106%86%60%86%62%86%64%86%66%109%178%171@$3@$2@$1@$0@2$1@|@|@|@|@2%86%60%86%62%86%64%86%66%109%178%180@$3@$2@$1@$0@2$0@|@|@|@|@4"])
  fun op datatype_plCommand x = x
    val op datatype_plCommand =
    ThmBind.DT(((("ConductORPType",18),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%151%44%185@%199@%171@%180@2"])
  fun op plCommand_distinct x = x
    val op plCommand_distinct =
    ThmBind.DT(((("ConductORPType",19),
                [("ConductORPType",[13,14]),
                 ("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%106%200%112%185@%199@3%106%200%112%185@%171@3%106%200%112%185@%180@3%106%200%112%199@%171@3%106%200%112%199@%180@3%200%112%171@%180@7"])
  fun op plCommand_case_cong x = x
    val op plCommand_case_cong =
    ThmBind.DT(((("ConductORPType",20),
                [("ConductORPType",[6,8,9,10,11,17]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%97%1%97%7%86%60%86%62%86%64%86%66%119%106%112$5@$4@2%106%119%112$4@%185@2%109$3@%61@3%106%119%112$4@%199@2%109$2@%63@3%106%119%112$4@%171@2%109$1@%65@3%119%112$4@%180@2%109$0@%67@7%109%178$5@$3@$2@$1@$0@2%178$4@%61@%63@%65@%67@3|@|@|@|@|@|@"])
  fun op plCommand_nchotomy x = x
    val op plCommand_nchotomy =
    ThmBind.DT(((("ConductORPType",21),
                [("ConductORPType",[6,8,9,10,11]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%97%19%169%112$0@%185@2%169%112$0@%199@2%169%112$0@%171@2%112$0@%180@4|@"])
  fun op plCommand_Axiom x = x
    val op plCommand_Axiom =
    ThmBind.DT(((("ConductORPType",22),
                [("ConductORPType",[13]),("bool",[8,14,25,53,55,63]),
                 ("numeral",[3,8])]),["DISK_THM"]),
               [ThmBind.read"%86%79%86%80%86%81%86%82%120%30%106%109$0%185@2$4@2%106%109$0%199@2$3@2%106%109$0%171@2$2@2%109$0%180@2$1@4|@|@|@|@|@"])
  fun op plCommand_induction x = x
    val op plCommand_induction =
    ThmBind.DT(((("ConductORPType",23),
                [("ConductORPType",[6,8,9,10,11]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%88%13%119%106$0%171@2%106$0%180@2%106$0%185@2$0%199@5%97%19$1$0@|@2|@"])
  fun op plCommand_distinct_clauses x = x
    val op plCommand_distinct_clauses =
    ThmBind.DT(((("ConductORPType",24),
                [("ConductORPType",[13,14]),
                 ("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%106%200%112%185@%199@3%106%200%112%185@%171@3%106%200%112%185@%180@3%106%200%112%199@%171@3%106%200%112%199@%180@3%200%112%171@%180@7"])
  fun op num2psgCommand_psgCommand2num x = x
    val op num2psgCommand_psgCommand2num =
    ThmBind.DT(((("ConductORPType",27),
                [("ConductORPType",[26])]),["DISK_THM"]),
               [ThmBind.read"%98%20%113%173%181$0@3$0@|@"])
  fun op psgCommand2num_num2psgCommand x = x
    val op psgCommand2num_num2psgCommand =
    ThmBind.DT(((("ConductORPType",28),
                [("ConductORPType",[26])]),["DISK_THM"]),
               [ThmBind.read"%96%46%110%108$0@%152%143%168@4%111%181%173$0@3$0@2|@"])
  fun op num2psgCommand_11 x = x
    val op num2psgCommand_11 =
    ThmBind.DT(((("ConductORPType",29),
                [("ConductORPType",[26]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%96%46%96%47%119%108$1@%152%143%168@4%119%108$0@%152%143%168@4%110%113%173$1@2%173$0@3%111$1@$0@4|@|@"])
  fun op psgCommand2num_11 x = x
    val op psgCommand2num_11 =
    ThmBind.DT(((("ConductORPType",30),
                [("ConductORPType",[26]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%98%20%98%25%110%111%181$1@2%181$0@3%113$1@$0@2|@|@"])
  fun op num2psgCommand_ONTO x = x
    val op num2psgCommand_ONTO =
    ThmBind.DT(((("ConductORPType",31),
                [("ConductORPType",[26]),("bool",[25,62])]),["DISK_THM"]),
               [ThmBind.read"%98%20%132%46%106%113$1@%173$0@3%108$0@%152%143%168@4|@|@"])
  fun op psgCommand2num_ONTO x = x
    val op psgCommand2num_ONTO =
    ThmBind.DT(((("ConductORPType",32),
                [("ConductORPType",[26]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%96%46%110%108$0@%152%143%168@4%134%20%111$1@%181$0@2|@2|@"])
  fun op num2psgCommand_thm x = x
    val op num2psgCommand_thm =
    ThmBind.DT(((("ConductORPType",35),[("ConductORPType",[33,34])]),[]),
               [ThmBind.read"%106%113%173%107@2%170@2%113%173%152%142%168@4%184@2"])
  fun op psgCommand2num_thm x = x
    val op psgCommand2num_thm =
    ThmBind.DT(((("ConductORPType",36),
                [("ConductORPType",[28,33,34]),("bool",[25,53]),
                 ("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%106%111%181%170@2%107@2%111%181%184@2%152%142%168@4"])
  fun op psgCommand_EQ_psgCommand x = x
    val op psgCommand_EQ_psgCommand =
    ThmBind.DT(((("ConductORPType",37),
                [("ConductORPType",[30]),("bool",[57])]),["DISK_THM"]),
               [ThmBind.read"%98%20%98%25%110%113$1@$0@2%111%181$1@2%181$0@3|@|@"])
  fun op psgCommand_case_def x = x
    val op psgCommand_case_def =
    ThmBind.DT(((("ConductORPType",40),
                [("ConductORPType",[36,39]),("bool",[55,63]),
                 ("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%106%86%60%86%62%109%182%170@$1@$0@2$1@|@|@2%86%60%86%62%109%182%184@$1@$0@2$0@|@|@2"])
  fun op datatype_psgCommand x = x
    val op datatype_psgCommand =
    ThmBind.DT(((("ConductORPType",41),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%151%45%170@%184@2"])
  fun op psgCommand_distinct x = x
    val op psgCommand_distinct =
    ThmBind.DT(((("ConductORPType",42),
                [("ConductORPType",[36,37]),
                 ("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%200%113%170@%184@2"])
  fun op psgCommand_case_cong x = x
    val op psgCommand_case_cong =
    ThmBind.DT(((("ConductORPType",43),
                [("ConductORPType",[31,33,34,40]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%98%2%98%8%86%60%86%62%119%106%113$3@$2@2%106%119%113$2@%170@2%109$1@%61@3%119%113$2@%184@2%109$0@%63@5%109%182$3@$1@$0@2%182$2@%61@%63@3|@|@|@|@"])
  fun op psgCommand_nchotomy x = x
    val op psgCommand_nchotomy =
    ThmBind.DT(((("ConductORPType",44),
                [("ConductORPType",[31,33,34]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%98%20%169%113$0@%170@2%113$0@%184@2|@"])
  fun op psgCommand_Axiom x = x
    val op psgCommand_Axiom =
    ThmBind.DT(((("ConductORPType",45),
                [("ConductORPType",[36]),("bool",[8,14,25,55,63]),
                 ("numeral",[3,8])]),["DISK_THM"]),
               [ThmBind.read"%86%79%86%80%122%31%106%109$0%170@2$2@2%109$0%184@2$1@2|@|@|@"])
  fun op psgCommand_induction x = x
    val op psgCommand_induction =
    ThmBind.DT(((("ConductORPType",46),
                [("ConductORPType",[31,33,34]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%90%14%119%106$0%170@2$0%184@3%98%20$1$0@|@2|@"])
  fun op psgCommand_distinct_clauses x = x
    val op psgCommand_distinct_clauses =
    ThmBind.DT(((("ConductORPType",47),
                [("ConductORPType",[36,37]),
                 ("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%200%113%170@%184@2"])
  fun op datatype_slCommand x = x
    val op datatype_slCommand =
    ThmBind.DT(((("ConductORPType",56),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%151%55%153@%154@2"])
  fun op slCommand_11 x = x
    val op slCommand_11 =
    ThmBind.DT(((("ConductORPType",57),
                [("ConductORPType",[49,50,51,52,53]),
                 ("bool",[26,55,62,180]),("ind_type",[33,34]),
                 ("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%106%97%19%97%24%110%115%153$1@2%153$0@3%112$1@$0@2|@|@2%98%20%98%25%110%115%154$1@2%154$0@3%113$1@$0@2|@|@2"])
  fun op slCommand_distinct x = x
    val op slCommand_distinct =
    ThmBind.DT(((("ConductORPType",58),
                [("ConductORPType",[49,50,51,52,53]),
                 ("bool",[25,26,46,53,62,180]),("ind_type",[33,34]),
                 ("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%98%25%97%19%200%115%153$0@2%154$1@3|@|@"])
  fun op slCommand_case_cong x = x
    val op slCommand_case_cong =
    ThmBind.DT(((("ConductORPType",59),
                [("ConductORPType",[49,50,51,52,53,54]),
                 ("bool",[26,180])]),["DISK_THM"]),
               [ThmBind.read"%100%3%100%9%87%30%89%37%119%106%115$3@$2@2%106%97%19%119%115$3@%153$0@3%109$2$0@2%35$0@3|@2%98%20%119%115$3@%154$0@3%109$1$0@2%38$0@3|@4%109%186$3@$1@$0@2%186$2@%35@%38@3|@|@|@|@"])
  fun op slCommand_nchotomy x = x
    val op slCommand_nchotomy =
    ThmBind.DT(((("ConductORPType",60),
                [("ConductORPType",[49,50,51,52,53]),
                 ("bool",[26,180])]),["DISK_THM"]),
               [ThmBind.read"%100%58%169%133%42%115$1@%153$0@2|@2%134%43%115$1@%154$0@2|@2|@"])
  fun op slCommand_Axiom x = x
    val op slCommand_Axiom =
    ThmBind.DT(((("ConductORPType",61),
                [("ConductORPType",[49,50,51,52,53]),("bool",[26,180]),
                 ("ind_type",[33,34]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%87%36%89%37%124%39%106%97%19%109$1%153$0@3$3$0@2|@2%98%20%109$1%154$0@3$2$0@2|@2|@|@|@"])
  fun op slCommand_induction x = x
    val op slCommand_induction =
    ThmBind.DT(((("ConductORPType",62),
                [("ConductORPType",[49,50,51,52,53]),
                 ("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%92%15%119%106%97%42$1%153$0@2|@2%98%43$1%154$0@2|@3%100%54$1$0@|@2|@"])
  fun op slCommand_distinct_clauses x = x
    val op slCommand_distinct_clauses =
    ThmBind.DT(((("ConductORPType",63),
                [("ConductORPType",[49,50,51,52,53]),
                 ("bool",[25,26,46,53,62,180]),("ind_type",[33,34]),
                 ("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%98%25%97%19%200%115%153$0@2%154$1@3|@|@"])
  fun op slCommand_one_one x = x
    val op slCommand_one_one =
    ThmBind.DT(((("ConductORPType",64),
                [("ConductORPType",[49,50,51,52,53]),
                 ("bool",[26,55,62,180]),("ind_type",[33,34]),
                 ("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%106%97%19%97%24%110%115%153$1@2%153$0@3%112$1@$0@2|@|@2%98%20%98%25%110%115%154$1@2%154$0@3%113$1@$0@2|@|@2"])
  fun op num2slState_slState2num x = x
    val op num2slState_slState2num =
    ThmBind.DT(((("ConductORPType",67),
                [("ConductORPType",[66])]),["DISK_THM"]),
               [ThmBind.read"%102%22%117%175%191$0@3$0@|@"])
  fun op slState2num_num2slState x = x
    val op slState2num_num2slState =
    ThmBind.DT(((("ConductORPType",68),
                [("ConductORPType",[66])]),["DISK_THM"]),
               [ThmBind.read"%96%46%110%108$0@%152%142%143%168@5%111%191%175$0@3$0@2|@"])
  fun op num2slState_11 x = x
    val op num2slState_11 =
    ThmBind.DT(((("ConductORPType",69),
                [("ConductORPType",[66]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%96%46%96%47%119%108$1@%152%142%143%168@5%119%108$0@%152%142%143%168@5%110%117%175$1@2%175$0@3%111$1@$0@4|@|@"])
  fun op slState2num_11 x = x
    val op slState2num_11 =
    ThmBind.DT(((("ConductORPType",70),
                [("ConductORPType",[66]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%102%22%102%27%110%111%191$1@2%191$0@3%117$1@$0@2|@|@"])
  fun op num2slState_ONTO x = x
    val op num2slState_ONTO =
    ThmBind.DT(((("ConductORPType",71),
                [("ConductORPType",[66]),("bool",[25,62])]),["DISK_THM"]),
               [ThmBind.read"%102%22%132%46%106%117$1@%175$0@3%108$0@%152%142%143%168@5|@|@"])
  fun op slState2num_ONTO x = x
    val op slState2num_ONTO =
    ThmBind.DT(((("ConductORPType",72),
                [("ConductORPType",[66]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%96%46%110%108$0@%152%142%143%168@5%136%22%111$1@%191$0@2|@2|@"])
  fun op num2slState_thm x = x
    val op num2slState_thm =
    ThmBind.DT(((("ConductORPType",78),
                [("ConductORPType",[73,74,75,76,77])]),[]),
               [ThmBind.read"%106%117%175%107@2%147@2%106%117%175%152%142%168@4%157@2%106%117%175%152%143%168@4%138@2%106%117%175%152%142%142%168@5%166@2%117%175%152%143%142%168@5%145@5"])
  fun op slState2num_thm x = x
    val op slState2num_thm =
    ThmBind.DT(((("ConductORPType",79),
                [("ConductORPType",[68,73,74,75,76,77]),("bool",[25,53]),
                 ("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%106%111%191%147@2%107@2%106%111%191%157@2%152%142%168@4%106%111%191%138@2%152%143%168@4%106%111%191%166@2%152%142%142%168@5%111%191%145@2%152%143%142%168@8"])
  fun op slState_EQ_slState x = x
    val op slState_EQ_slState =
    ThmBind.DT(((("ConductORPType",80),
                [("ConductORPType",[70]),("bool",[57])]),["DISK_THM"]),
               [ThmBind.read"%102%22%102%27%110%117$1@$0@2%111%191$1@2%191$0@3|@|@"])
  fun op slState_case_def x = x
    val op slState_case_def =
    ThmBind.DT(((("ConductORPType",83),
                [("ConductORPType",[79,82]),("bool",[53,55,63]),
                 ("numeral",[3,6,7])]),["DISK_THM"]),
               [ThmBind.read"%106%86%60%86%62%86%64%86%66%86%68%109%192%147@$4@$3@$2@$1@$0@2$4@|@|@|@|@|@2%106%86%60%86%62%86%64%86%66%86%68%109%192%157@$4@$3@$2@$1@$0@2$3@|@|@|@|@|@2%106%86%60%86%62%86%64%86%66%86%68%109%192%138@$4@$3@$2@$1@$0@2$2@|@|@|@|@|@2%106%86%60%86%62%86%64%86%66%86%68%109%192%166@$4@$3@$2@$1@$0@2$1@|@|@|@|@|@2%86%60%86%62%86%64%86%66%86%68%109%192%145@$4@$3@$2@$1@$0@2$0@|@|@|@|@|@5"])
  fun op datatype_slState x = x
    val op datatype_slState =
    ThmBind.DT(((("ConductORPType",84),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%151%57%147@%157@%138@%166@%145@2"])
  fun op slState_distinct x = x
    val op slState_distinct =
    ThmBind.DT(((("ConductORPType",85),
                [("ConductORPType",[79,80]),
                 ("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%106%200%117%147@%157@3%106%200%117%147@%138@3%106%200%117%147@%166@3%106%200%117%147@%145@3%106%200%117%157@%138@3%106%200%117%157@%166@3%106%200%117%157@%145@3%106%200%117%138@%166@3%106%200%117%138@%145@3%200%117%166@%145@11"])
  fun op slState_case_cong x = x
    val op slState_case_cong =
    ThmBind.DT(((("ConductORPType",86),
                [("ConductORPType",[71,73,74,75,76,77,83]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%102%5%102%11%86%60%86%62%86%64%86%66%86%68%119%106%117$6@$5@2%106%119%117$5@%147@2%109$4@%61@3%106%119%117$5@%157@2%109$3@%63@3%106%119%117$5@%138@2%109$2@%65@3%106%119%117$5@%166@2%109$1@%67@3%119%117$5@%145@2%109$0@%69@8%109%192$6@$4@$3@$2@$1@$0@2%192$5@%61@%63@%65@%67@%69@3|@|@|@|@|@|@|@"])
  fun op slState_nchotomy x = x
    val op slState_nchotomy =
    ThmBind.DT(((("ConductORPType",87),
                [("ConductORPType",[71,73,74,75,76,77]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%102%22%169%117$0@%147@2%169%117$0@%157@2%169%117$0@%138@2%169%117$0@%166@2%117$0@%145@5|@"])
  fun op slState_Axiom x = x
    val op slState_Axiom =
    ThmBind.DT(((("ConductORPType",88),
                [("ConductORPType",[79]),("bool",[8,14,25,53,55,63]),
                 ("numeral",[3,8])]),["DISK_THM"]),
               [ThmBind.read"%86%79%86%80%86%81%86%82%86%83%128%33%106%109$0%147@2$5@2%106%109$0%157@2$4@2%106%109$0%138@2$3@2%106%109$0%166@2$2@2%109$0%145@2$1@5|@|@|@|@|@|@"])
  fun op slState_induction x = x
    val op slState_induction =
    ThmBind.DT(((("ConductORPType",89),
                [("ConductORPType",[71,73,74,75,76,77]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%94%17%119%106$0%138@2%106$0%145@2%106$0%147@2%106$0%157@2$0%166@6%102%22$1$0@|@2|@"])
  fun op slState_distinct_clauses x = x
    val op slState_distinct_clauses =
    ThmBind.DT(((("ConductORPType",90),
                [("ConductORPType",[79,80]),
                 ("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%106%200%117%147@%157@3%106%200%117%147@%138@3%106%200%117%147@%166@3%106%200%117%147@%145@3%106%200%117%157@%138@3%106%200%117%157@%166@3%106%200%117%157@%145@3%106%200%117%138@%166@3%106%200%117%138@%145@3%200%117%166@%145@11"])
  fun op num2slOutput_slOutput2num x = x
    val op num2slOutput_slOutput2num =
    ThmBind.DT(((("ConductORPType",93),
                [("ConductORPType",[92])]),["DISK_THM"]),
               [ThmBind.read"%101%21%116%174%188$0@3$0@|@"])
  fun op slOutput2num_num2slOutput x = x
    val op slOutput2num_num2slOutput =
    ThmBind.DT(((("ConductORPType",94),
                [("ConductORPType",[92])]),["DISK_THM"]),
               [ThmBind.read"%96%46%110%108$0@%152%142%142%142%168@6%111%188%174$0@3$0@2|@"])
  fun op num2slOutput_11 x = x
    val op num2slOutput_11 =
    ThmBind.DT(((("ConductORPType",95),
                [("ConductORPType",[92]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%96%46%96%47%119%108$1@%152%142%142%142%168@6%119%108$0@%152%142%142%142%168@6%110%116%174$1@2%174$0@3%111$1@$0@4|@|@"])
  fun op slOutput2num_11 x = x
    val op slOutput2num_11 =
    ThmBind.DT(((("ConductORPType",96),
                [("ConductORPType",[92]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%101%21%101%26%110%111%188$1@2%188$0@3%116$1@$0@2|@|@"])
  fun op num2slOutput_ONTO x = x
    val op num2slOutput_ONTO =
    ThmBind.DT(((("ConductORPType",97),
                [("ConductORPType",[92]),("bool",[25,62])]),["DISK_THM"]),
               [ThmBind.read"%101%21%132%46%106%116$1@%174$0@3%108$0@%152%142%142%142%168@6|@|@"])
  fun op slOutput2num_ONTO x = x
    val op slOutput2num_ONTO =
    ThmBind.DT(((("ConductORPType",98),
                [("ConductORPType",[92]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%96%46%110%108$0@%152%142%142%142%168@6%135%21%111$1@%188$0@2|@2|@"])
  fun op num2slOutput_thm x = x
    val op num2slOutput_thm =
    ThmBind.DT(((("ConductORPType",106),
                [("ConductORPType",[99,100,101,102,103,104,105])]),[]),
               [ThmBind.read"%106%116%174%107@2%150@2%106%116%174%152%142%168@4%159@2%106%116%174%152%143%168@4%141@2%106%116%174%152%142%142%168@5%167@2%106%116%174%152%143%142%168@5%149@2%106%116%174%152%142%143%168@5%197@2%116%174%152%143%143%168@5%198@7"])
  fun op slOutput2num_thm x = x
    val op slOutput2num_thm =
    ThmBind.DT(((("ConductORPType",107),
                [("ConductORPType",[94,99,100,101,102,103,104,105]),
                 ("bool",[25]),("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%106%111%188%150@2%107@2%106%111%188%159@2%152%142%168@4%106%111%188%141@2%152%143%168@4%106%111%188%167@2%152%142%142%168@5%106%111%188%149@2%152%143%142%168@5%106%111%188%197@2%152%142%143%168@5%111%188%198@2%152%143%143%168@10"])
  fun op slOutput_EQ_slOutput x = x
    val op slOutput_EQ_slOutput =
    ThmBind.DT(((("ConductORPType",108),
                [("ConductORPType",[96]),("bool",[57])]),["DISK_THM"]),
               [ThmBind.read"%101%21%101%26%110%116$1@$0@2%111%188$1@2%188$0@3|@|@"])
  fun op slOutput_case_def x = x
    val op slOutput_case_def =
    ThmBind.DT(((("ConductORPType",111),
                [("ConductORPType",[107,110]),("bool",[53,55,63]),
                 ("numeral",[3,6,7])]),["DISK_THM"]),
               [ThmBind.read"%106%86%60%86%62%86%64%86%66%86%68%86%70%86%72%109%189%150@$6@$5@$4@$3@$2@$1@$0@2$6@|@|@|@|@|@|@|@2%106%86%60%86%62%86%64%86%66%86%68%86%70%86%72%109%189%159@$6@$5@$4@$3@$2@$1@$0@2$5@|@|@|@|@|@|@|@2%106%86%60%86%62%86%64%86%66%86%68%86%70%86%72%109%189%141@$6@$5@$4@$3@$2@$1@$0@2$4@|@|@|@|@|@|@|@2%106%86%60%86%62%86%64%86%66%86%68%86%70%86%72%109%189%167@$6@$5@$4@$3@$2@$1@$0@2$3@|@|@|@|@|@|@|@2%106%86%60%86%62%86%64%86%66%86%68%86%70%86%72%109%189%149@$6@$5@$4@$3@$2@$1@$0@2$2@|@|@|@|@|@|@|@2%106%86%60%86%62%86%64%86%66%86%68%86%70%86%72%109%189%197@$6@$5@$4@$3@$2@$1@$0@2$1@|@|@|@|@|@|@|@2%86%60%86%62%86%64%86%66%86%68%86%70%86%72%109%189%198@$6@$5@$4@$3@$2@$1@$0@2$0@|@|@|@|@|@|@|@7"])
  fun op datatype_slOutput x = x
    val op datatype_slOutput =
    ThmBind.DT(((("ConductORPType",112),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%151%56%150@%159@%141@%167@%149@%197@%198@2"])
  fun op slOutput_distinct x = x
    val op slOutput_distinct =
    ThmBind.DT(((("ConductORPType",113),
                [("ConductORPType",[107,108]),
                 ("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%106%200%116%150@%159@3%106%200%116%150@%141@3%106%200%116%150@%167@3%106%200%116%150@%149@3%106%200%116%150@%197@3%106%200%116%150@%198@3%106%200%116%159@%141@3%106%200%116%159@%167@3%106%200%116%159@%149@3%106%200%116%159@%197@3%106%200%116%159@%198@3%106%200%116%141@%167@3%106%200%116%141@%149@3%106%200%116%141@%197@3%106%200%116%141@%198@3%106%200%116%167@%149@3%106%200%116%167@%197@3%106%200%116%167@%198@3%106%200%116%149@%197@3%106%200%116%149@%198@3%200%116%197@%198@22"])
  fun op slOutput_case_cong x = x
    val op slOutput_case_cong =
    ThmBind.DT(((("ConductORPType",114),
                [("ConductORPType",[97,99,100,101,102,103,104,105,111]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%101%4%101%10%86%60%86%62%86%64%86%66%86%68%86%70%86%72%119%106%116$8@$7@2%106%119%116$7@%150@2%109$6@%61@3%106%119%116$7@%159@2%109$5@%63@3%106%119%116$7@%141@2%109$4@%65@3%106%119%116$7@%167@2%109$3@%67@3%106%119%116$7@%149@2%109$2@%69@3%106%119%116$7@%197@2%109$1@%71@3%119%116$7@%198@2%109$0@%73@10%109%189$8@$6@$5@$4@$3@$2@$1@$0@2%189$7@%61@%63@%65@%67@%69@%71@%73@3|@|@|@|@|@|@|@|@|@"])
  fun op slOutput_nchotomy x = x
    val op slOutput_nchotomy =
    ThmBind.DT(((("ConductORPType",115),
                [("ConductORPType",[97,99,100,101,102,103,104,105]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%101%21%169%116$0@%150@2%169%116$0@%159@2%169%116$0@%141@2%169%116$0@%167@2%169%116$0@%149@2%169%116$0@%197@2%116$0@%198@7|@"])
  fun op slOutput_Axiom x = x
    val op slOutput_Axiom =
    ThmBind.DT(((("ConductORPType",116),
                [("ConductORPType",[107]),("bool",[8,14,25,53,55,63]),
                 ("numeral",[3,8])]),["DISK_THM"]),
               [ThmBind.read"%86%79%86%80%86%81%86%82%86%83%86%84%86%85%126%32%106%109$0%150@2$7@2%106%109$0%159@2$6@2%106%109$0%141@2$5@2%106%109$0%167@2$4@2%106%109$0%149@2$3@2%106%109$0%197@2$2@2%109$0%198@2$1@7|@|@|@|@|@|@|@|@"])
  fun op slOutput_induction x = x
    val op slOutput_induction =
    ThmBind.DT(((("ConductORPType",117),
                [("ConductORPType",[97,99,100,101,102,103,104,105]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%93%16%119%106$0%141@2%106$0%149@2%106$0%150@2%106$0%159@2%106$0%167@2%106$0%197@2$0%198@8%101%21$1$0@|@2|@"])
  fun op slOutput_distinct_clauses x = x
    val op slOutput_distinct_clauses =
    ThmBind.DT(((("ConductORPType",118),
                [("ConductORPType",[107,108]),
                 ("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%106%200%116%150@%159@3%106%200%116%150@%141@3%106%200%116%150@%167@3%106%200%116%150@%149@3%106%200%116%150@%197@3%106%200%116%150@%198@3%106%200%116%159@%141@3%106%200%116%159@%167@3%106%200%116%159@%149@3%106%200%116%159@%197@3%106%200%116%159@%198@3%106%200%116%141@%167@3%106%200%116%141@%149@3%106%200%116%141@%197@3%106%200%116%141@%198@3%106%200%116%167@%149@3%106%200%116%167@%197@3%106%200%116%167@%198@3%106%200%116%149@%197@3%106%200%116%149@%198@3%200%116%197@%198@22"])
  fun op num2stateRole_stateRole2num x = x
    val op num2stateRole_stateRole2num =
    ThmBind.DT(((("ConductORPType",121),
                [("ConductORPType",[120])]),["DISK_THM"]),
               [ThmBind.read"%103%23%118%176%194$0@3$0@|@"])
  fun op stateRole2num_num2stateRole x = x
    val op stateRole2num_num2stateRole =
    ThmBind.DT(((("ConductORPType",122),
                [("ConductORPType",[120])]),["DISK_THM"]),
               [ThmBind.read"%96%46%110%108$0@%152%143%168@4%111%194%176$0@3$0@2|@"])
  fun op num2stateRole_11 x = x
    val op num2stateRole_11 =
    ThmBind.DT(((("ConductORPType",123),
                [("ConductORPType",[120]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%96%46%96%47%119%108$1@%152%143%168@4%119%108$0@%152%143%168@4%110%118%176$1@2%176$0@3%111$1@$0@4|@|@"])
  fun op stateRole2num_11 x = x
    val op stateRole2num_11 =
    ThmBind.DT(((("ConductORPType",124),
                [("ConductORPType",[120]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%103%23%103%28%110%111%194$1@2%194$0@3%118$1@$0@2|@|@"])
  fun op num2stateRole_ONTO x = x
    val op num2stateRole_ONTO =
    ThmBind.DT(((("ConductORPType",125),
                [("ConductORPType",[120]),("bool",[25,62])]),["DISK_THM"]),
               [ThmBind.read"%103%23%132%46%106%118$1@%176$0@3%108$0@%152%143%168@4|@|@"])
  fun op stateRole2num_ONTO x = x
    val op stateRole2num_ONTO =
    ThmBind.DT(((("ConductORPType",126),
                [("ConductORPType",[120]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%96%46%110%108$0@%152%143%168@4%137%23%111$1@%194$0@2|@2|@"])
  fun op num2stateRole_thm x = x
    val op num2stateRole_thm =
    ThmBind.DT(((("ConductORPType",129),
                [("ConductORPType",[127,128])]),[]),
               [ThmBind.read"%106%118%176%107@2%155@2%118%176%152%142%168@4%156@2"])
  fun op stateRole2num_thm x = x
    val op stateRole2num_thm =
    ThmBind.DT(((("ConductORPType",130),
                [("ConductORPType",[122,127,128]),("bool",[25,53]),
                 ("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%106%111%194%155@2%107@2%111%194%156@2%152%142%168@4"])
  fun op stateRole_EQ_stateRole x = x
    val op stateRole_EQ_stateRole =
    ThmBind.DT(((("ConductORPType",131),
                [("ConductORPType",[124]),("bool",[57])]),["DISK_THM"]),
               [ThmBind.read"%103%23%103%28%110%118$1@$0@2%111%194$1@2%194$0@3|@|@"])
  fun op stateRole_case_def x = x
    val op stateRole_case_def =
    ThmBind.DT(((("ConductORPType",134),
                [("ConductORPType",[130,133]),("bool",[55,63]),
                 ("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%106%86%60%86%62%109%195%155@$1@$0@2$1@|@|@2%86%60%86%62%109%195%156@$1@$0@2$0@|@|@2"])
  fun op datatype_stateRole x = x
    val op datatype_stateRole =
    ThmBind.DT(((("ConductORPType",135),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%151%59%155@%156@2"])
  fun op stateRole_distinct x = x
    val op stateRole_distinct =
    ThmBind.DT(((("ConductORPType",136),
                [("ConductORPType",[130,131]),
                 ("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%200%118%155@%156@2"])
  fun op stateRole_case_cong x = x
    val op stateRole_case_cong =
    ThmBind.DT(((("ConductORPType",137),
                [("ConductORPType",[125,127,128,134]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%103%6%103%12%86%60%86%62%119%106%118$3@$2@2%106%119%118$2@%155@2%109$1@%61@3%119%118$2@%156@2%109$0@%63@5%109%195$3@$1@$0@2%195$2@%61@%63@3|@|@|@|@"])
  fun op stateRole_nchotomy x = x
    val op stateRole_nchotomy =
    ThmBind.DT(((("ConductORPType",138),
                [("ConductORPType",[125,127,128]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%103%23%169%118$0@%155@2%118$0@%156@2|@"])
  fun op stateRole_Axiom x = x
    val op stateRole_Axiom =
    ThmBind.DT(((("ConductORPType",139),
                [("ConductORPType",[130]),("bool",[8,14,25,55,63]),
                 ("numeral",[3,8])]),["DISK_THM"]),
               [ThmBind.read"%86%79%86%80%130%34%106%109$0%155@2$2@2%109$0%156@2$1@2|@|@|@"])
  fun op stateRole_induction x = x
    val op stateRole_induction =
    ThmBind.DT(((("ConductORPType",140),
                [("ConductORPType",[125,127,128]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%95%18%119%106$0%155@2$0%156@3%103%23$1$0@|@2|@"])
  fun op slRole_distinct_clauses x = x
    val op slRole_distinct_clauses =
    ThmBind.DT(((("ConductORPType",141),
                [("ConductORPType",[130,131]),
                 ("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%200%118%155@%156@2"])

  val _ = DB.bindl "ConductORPType"
  [("plCommand_TY_DEF",plCommand_TY_DEF,DB.Def),
   ("plCommand_BIJ",plCommand_BIJ,DB.Def),
   ("plCommand_size_def",plCommand_size_def,DB.Def),
   ("plCommand_CASE",plCommand_CASE,DB.Def),
   ("psgCommand_TY_DEF",psgCommand_TY_DEF,DB.Def),
   ("psgCommand_BIJ",psgCommand_BIJ,DB.Def),
   ("psgCommand_size_def",psgCommand_size_def,DB.Def),
   ("psgCommand_CASE",psgCommand_CASE,DB.Def),
   ("slCommand_TY_DEF",slCommand_TY_DEF,DB.Def),
   ("slCommand_case_def",slCommand_case_def,DB.Def),
   ("slCommand_size_def",slCommand_size_def,DB.Def),
   ("slState_TY_DEF",slState_TY_DEF,DB.Def),
   ("slState_BIJ",slState_BIJ,DB.Def),
   ("slState_size_def",slState_size_def,DB.Def),
   ("slState_CASE",slState_CASE,DB.Def),
   ("slOutput_TY_DEF",slOutput_TY_DEF,DB.Def),
   ("slOutput_BIJ",slOutput_BIJ,DB.Def),
   ("slOutput_size_def",slOutput_size_def,DB.Def),
   ("slOutput_CASE",slOutput_CASE,DB.Def),
   ("stateRole_TY_DEF",stateRole_TY_DEF,DB.Def),
   ("stateRole_BIJ",stateRole_BIJ,DB.Def),
   ("stateRole_size_def",stateRole_size_def,DB.Def),
   ("stateRole_CASE",stateRole_CASE,DB.Def),
   ("num2plCommand_plCommand2num",num2plCommand_plCommand2num,DB.Thm),
   ("plCommand2num_num2plCommand",plCommand2num_num2plCommand,DB.Thm),
   ("num2plCommand_11",num2plCommand_11,DB.Thm),
   ("plCommand2num_11",plCommand2num_11,DB.Thm),
   ("num2plCommand_ONTO",num2plCommand_ONTO,DB.Thm),
   ("plCommand2num_ONTO",plCommand2num_ONTO,DB.Thm),
   ("num2plCommand_thm",num2plCommand_thm,DB.Thm),
   ("plCommand2num_thm",plCommand2num_thm,DB.Thm),
   ("plCommand_EQ_plCommand",plCommand_EQ_plCommand,DB.Thm),
   ("plCommand_case_def",plCommand_case_def,DB.Thm),
   ("datatype_plCommand",datatype_plCommand,DB.Thm),
   ("plCommand_distinct",plCommand_distinct,DB.Thm),
   ("plCommand_case_cong",plCommand_case_cong,DB.Thm),
   ("plCommand_nchotomy",plCommand_nchotomy,DB.Thm),
   ("plCommand_Axiom",plCommand_Axiom,DB.Thm),
   ("plCommand_induction",plCommand_induction,DB.Thm),
   ("plCommand_distinct_clauses",plCommand_distinct_clauses,DB.Thm),
   ("num2psgCommand_psgCommand2num",num2psgCommand_psgCommand2num,DB.Thm),
   ("psgCommand2num_num2psgCommand",psgCommand2num_num2psgCommand,DB.Thm),
   ("num2psgCommand_11",num2psgCommand_11,DB.Thm),
   ("psgCommand2num_11",psgCommand2num_11,DB.Thm),
   ("num2psgCommand_ONTO",num2psgCommand_ONTO,DB.Thm),
   ("psgCommand2num_ONTO",psgCommand2num_ONTO,DB.Thm),
   ("num2psgCommand_thm",num2psgCommand_thm,DB.Thm),
   ("psgCommand2num_thm",psgCommand2num_thm,DB.Thm),
   ("psgCommand_EQ_psgCommand",psgCommand_EQ_psgCommand,DB.Thm),
   ("psgCommand_case_def",psgCommand_case_def,DB.Thm),
   ("datatype_psgCommand",datatype_psgCommand,DB.Thm),
   ("psgCommand_distinct",psgCommand_distinct,DB.Thm),
   ("psgCommand_case_cong",psgCommand_case_cong,DB.Thm),
   ("psgCommand_nchotomy",psgCommand_nchotomy,DB.Thm),
   ("psgCommand_Axiom",psgCommand_Axiom,DB.Thm),
   ("psgCommand_induction",psgCommand_induction,DB.Thm),
   ("psgCommand_distinct_clauses",psgCommand_distinct_clauses,DB.Thm),
   ("datatype_slCommand",datatype_slCommand,DB.Thm),
   ("slCommand_11",slCommand_11,DB.Thm),
   ("slCommand_distinct",slCommand_distinct,DB.Thm),
   ("slCommand_case_cong",slCommand_case_cong,DB.Thm),
   ("slCommand_nchotomy",slCommand_nchotomy,DB.Thm),
   ("slCommand_Axiom",slCommand_Axiom,DB.Thm),
   ("slCommand_induction",slCommand_induction,DB.Thm),
   ("slCommand_distinct_clauses",slCommand_distinct_clauses,DB.Thm),
   ("slCommand_one_one",slCommand_one_one,DB.Thm),
   ("num2slState_slState2num",num2slState_slState2num,DB.Thm),
   ("slState2num_num2slState",slState2num_num2slState,DB.Thm),
   ("num2slState_11",num2slState_11,DB.Thm),
   ("slState2num_11",slState2num_11,DB.Thm),
   ("num2slState_ONTO",num2slState_ONTO,DB.Thm),
   ("slState2num_ONTO",slState2num_ONTO,DB.Thm),
   ("num2slState_thm",num2slState_thm,DB.Thm),
   ("slState2num_thm",slState2num_thm,DB.Thm),
   ("slState_EQ_slState",slState_EQ_slState,DB.Thm),
   ("slState_case_def",slState_case_def,DB.Thm),
   ("datatype_slState",datatype_slState,DB.Thm),
   ("slState_distinct",slState_distinct,DB.Thm),
   ("slState_case_cong",slState_case_cong,DB.Thm),
   ("slState_nchotomy",slState_nchotomy,DB.Thm),
   ("slState_Axiom",slState_Axiom,DB.Thm),
   ("slState_induction",slState_induction,DB.Thm),
   ("slState_distinct_clauses",slState_distinct_clauses,DB.Thm),
   ("num2slOutput_slOutput2num",num2slOutput_slOutput2num,DB.Thm),
   ("slOutput2num_num2slOutput",slOutput2num_num2slOutput,DB.Thm),
   ("num2slOutput_11",num2slOutput_11,DB.Thm),
   ("slOutput2num_11",slOutput2num_11,DB.Thm),
   ("num2slOutput_ONTO",num2slOutput_ONTO,DB.Thm),
   ("slOutput2num_ONTO",slOutput2num_ONTO,DB.Thm),
   ("num2slOutput_thm",num2slOutput_thm,DB.Thm),
   ("slOutput2num_thm",slOutput2num_thm,DB.Thm),
   ("slOutput_EQ_slOutput",slOutput_EQ_slOutput,DB.Thm),
   ("slOutput_case_def",slOutput_case_def,DB.Thm),
   ("datatype_slOutput",datatype_slOutput,DB.Thm),
   ("slOutput_distinct",slOutput_distinct,DB.Thm),
   ("slOutput_case_cong",slOutput_case_cong,DB.Thm),
   ("slOutput_nchotomy",slOutput_nchotomy,DB.Thm),
   ("slOutput_Axiom",slOutput_Axiom,DB.Thm),
   ("slOutput_induction",slOutput_induction,DB.Thm),
   ("slOutput_distinct_clauses",slOutput_distinct_clauses,DB.Thm),
   ("num2stateRole_stateRole2num",num2stateRole_stateRole2num,DB.Thm),
   ("stateRole2num_num2stateRole",stateRole2num_num2stateRole,DB.Thm),
   ("num2stateRole_11",num2stateRole_11,DB.Thm),
   ("stateRole2num_11",stateRole2num_11,DB.Thm),
   ("num2stateRole_ONTO",num2stateRole_ONTO,DB.Thm),
   ("stateRole2num_ONTO",stateRole2num_ONTO,DB.Thm),
   ("num2stateRole_thm",num2stateRole_thm,DB.Thm),
   ("stateRole2num_thm",stateRole2num_thm,DB.Thm),
   ("stateRole_EQ_stateRole",stateRole_EQ_stateRole,DB.Thm),
   ("stateRole_case_def",stateRole_case_def,DB.Thm),
   ("datatype_stateRole",datatype_stateRole,DB.Thm),
   ("stateRole_distinct",stateRole_distinct,DB.Thm),
   ("stateRole_case_cong",stateRole_case_cong,DB.Thm),
   ("stateRole_nchotomy",stateRole_nchotomy,DB.Thm),
   ("stateRole_Axiom",stateRole_Axiom,DB.Thm),
   ("stateRole_induction",stateRole_induction,DB.Thm),
   ("slRole_distinct_clauses",slRole_distinct_clauses,DB.Thm)]

  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "ConductORPType",
    thydataty = "TypeGrammarDeltas",
    read = ThmBind.read,
    data =
        "NTY14.ConductORPType,9.plCommandNTY14.ConductORPType,10.psgCommandNTY14.ConductORPType,9.slCommandNTY14.ConductORPType,7.slStateNTY14.ConductORPType,8.slOutputNTY14.ConductORPType,9.stateRole"
  }
  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "ConductORPType",
    thydataty = "TermGrammarDeltas",
    read = ThmBind.read,
    data =
        "OO13.plCommand2num4.%177OO13.num2plCommand4.%172OO6.secure4.%185OO8.withdraw4.%199OO8.complete4.%171OO12.plIncomplete4.%180OO14.plCommand_size4.%179OO14.plCommand_CASE4.%178OO4.case4.%178OO14.psgCommand2num4.%181OO14.num2psgCommand4.%173OO9.actionsIn4.%170OO13.psgIncomplete4.%184OO15.psgCommand_size4.%183OO15.psgCommand_CASE4.%182OO4.case4.%182OO2.PL4.%153OO3.PSG4.%154OO14.slCommand_CASE4.%186OO14.slCommand_size4.%187OO4.case4.%186OO11.slState2num4.%191OO11.num2slState4.%175OO11.CONDUCT_ORP4.%147OO6.SECURE4.%157OO10.ACTIONS_IN4.%138OO8.WITHDRAW4.%166OO8.COMPLETE4.%145OO12.slState_size4.%193OO12.slState_CASE4.%192OO4.case4.%192OO12.slOutput2num4.%188OO12.num2slOutput4.%174OO10.ConductORP4.%150OO6.Secure4.%159OO9.ActionsIn4.%141OO8.Withdraw4.%167OO8.Complete4.%149OO15.unAuthenticated4.%197OO12.unAuthorized4.%198OO13.slOutput_size4.%190OO13.slOutput_CASE4.%189OO4.case4.%189OO13.stateRole2num4.%194OO13.num2stateRole4.%176OO13.PlatoonLeader4.%155OO15.PlatoonSergeant4.%156OO14.stateRole_size4.%196OO14.stateRole_CASE4.%195OO4.case4.%195"
  }
  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val ConductORPType_grammars = merge_grammars ["indexedLists",
                                                "patternMatches"]
  local
  val (tyUDs, tmUDs) = GrammarDeltas.thy_deltas{thyname="ConductORPType"}
  val addtmUDs = term_grammar.add_deltas tmUDs
  val addtyUDs = type_grammar.apply_deltas tyUDs
  in
  val ConductORPType_grammars = 
    Portable.## (addtyUDs,addtmUDs) ConductORPType_grammars
  val _ = Parse.grammarDB_insert("ConductORPType",ConductORPType_grammars)
  val _ = Parse.temp_set_grammars (addtyUDs (Parse.type_grammar()), addtmUDs (Parse.term_grammar()))
  end (* addUDs local *)
  end


  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG plCommand_Axiom,
           case_def=plCommand_case_def,
           case_cong=plCommand_case_cong,
           induction=ORIG plCommand_induction,
           nchotomy=plCommand_nchotomy,
           size=SOME(Parse.Term`(ConductORPType$plCommand_size) :ConductORPType$plCommand -> num$num`,
                     ORIG plCommand_size_def),
           encode = NONE,
           lift=NONE,
           one_one=NONE,
           distinct=SOME plCommand_distinct,
           fields=let fun T t s A = mk_thy_type{Thy=t,Tyop=s,Args=A}
    val U = mk_vartype
in
[] end,
           accessors=[],
           updates=[],
           recognizers=[],
           destructors=[]}
        val tyinfo0 = EnumType.update_tyinfo num2plCommand_thm plCommand2num_thm NONE tyinfo0
        val () = computeLib.write_datatype_info tyinfo0
      in
        tyinfo0
      end
    ];


  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG psgCommand_Axiom,
           case_def=psgCommand_case_def,
           case_cong=psgCommand_case_cong,
           induction=ORIG psgCommand_induction,
           nchotomy=psgCommand_nchotomy,
           size=SOME(Parse.Term`(ConductORPType$psgCommand_size) :ConductORPType$psgCommand -> num$num`,
                     ORIG psgCommand_size_def),
           encode = NONE,
           lift=NONE,
           one_one=NONE,
           distinct=SOME psgCommand_distinct,
           fields=let fun T t s A = mk_thy_type{Thy=t,Tyop=s,Args=A}
    val U = mk_vartype
in
[] end,
           accessors=[],
           updates=[],
           recognizers=[],
           destructors=[]}
        val tyinfo0 = EnumType.update_tyinfo num2psgCommand_thm psgCommand2num_thm NONE tyinfo0
        val () = computeLib.write_datatype_info tyinfo0
      in
        tyinfo0
      end
    ];


  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG slCommand_Axiom,
           case_def=slCommand_case_def,
           case_cong=slCommand_case_cong,
           induction=ORIG slCommand_induction,
           nchotomy=slCommand_nchotomy,
           size=SOME(Parse.Term`(ConductORPType$slCommand_size) :ConductORPType$slCommand -> num$num`,
                     ORIG slCommand_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME slCommand_11,
           distinct=SOME slCommand_distinct,
           fields=let fun T t s A = mk_thy_type{Thy=t,Tyop=s,Args=A}
    val U = mk_vartype
in
[] end,
           accessors=[],
           updates=[],
           recognizers=[],
           destructors=[]}
        val tyinfo0 = tyinfo0
        val () = computeLib.write_datatype_info tyinfo0
      in
        tyinfo0
      end
    ];


  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG slState_Axiom,
           case_def=slState_case_def,
           case_cong=slState_case_cong,
           induction=ORIG slState_induction,
           nchotomy=slState_nchotomy,
           size=SOME(Parse.Term`(ConductORPType$slState_size) :ConductORPType$slState -> num$num`,
                     ORIG slState_size_def),
           encode = NONE,
           lift=NONE,
           one_one=NONE,
           distinct=SOME slState_distinct,
           fields=let fun T t s A = mk_thy_type{Thy=t,Tyop=s,Args=A}
    val U = mk_vartype
in
[] end,
           accessors=[],
           updates=[],
           recognizers=[],
           destructors=[]}
        val tyinfo0 = EnumType.update_tyinfo num2slState_thm slState2num_thm NONE tyinfo0
        val () = computeLib.write_datatype_info tyinfo0
      in
        tyinfo0
      end
    ];


  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG slOutput_Axiom,
           case_def=slOutput_case_def,
           case_cong=slOutput_case_cong,
           induction=ORIG slOutput_induction,
           nchotomy=slOutput_nchotomy,
           size=SOME(Parse.Term`(ConductORPType$slOutput_size) :ConductORPType$slOutput -> num$num`,
                     ORIG slOutput_size_def),
           encode = NONE,
           lift=NONE,
           one_one=NONE,
           distinct=SOME slOutput_distinct,
           fields=let fun T t s A = mk_thy_type{Thy=t,Tyop=s,Args=A}
    val U = mk_vartype
in
[] end,
           accessors=[],
           updates=[],
           recognizers=[],
           destructors=[]}
        val tyinfo0 = EnumType.update_tyinfo num2slOutput_thm slOutput2num_thm NONE tyinfo0
        val () = computeLib.write_datatype_info tyinfo0
      in
        tyinfo0
      end
    ];


  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG stateRole_Axiom,
           case_def=stateRole_case_def,
           case_cong=stateRole_case_cong,
           induction=ORIG stateRole_induction,
           nchotomy=stateRole_nchotomy,
           size=SOME(Parse.Term`(ConductORPType$stateRole_size) :ConductORPType$stateRole -> num$num`,
                     ORIG stateRole_size_def),
           encode = NONE,
           lift=NONE,
           one_one=NONE,
           distinct=SOME stateRole_distinct,
           fields=let fun T t s A = mk_thy_type{Thy=t,Tyop=s,Args=A}
    val U = mk_vartype
in
[] end,
           accessors=[],
           updates=[],
           recognizers=[],
           destructors=[]}
        val tyinfo0 = EnumType.update_tyinfo num2stateRole_thm stateRole2num_thm NONE tyinfo0
        val () = computeLib.write_datatype_info tyinfo0
      in
        tyinfo0
      end
    ];

val _ = if !Globals.print_thy_loads then print "done\n" else ()
val _ = Theory.load_complete "ConductORPType"
end
