structure PlanPBTypeTheory :> PlanPBTypeTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading PlanPBTypeTheory ... " else ()
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
          ("PlanPBType",
          Arbnum.fromString "1500860943",
          Arbnum.fromString "711843")
          [("indexedLists",
           Arbnum.fromString "1480536572",
           Arbnum.fromString "423707"),
           ("patternMatches",
           Arbnum.fromString "1480536620",
           Arbnum.fromString "572815")];
  val _ = Theory.incorporate_types "PlanPBType"
       [("stateRole", 0), ("slState", 0), ("slOutput", 0),
        ("slCommand", 0), ("psgCommand", 0), ("plCommand", 0)];

  val idvector = 
    let fun ID(thy,oth) = {Thy = thy, Other = oth}
    in Vector.fromList
  [ID("PlanPBType", "plCommand"), ID("PlanPBType", "slOutput"),
   ID("min", "fun"), ID("num", "num"), ID("PlanPBType", "stateRole"),
   ID("PlanPBType", "slState"), ID("PlanPBType", "slCommand"),
   ID("PlanPBType", "psgCommand"), ID("min", "bool"),
   ID("ind_type", "recspace"), ID("pair", "prod"), ID("bool", "!"),
   ID("arithmetic", "+"), ID("pair", ","), ID("bool", "/\\"),
   ID("num", "0"), ID("prim_rec", "<"), ID("min", "="), ID("min", "==>"),
   ID("bool", "?"), ID("bool", "ARB"), ID("arithmetic", "BIT1"),
   ID("arithmetic", "BIT2"), ID("ind_type", "BOTTOM"),
   ID("PlanPBType", "COMPLETE"), ID("bool", "COND"),
   ID("ind_type", "CONSTR"), ID("PlanPBType", "Complete"),
   ID("bool", "DATATYPE"), ID("PlanPBType", "INITIATE_MOVEMENT"),
   ID("PlanPBType", "InitiateMovement"), ID("arithmetic", "NUMERAL"),
   ID("PlanPBType", "PL"), ID("PlanPBType", "PSG"),
   ID("PlanPBType", "PlatoonLeader"), ID("PlanPBType", "PlatoonSergeant"),
   ID("PlanPBType", "RECEIVE_MISSION"), ID("PlanPBType", "RECON"),
   ID("PlanPBType", "ReceiveMission"), ID("PlanPBType", "Recon"),
   ID("num", "SUC"), ID("PlanPBType", "TENTATIVE_PLAN"),
   ID("bool", "TYPE_DEFINITION"), ID("PlanPBType", "TentativePlan"),
   ID("PlanPBType", "WARNO"), ID("PlanPBType", "Warno"),
   ID("arithmetic", "ZERO"), ID("bool", "\\/"),
   ID("PlanPBType", "complete"), ID("PlanPBType", "initiateMovement"),
   ID("PlanPBType", "num2plCommand"), ID("PlanPBType", "num2psgCommand"),
   ID("PlanPBType", "num2slOutput"), ID("PlanPBType", "num2slState"),
   ID("PlanPBType", "num2stateRole"), ID("PlanPBType", "plCommand2num"),
   ID("PlanPBType", "plCommand_CASE"), ID("PlanPBType", "plCommand_size"),
   ID("PlanPBType", "plIncomplete"), ID("PlanPBType", "psgCommand2num"),
   ID("PlanPBType", "psgCommand_CASE"),
   ID("PlanPBType", "psgCommand_size"), ID("PlanPBType", "psgIncomplete"),
   ID("PlanPBType", "receiveMission"), ID("PlanPBType", "recon"),
   ID("PlanPBType", "slCommand_CASE"), ID("PlanPBType", "slCommand_size"),
   ID("PlanPBType", "slOutput2num"), ID("PlanPBType", "slOutput_CASE"),
   ID("PlanPBType", "slOutput_size"), ID("PlanPBType", "slState2num"),
   ID("PlanPBType", "slState_CASE"), ID("PlanPBType", "slState_size"),
   ID("PlanPBType", "stateRole2num"), ID("PlanPBType", "stateRole_CASE"),
   ID("PlanPBType", "stateRole_size"), ID("PlanPBType", "tentativePlan"),
   ID("PlanPBType", "unAuthenticated"), ID("PlanPBType", "unAuthorized"),
   ID("PlanPBType", "warno"), ID("bool", "~")]
  end;
  local open SharingTables
  in
  val tyvector = build_type_vector idvector
  [TYOP [0], TYOP [1], TYOP [3], TYOP [4], TYOP [2, 3, 2], TYV "'a",
   TYOP [2, 5, 5], TYOP [2, 5, 6], TYOP [2, 3, 7], TYOP [5],
   TYOP [2, 9, 2], TYOP [2, 5, 7], TYOP [2, 5, 11], TYOP [2, 5, 12],
   TYOP [2, 5, 13], TYOP [2, 9, 14], TYOP [2, 1, 2], TYOP [2, 5, 14],
   TYOP [2, 5, 17], TYOP [2, 1, 18], TYOP [6], TYOP [2, 20, 2], TYOP [7],
   TYOP [2, 22, 5], TYOP [2, 23, 5], TYOP [2, 0, 5], TYOP [2, 25, 24],
   TYOP [2, 20, 26], TYOP [2, 22, 2], TYOP [2, 22, 7], TYOP [2, 0, 2],
   TYOP [2, 0, 14], TYOP [2, 2, 3], TYOP [2, 2, 9], TYOP [2, 2, 1],
   TYOP [2, 2, 22], TYOP [2, 2, 0], TYOP [2, 22, 20], TYOP [2, 0, 20],
   TYOP [8], TYOP [10, 0, 22], TYOP [9, 40], TYOP [2, 41, 39],
   TYOP [2, 0, 39], TYOP [2, 22, 39], TYOP [2, 20, 39], TYOP [2, 1, 39],
   TYOP [2, 9, 39], TYOP [2, 3, 39], TYOP [2, 1, 5], TYOP [2, 9, 5],
   TYOP [2, 3, 5], TYOP [2, 20, 5], TYOP [2, 0, 43], TYOP [2, 0, 53],
   TYOP [2, 0, 54], TYOP [2, 0, 55], TYOP [2, 0, 56], TYOP [2, 22, 44],
   TYOP [2, 20, 41], TYOP [2, 37, 39], TYOP [2, 38, 60], TYOP [2, 1, 46],
   TYOP [2, 1, 62], TYOP [2, 1, 63], TYOP [2, 1, 64], TYOP [2, 1, 65],
   TYOP [2, 1, 66], TYOP [2, 1, 67], TYOP [2, 9, 47], TYOP [2, 9, 69],
   TYOP [2, 9, 70], TYOP [2, 9, 71], TYOP [2, 9, 72], TYOP [2, 3, 48],
   TYOP [2, 5, 39], TYOP [2, 75, 39], TYOP [2, 25, 39], TYOP [2, 77, 39],
   TYOP [2, 43, 39], TYOP [2, 79, 39], TYOP [2, 23, 39], TYOP [2, 81, 39],
   TYOP [2, 44, 39], TYOP [2, 83, 39], TYOP [2, 42, 39], TYOP [2, 85, 39],
   TYOP [2, 45, 39], TYOP [2, 87, 39], TYOP [2, 46, 39], TYOP [2, 89, 39],
   TYOP [2, 47, 39], TYOP [2, 91, 39], TYOP [2, 48, 39], TYOP [2, 93, 39],
   TYOP [2, 2, 39], TYOP [2, 95, 39], TYOP [2, 2, 2], TYOP [2, 2, 97],
   TYOP [2, 22, 40], TYOP [2, 0, 99], TYOP [2, 39, 39], TYOP [2, 39, 101],
   TYOP [2, 2, 95], TYOP [2, 5, 75], TYOP [2, 41, 42], TYOP [2, 20, 45],
   TYOP [2, 30, 39], TYOP [2, 107, 39], TYOP [2, 28, 39],
   TYOP [2, 109, 39], TYOP [2, 52, 39], TYOP [2, 111, 39],
   TYOP [2, 59, 39], TYOP [2, 113, 39], TYOP [2, 49, 39],
   TYOP [2, 115, 39], TYOP [2, 16, 39], TYOP [2, 117, 39],
   TYOP [2, 50, 39], TYOP [2, 119, 39], TYOP [2, 10, 39],
   TYOP [2, 121, 39], TYOP [2, 51, 39], TYOP [2, 123, 39], TYOP [2, 4, 39],
   TYOP [2, 125, 39], TYOP [2, 39, 7], TYOP [2, 2, 41], TYOP [2, 128, 41],
   TYOP [2, 40, 129], TYOP [2, 2, 130], TYOP [2, 95, 107],
   TYOP [2, 95, 109], TYOP [2, 95, 117], TYOP [2, 95, 121],
   TYOP [2, 95, 125], TYOP [2, 42, 113]]
  end
  val _ = Theory.incorporate_consts "PlanPBType" tyvector
     [("warno", 0), ("unAuthorized", 1), ("unAuthenticated", 1),
      ("tentativePlan", 0), ("stateRole_size", 4), ("stateRole_CASE", 8),
      ("stateRole2num", 4), ("slState_size", 10), ("slState_CASE", 15),
      ("slState2num", 10), ("slOutput_size", 16), ("slOutput_CASE", 19),
      ("slOutput2num", 16), ("slCommand_size", 21), ("slCommand_CASE", 27),
      ("recon", 0), ("receiveMission", 0), ("psgIncomplete", 22),
      ("psgCommand_size", 28), ("psgCommand_CASE", 29),
      ("psgCommand2num", 28), ("plIncomplete", 0), ("plCommand_size", 30),
      ("plCommand_CASE", 31), ("plCommand2num", 30), ("num2stateRole", 32),
      ("num2slState", 33), ("num2slOutput", 34), ("num2psgCommand", 35),
      ("num2plCommand", 36), ("initiateMovement", 22), ("complete", 0),
      ("Warno", 1), ("WARNO", 9), ("TentativePlan", 1),
      ("TENTATIVE_PLAN", 9), ("Recon", 1), ("ReceiveMission", 1),
      ("RECON", 9), ("RECEIVE_MISSION", 9), ("PlatoonSergeant", 3),
      ("PlatoonLeader", 3), ("PSG", 37), ("PL", 38),
      ("InitiateMovement", 1), ("INITIATE_MOVEMENT", 9), ("Complete", 1),
      ("COMPLETE", 9)];

  local open SharingTables
  in
  val tmvector = build_term_vector idvector tyvector
  [TMV("'slCommand'", 42), TMV("M", 0), TMV("M", 22), TMV("M", 20),
   TMV("M", 1), TMV("M", 9), TMV("M", 3), TMV("M'", 0), TMV("M'", 22),
   TMV("M'", 20), TMV("M'", 1), TMV("M'", 9), TMV("M'", 3), TMV("P", 43),
   TMV("P", 44), TMV("P", 45), TMV("P", 46), TMV("P", 47), TMV("P", 48),
   TMV("a", 0), TMV("a", 22), TMV("a", 1), TMV("a", 9), TMV("a", 3),
   TMV("a'", 0), TMV("a'", 22), TMV("a'", 1), TMV("a'", 9), TMV("a'", 3),
   TMV("a0", 41), TMV("f", 25), TMV("f", 23), TMV("f", 49), TMV("f", 50),
   TMV("f", 51), TMV("f'", 25), TMV("f0", 25), TMV("f1", 23),
   TMV("f1'", 23), TMV("fn", 52), TMV("m", 2), TMV("n", 2), TMV("p", 0),
   TMV("p", 22), TMV("plCommand", 57), TMV("psgCommand", 58), TMV("r", 2),
   TMV("r'", 2), TMV("rep", 30), TMV("rep", 28), TMV("rep", 59),
   TMV("rep", 16), TMV("rep", 10), TMV("rep", 4), TMV("s", 20),
   TMV("slCommand", 61), TMV("slOutput", 68), TMV("slState", 73),
   TMV("ss", 20), TMV("stateRole", 74), TMV("v0", 5), TMV("v0'", 5),
   TMV("v1", 5), TMV("v1'", 5), TMV("v2", 5), TMV("v2'", 5), TMV("v3", 5),
   TMV("v3'", 5), TMV("v4", 5), TMV("v4'", 5), TMV("v5", 5), TMV("v5'", 5),
   TMV("v6", 5), TMV("v6'", 5), TMV("v7", 5), TMV("v7'", 5), TMV("x", 0),
   TMV("x", 22), TMV("x", 1), TMV("x", 9), TMV("x", 3), TMV("x0", 5),
   TMV("x1", 5), TMV("x2", 5), TMV("x3", 5), TMV("x4", 5), TMV("x5", 5),
   TMV("x6", 5), TMV("x7", 5), TMC(11, 76), TMC(11, 78), TMC(11, 80),
   TMC(11, 82), TMC(11, 84), TMC(11, 86), TMC(11, 88), TMC(11, 90),
   TMC(11, 92), TMC(11, 94), TMC(11, 96), TMC(11, 79), TMC(11, 83),
   TMC(11, 85), TMC(11, 87), TMC(11, 89), TMC(11, 91), TMC(11, 93),
   TMC(12, 98), TMC(13, 100), TMC(14, 102), TMC(15, 2), TMC(16, 103),
   TMC(17, 104), TMC(17, 102), TMC(17, 103), TMC(17, 53), TMC(17, 58),
   TMC(17, 105), TMC(17, 106), TMC(17, 62), TMC(17, 69), TMC(17, 74),
   TMC(18, 102), TMC(19, 78), TMC(19, 108), TMC(19, 82), TMC(19, 110),
   TMC(19, 112), TMC(19, 114), TMC(19, 116), TMC(19, 118), TMC(19, 120),
   TMC(19, 122), TMC(19, 124), TMC(19, 126), TMC(19, 96), TMC(19, 79),
   TMC(19, 83), TMC(19, 89), TMC(19, 91), TMC(19, 93), TMC(20, 0),
   TMC(20, 22), TMC(21, 97), TMC(22, 97), TMC(23, 41), TMC(24, 9),
   TMC(25, 127), TMC(26, 131), TMC(27, 1), TMC(28, 101), TMC(29, 9),
   TMC(30, 1), TMC(31, 97), TMC(32, 38), TMC(33, 37), TMC(34, 3),
   TMC(35, 3), TMC(36, 9), TMC(37, 9), TMC(38, 1), TMC(39, 1), TMC(40, 97),
   TMC(41, 9), TMC(42, 132), TMC(42, 133), TMC(42, 134), TMC(42, 135),
   TMC(42, 136), TMC(42, 137), TMC(43, 1), TMC(44, 9), TMC(45, 1),
   TMC(46, 2), TMC(47, 102), TMC(48, 0), TMC(49, 22), TMC(50, 36),
   TMC(51, 35), TMC(52, 34), TMC(53, 33), TMC(54, 32), TMC(55, 30),
   TMC(56, 31), TMC(57, 30), TMC(58, 0), TMC(59, 28), TMC(60, 29),
   TMC(61, 28), TMC(62, 22), TMC(63, 0), TMC(64, 0), TMC(65, 27),
   TMC(66, 21), TMC(67, 16), TMC(68, 19), TMC(69, 16), TMC(70, 10),
   TMC(71, 15), TMC(72, 10), TMC(73, 4), TMC(74, 8), TMC(75, 4),
   TMC(76, 0), TMC(77, 1), TMC(78, 1), TMC(79, 0), TMC(80, 101)]
  end
  structure ThmBind = struct
    val DT = Thm.disk_thm
    val read = Term.read_raw tmvector
  end
  fun op plCommand_TY_DEF x = x
    val op plCommand_TY_DEF =
    ThmBind.DT(((("PlanPBType",0),
                [("bool",[25]),("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%124%48%164%41%111$0@%153%144%144%173@4|@$0@|@"])
  fun op plCommand_BIJ x = x
    val op plCommand_BIJ =
    ThmBind.DT(((("PlanPBType",1),
                [("PlanPBType",[0]),("bool",[116])]),["DISK_THM"]),
               [ThmBind.read"%109%100%19%115%177%182$0@3$0@|@2%99%46%113%41%111$0@%153%144%144%173@4|$0@2%114%182%177$0@3$0@2|@2"])






  fun op plCommand_size_def x = x
    val op plCommand_size_def =
    ThmBind.DT(((("PlanPBType",17),[]),[]),
               [ThmBind.read"%100%76%114%184$0@2%110@|@"])
  fun op plCommand_CASE x = x
    val op plCommand_CASE =
    ThmBind.DT(((("PlanPBType",18),[]),[]),
               [ThmBind.read"%100%76%89%60%89%62%89%64%89%66%89%68%89%70%112%183$6@$5@$4@$3@$2@$1@$0@2%40%147%111$0@%153%144%173@4%147%114$0@%110@2$6@$5@2%147%111$0@%153%143%143%173@5$4@%147%111$0@%153%144%143%173@5$3@%147%114$0@%153%144%143%173@5$2@$1@4|%182$6@3|@|@|@|@|@|@|@"])
  fun op psgCommand_TY_DEF x = x
    val op psgCommand_TY_DEF =
    ThmBind.DT(((("PlanPBType",27),
                [("bool",[25]),("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%126%49%165%41%111$0@%153%144%173@3|@$0@|@"])
  fun op psgCommand_BIJ x = x
    val op psgCommand_BIJ =
    ThmBind.DT(((("PlanPBType",28),
                [("PlanPBType",[27]),("bool",[116])]),["DISK_THM"]),
               [ThmBind.read"%109%101%20%116%178%186$0@3$0@|@2%99%46%113%41%111$0@%153%144%173@3|$0@2%114%186%178$0@3$0@2|@2"])


  fun op psgCommand_size_def x = x
    val op psgCommand_size_def =
    ThmBind.DT(((("PlanPBType",40),[]),[]),
               [ThmBind.read"%101%77%114%188$0@2%110@|@"])
  fun op psgCommand_CASE x = x
    val op psgCommand_CASE =
    ThmBind.DT(((("PlanPBType",41),[]),[]),
               [ThmBind.read"%101%77%89%60%89%62%112%187$2@$1@$0@2%40%147%114$0@%110@2$2@$1@|%186$2@3|@|@|@"])
  fun op slCommand_TY_DEF x = x
    val op slCommand_TY_DEF =
    ThmBind.DT(((("PlanPBType",50),[("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%128%50%169%29%94%0%122%102%29%122%174%136%19%117$1@%19%148%110@%108$0@%142@2%41%145|@|$0@2|@2%137%20%117$1@%20%148%162%110@2%108%141@$0@2%41%145|@|$0@2|@3$1$0@2|@2$0$1@2|@|@$0@|@"])
  fun op slCommand_case_def x = x
    val op slCommand_case_def =
    ThmBind.DT(((("PlanPBType",56),
                [("PlanPBType",[51,52,53,54,55]),("bool",[26,180]),
                 ("ind_type",[33,34]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%109%100%19%90%30%92%37%112%192%154$2@2$1@$0@2$1$2@2|@|@|@2%101%20%90%30%92%37%112%192%155$2@2$1@$0@2$0$2@2|@|@|@2"])
  fun op slCommand_size_def x = x
    val op slCommand_size_def =
    ThmBind.DT(((("PlanPBType",57),
                [("PlanPBType",[51,52,53,54,55]),("bool",[26,180]),
                 ("ind_type",[33,34]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%109%100%19%114%193%154$0@3%107%153%143%173@3%184$0@3|@2%101%20%114%193%155$0@3%107%153%143%173@3%188$0@3|@2"])
  fun op slState_TY_DEF x = x
    val op slState_TY_DEF =
    ThmBind.DT(((("PlanPBType",67),
                [("bool",[25]),("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%132%52%167%41%111$0@%153%144%144%173@4|@$0@|@"])
  fun op slState_BIJ x = x
    val op slState_BIJ =
    ThmBind.DT(((("PlanPBType",68),
                [("PlanPBType",[67]),("bool",[116])]),["DISK_THM"]),
               [ThmBind.read"%109%105%22%120%180%197$0@3$0@|@2%99%46%113%41%111$0@%153%144%144%173@4|$0@2%114%197%180$0@3$0@2|@2"])






  fun op slState_size_def x = x
    val op slState_size_def =
    ThmBind.DT(((("PlanPBType",84),[]),[]),
               [ThmBind.read"%105%79%114%199$0@2%110@|@"])
  fun op slState_CASE x = x
    val op slState_CASE =
    ThmBind.DT(((("PlanPBType",85),[]),[]),
               [ThmBind.read"%105%79%89%60%89%62%89%64%89%66%89%68%89%70%112%198$6@$5@$4@$3@$2@$1@$0@2%40%147%111$0@%153%144%173@4%147%114$0@%110@2$6@$5@2%147%111$0@%153%143%143%173@5$4@%147%111$0@%153%144%143%173@5$3@%147%114$0@%153%144%143%173@5$2@$1@4|%197$6@3|@|@|@|@|@|@|@"])
  fun op slOutput_TY_DEF x = x
    val op slOutput_TY_DEF =
    ThmBind.DT(((("PlanPBType",94),
                [("bool",[25]),("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%130%51%166%41%111$0@%153%144%143%143%173@5|@$0@|@"])
  fun op slOutput_BIJ x = x
    val op slOutput_BIJ =
    ThmBind.DT(((("PlanPBType",95),
                [("PlanPBType",[94]),("bool",[116])]),["DISK_THM"]),
               [ThmBind.read"%109%104%21%119%179%194$0@3$0@|@2%99%46%113%41%111$0@%153%144%143%143%173@5|$0@2%114%194%179$0@3$0@2|@2"])








  fun op slOutput_size_def x = x
    val op slOutput_size_def =
    ThmBind.DT(((("PlanPBType",113),[]),[]),
               [ThmBind.read"%104%78%114%196$0@2%110@|@"])
  fun op slOutput_CASE x = x
    val op slOutput_CASE =
    ThmBind.DT(((("PlanPBType",114),[]),[]),
               [ThmBind.read"%104%78%89%60%89%62%89%64%89%66%89%68%89%70%89%72%89%74%112%195$8@$7@$6@$5@$4@$3@$2@$1@$0@2%40%147%111$0@%153%143%143%173@5%147%111$0@%153%143%173@4$8@%147%114$0@%153%143%173@4$7@$6@3%147%111$0@%153%143%144%173@5%147%114$0@%153%143%143%173@5$5@$4@2%147%111$0@%153%144%144%173@5$3@%147%114$0@%153%144%144%173@5$2@$1@4|%194$8@3|@|@|@|@|@|@|@|@|@"])
  fun op stateRole_TY_DEF x = x
    val op stateRole_TY_DEF =
    ThmBind.DT(((("PlanPBType",123),
                [("bool",[25]),("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%134%53%168%41%111$0@%153%144%173@3|@$0@|@"])
  fun op stateRole_BIJ x = x
    val op stateRole_BIJ =
    ThmBind.DT(((("PlanPBType",124),
                [("PlanPBType",[123]),("bool",[116])]),["DISK_THM"]),
               [ThmBind.read"%109%106%23%121%181%200$0@3$0@|@2%99%46%113%41%111$0@%153%144%173@3|$0@2%114%200%181$0@3$0@2|@2"])


  fun op stateRole_size_def x = x
    val op stateRole_size_def =
    ThmBind.DT(((("PlanPBType",136),[]),[]),
               [ThmBind.read"%106%80%114%202$0@2%110@|@"])
  fun op stateRole_CASE x = x
    val op stateRole_CASE =
    ThmBind.DT(((("PlanPBType",137),[]),[]),
               [ThmBind.read"%106%80%89%60%89%62%112%201$2@$1@$0@2%40%147%114$0@%110@2$2@$1@|%200$2@3|@|@|@"])
  fun op num2plCommand_plCommand2num x = x
    val op num2plCommand_plCommand2num =
    ThmBind.DT(((("PlanPBType",2),[("PlanPBType",[1])]),["DISK_THM"]),
               [ThmBind.read"%100%19%115%177%182$0@3$0@|@"])
  fun op plCommand2num_num2plCommand x = x
    val op plCommand2num_num2plCommand =
    ThmBind.DT(((("PlanPBType",3),[("PlanPBType",[1])]),["DISK_THM"]),
               [ThmBind.read"%99%46%113%111$0@%153%144%144%173@5%114%182%177$0@3$0@2|@"])
  fun op num2plCommand_11 x = x
    val op num2plCommand_11 =
    ThmBind.DT(((("PlanPBType",4),
                [("PlanPBType",[1]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%99%46%99%47%122%111$1@%153%144%144%173@5%122%111$0@%153%144%144%173@5%113%115%177$1@2%177$0@3%114$1@$0@4|@|@"])
  fun op plCommand2num_11 x = x
    val op plCommand2num_11 =
    ThmBind.DT(((("PlanPBType",5),
                [("PlanPBType",[1]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%100%19%100%24%113%114%182$1@2%182$0@3%115$1@$0@2|@|@"])
  fun op num2plCommand_ONTO x = x
    val op num2plCommand_ONTO =
    ThmBind.DT(((("PlanPBType",6),
                [("PlanPBType",[1]),("bool",[25,62])]),["DISK_THM"]),
               [ThmBind.read"%100%19%135%46%109%115$1@%177$0@3%111$0@%153%144%144%173@5|@|@"])
  fun op plCommand2num_ONTO x = x
    val op plCommand2num_ONTO =
    ThmBind.DT(((("PlanPBType",7),
                [("PlanPBType",[1]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%99%46%113%111$0@%153%144%144%173@5%136%19%114$1@%182$0@2|@2|@"])
  fun op num2plCommand_thm x = x
    val op num2plCommand_thm =
    ThmBind.DT(((("PlanPBType",14),[("PlanPBType",[8,9,10,11,12,13])]),[]),
               [ThmBind.read"%109%115%177%110@2%190@2%109%115%177%153%143%173@4%206@2%109%115%177%153%144%173@4%203@2%109%115%177%153%143%143%173@5%191@2%109%115%177%153%144%143%173@5%175@2%115%177%153%143%144%173@5%185@6"])
  fun op plCommand2num_thm x = x
    val op plCommand2num_thm =
    ThmBind.DT(((("PlanPBType",15),
                [("PlanPBType",[3,8,9,10,11,12,13]),("bool",[25,53]),
                 ("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%109%114%182%190@2%110@2%109%114%182%206@2%153%143%173@4%109%114%182%203@2%153%144%173@4%109%114%182%191@2%153%143%143%173@5%109%114%182%175@2%153%144%143%173@5%114%182%185@2%153%143%144%173@9"])
  fun op plCommand_EQ_plCommand x = x
    val op plCommand_EQ_plCommand =
    ThmBind.DT(((("PlanPBType",16),
                [("PlanPBType",[5]),("bool",[57])]),["DISK_THM"]),
               [ThmBind.read"%100%19%100%24%113%115$1@$0@2%114%182$1@2%182$0@3|@|@"])
  fun op plCommand_case_def x = x
    val op plCommand_case_def =
    ThmBind.DT(((("PlanPBType",19),
                [("PlanPBType",[15,18]),("bool",[53,55,63]),
                 ("numeral",[3,6,7])]),["DISK_THM"]),
               [ThmBind.read"%109%89%60%89%62%89%64%89%66%89%68%89%70%112%183%190@$5@$4@$3@$2@$1@$0@2$5@|@|@|@|@|@|@2%109%89%60%89%62%89%64%89%66%89%68%89%70%112%183%206@$5@$4@$3@$2@$1@$0@2$4@|@|@|@|@|@|@2%109%89%60%89%62%89%64%89%66%89%68%89%70%112%183%203@$5@$4@$3@$2@$1@$0@2$3@|@|@|@|@|@|@2%109%89%60%89%62%89%64%89%66%89%68%89%70%112%183%191@$5@$4@$3@$2@$1@$0@2$2@|@|@|@|@|@|@2%109%89%60%89%62%89%64%89%66%89%68%89%70%112%183%175@$5@$4@$3@$2@$1@$0@2$1@|@|@|@|@|@|@2%89%60%89%62%89%64%89%66%89%68%89%70%112%183%185@$5@$4@$3@$2@$1@$0@2$0@|@|@|@|@|@|@6"])
  fun op datatype_plCommand x = x
    val op datatype_plCommand =
    ThmBind.DT(((("PlanPBType",20),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%150%44%190@%206@%203@%191@%175@%185@2"])
  fun op plCommand_distinct x = x
    val op plCommand_distinct =
    ThmBind.DT(((("PlanPBType",21),
                [("PlanPBType",[15,16]),("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%109%207%115%190@%206@3%109%207%115%190@%203@3%109%207%115%190@%191@3%109%207%115%190@%175@3%109%207%115%190@%185@3%109%207%115%206@%203@3%109%207%115%206@%191@3%109%207%115%206@%175@3%109%207%115%206@%185@3%109%207%115%203@%191@3%109%207%115%203@%175@3%109%207%115%203@%185@3%109%207%115%191@%175@3%109%207%115%191@%185@3%207%115%175@%185@16"])
  fun op plCommand_case_cong x = x
    val op plCommand_case_cong =
    ThmBind.DT(((("PlanPBType",22),
                [("PlanPBType",[6,8,9,10,11,12,13,19]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%100%1%100%7%89%60%89%62%89%64%89%66%89%68%89%70%122%109%115$7@$6@2%109%122%115$6@%190@2%112$5@%61@3%109%122%115$6@%206@2%112$4@%63@3%109%122%115$6@%203@2%112$3@%65@3%109%122%115$6@%191@2%112$2@%67@3%109%122%115$6@%175@2%112$1@%69@3%122%115$6@%185@2%112$0@%71@9%112%183$7@$5@$4@$3@$2@$1@$0@2%183$6@%61@%63@%65@%67@%69@%71@3|@|@|@|@|@|@|@|@"])
  fun op plCommand_nchotomy x = x
    val op plCommand_nchotomy =
    ThmBind.DT(((("PlanPBType",23),
                [("PlanPBType",[6,8,9,10,11,12,13]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%100%19%174%115$0@%190@2%174%115$0@%206@2%174%115$0@%203@2%174%115$0@%191@2%174%115$0@%175@2%115$0@%185@6|@"])
  fun op plCommand_Axiom x = x
    val op plCommand_Axiom =
    ThmBind.DT(((("PlanPBType",24),
                [("PlanPBType",[15]),("bool",[8,14,25,53,55,63]),
                 ("numeral",[3,8])]),["DISK_THM"]),
               [ThmBind.read"%89%81%89%82%89%83%89%84%89%85%89%86%123%30%109%112$0%190@2$6@2%109%112$0%206@2$5@2%109%112$0%203@2$4@2%109%112$0%191@2$3@2%109%112$0%175@2$2@2%112$0%185@2$1@6|@|@|@|@|@|@|@"])
  fun op plCommand_induction x = x
    val op plCommand_induction =
    ThmBind.DT(((("PlanPBType",25),
                [("PlanPBType",[6,8,9,10,11,12,13]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%91%13%122%109$0%175@2%109$0%185@2%109$0%190@2%109$0%191@2%109$0%203@2$0%206@7%100%19$1$0@|@2|@"])
  fun op plCommand_distinct_clauses x = x
    val op plCommand_distinct_clauses =
    ThmBind.DT(((("PlanPBType",26),
                [("PlanPBType",[15,16]),("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%109%207%115%190@%206@3%109%207%115%190@%203@3%109%207%115%190@%191@3%109%207%115%190@%175@3%109%207%115%190@%185@3%109%207%115%206@%203@3%109%207%115%206@%191@3%109%207%115%206@%175@3%109%207%115%206@%185@3%109%207%115%203@%191@3%109%207%115%203@%175@3%109%207%115%203@%185@3%109%207%115%191@%175@3%109%207%115%191@%185@3%207%115%175@%185@16"])
  fun op num2psgCommand_psgCommand2num x = x
    val op num2psgCommand_psgCommand2num =
    ThmBind.DT(((("PlanPBType",29),[("PlanPBType",[28])]),["DISK_THM"]),
               [ThmBind.read"%101%20%116%178%186$0@3$0@|@"])
  fun op psgCommand2num_num2psgCommand x = x
    val op psgCommand2num_num2psgCommand =
    ThmBind.DT(((("PlanPBType",30),[("PlanPBType",[28])]),["DISK_THM"]),
               [ThmBind.read"%99%46%113%111$0@%153%144%173@4%114%186%178$0@3$0@2|@"])
  fun op num2psgCommand_11 x = x
    val op num2psgCommand_11 =
    ThmBind.DT(((("PlanPBType",31),
                [("PlanPBType",[28]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%99%46%99%47%122%111$1@%153%144%173@4%122%111$0@%153%144%173@4%113%116%178$1@2%178$0@3%114$1@$0@4|@|@"])
  fun op psgCommand2num_11 x = x
    val op psgCommand2num_11 =
    ThmBind.DT(((("PlanPBType",32),
                [("PlanPBType",[28]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%101%20%101%25%113%114%186$1@2%186$0@3%116$1@$0@2|@|@"])
  fun op num2psgCommand_ONTO x = x
    val op num2psgCommand_ONTO =
    ThmBind.DT(((("PlanPBType",33),
                [("PlanPBType",[28]),("bool",[25,62])]),["DISK_THM"]),
               [ThmBind.read"%101%20%135%46%109%116$1@%178$0@3%111$0@%153%144%173@4|@|@"])
  fun op psgCommand2num_ONTO x = x
    val op psgCommand2num_ONTO =
    ThmBind.DT(((("PlanPBType",34),
                [("PlanPBType",[28]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%99%46%113%111$0@%153%144%173@4%137%20%114$1@%186$0@2|@2|@"])
  fun op num2psgCommand_thm x = x
    val op num2psgCommand_thm =
    ThmBind.DT(((("PlanPBType",37),[("PlanPBType",[35,36])]),[]),
               [ThmBind.read"%109%116%178%110@2%176@2%116%178%153%143%173@4%189@2"])
  fun op psgCommand2num_thm x = x
    val op psgCommand2num_thm =
    ThmBind.DT(((("PlanPBType",38),
                [("PlanPBType",[30,35,36]),("bool",[25,53]),
                 ("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%109%114%186%176@2%110@2%114%186%189@2%153%143%173@4"])
  fun op psgCommand_EQ_psgCommand x = x
    val op psgCommand_EQ_psgCommand =
    ThmBind.DT(((("PlanPBType",39),
                [("PlanPBType",[32]),("bool",[57])]),["DISK_THM"]),
               [ThmBind.read"%101%20%101%25%113%116$1@$0@2%114%186$1@2%186$0@3|@|@"])
  fun op psgCommand_case_def x = x
    val op psgCommand_case_def =
    ThmBind.DT(((("PlanPBType",42),
                [("PlanPBType",[38,41]),("bool",[55,63]),
                 ("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%109%89%60%89%62%112%187%176@$1@$0@2$1@|@|@2%89%60%89%62%112%187%189@$1@$0@2$0@|@|@2"])
  fun op datatype_psgCommand x = x
    val op datatype_psgCommand =
    ThmBind.DT(((("PlanPBType",43),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%150%45%176@%189@2"])
  fun op psgCommand_distinct x = x
    val op psgCommand_distinct =
    ThmBind.DT(((("PlanPBType",44),
                [("PlanPBType",[38,39]),("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%207%116%176@%189@2"])
  fun op psgCommand_case_cong x = x
    val op psgCommand_case_cong =
    ThmBind.DT(((("PlanPBType",45),
                [("PlanPBType",[33,35,36,42]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%101%2%101%8%89%60%89%62%122%109%116$3@$2@2%109%122%116$2@%176@2%112$1@%61@3%122%116$2@%189@2%112$0@%63@5%112%187$3@$1@$0@2%187$2@%61@%63@3|@|@|@|@"])
  fun op psgCommand_nchotomy x = x
    val op psgCommand_nchotomy =
    ThmBind.DT(((("PlanPBType",46),
                [("PlanPBType",[33,35,36]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%101%20%174%116$0@%176@2%116$0@%189@2|@"])
  fun op psgCommand_Axiom x = x
    val op psgCommand_Axiom =
    ThmBind.DT(((("PlanPBType",47),
                [("PlanPBType",[38]),("bool",[8,14,25,55,63]),
                 ("numeral",[3,8])]),["DISK_THM"]),
               [ThmBind.read"%89%81%89%82%125%31%109%112$0%176@2$2@2%112$0%189@2$1@2|@|@|@"])
  fun op psgCommand_induction x = x
    val op psgCommand_induction =
    ThmBind.DT(((("PlanPBType",48),
                [("PlanPBType",[33,35,36]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%93%14%122%109$0%176@2$0%189@3%101%20$1$0@|@2|@"])
  fun op psgCommand_distinct_clauses x = x
    val op psgCommand_distinct_clauses =
    ThmBind.DT(((("PlanPBType",49),
                [("PlanPBType",[38,39]),("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%207%116%176@%189@2"])
  fun op datatype_slCommand x = x
    val op datatype_slCommand =
    ThmBind.DT(((("PlanPBType",58),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%150%55%154@%155@2"])
  fun op slCommand_11 x = x
    val op slCommand_11 =
    ThmBind.DT(((("PlanPBType",59),
                [("PlanPBType",[51,52,53,54,55]),("bool",[26,55,62,180]),
                 ("ind_type",[33,34]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%109%100%19%100%24%113%118%154$1@2%154$0@3%115$1@$0@2|@|@2%101%20%101%25%113%118%155$1@2%155$0@3%116$1@$0@2|@|@2"])
  fun op slCommand_distinct x = x
    val op slCommand_distinct =
    ThmBind.DT(((("PlanPBType",60),
                [("PlanPBType",[51,52,53,54,55]),
                 ("bool",[25,26,46,53,62,180]),("ind_type",[33,34]),
                 ("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%101%25%100%19%207%118%154$0@2%155$1@3|@|@"])
  fun op slCommand_case_cong x = x
    val op slCommand_case_cong =
    ThmBind.DT(((("PlanPBType",61),
                [("PlanPBType",[51,52,53,54,55,56]),
                 ("bool",[26,180])]),["DISK_THM"]),
               [ThmBind.read"%103%3%103%9%90%30%92%37%122%109%118$3@$2@2%109%100%19%122%118$3@%154$0@3%112$2$0@2%35$0@3|@2%101%20%122%118$3@%155$0@3%112$1$0@2%38$0@3|@4%112%192$3@$1@$0@2%192$2@%35@%38@3|@|@|@|@"])
  fun op slCommand_nchotomy x = x
    val op slCommand_nchotomy =
    ThmBind.DT(((("PlanPBType",62),
                [("PlanPBType",[51,52,53,54,55]),
                 ("bool",[26,180])]),["DISK_THM"]),
               [ThmBind.read"%103%58%174%136%42%118$1@%154$0@2|@2%137%43%118$1@%155$0@2|@2|@"])
  fun op slCommand_Axiom x = x
    val op slCommand_Axiom =
    ThmBind.DT(((("PlanPBType",63),
                [("PlanPBType",[51,52,53,54,55]),("bool",[26,180]),
                 ("ind_type",[33,34]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%90%36%92%37%127%39%109%100%19%112$1%154$0@3$3$0@2|@2%101%20%112$1%155$0@3$2$0@2|@2|@|@|@"])
  fun op slCommand_induction x = x
    val op slCommand_induction =
    ThmBind.DT(((("PlanPBType",64),
                [("PlanPBType",[51,52,53,54,55]),
                 ("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%95%15%122%109%100%42$1%154$0@2|@2%101%43$1%155$0@2|@3%103%54$1$0@|@2|@"])
  fun op slCommand_distinct_clauses x = x
    val op slCommand_distinct_clauses =
    ThmBind.DT(((("PlanPBType",65),
                [("PlanPBType",[51,52,53,54,55]),
                 ("bool",[25,26,46,53,62,180]),("ind_type",[33,34]),
                 ("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%101%25%100%19%207%118%154$0@2%155$1@3|@|@"])
  fun op slCommand_one_one x = x
    val op slCommand_one_one =
    ThmBind.DT(((("PlanPBType",66),
                [("PlanPBType",[51,52,53,54,55]),("bool",[26,55,62,180]),
                 ("ind_type",[33,34]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%109%100%19%100%24%113%118%154$1@2%154$0@3%115$1@$0@2|@|@2%101%20%101%25%113%118%155$1@2%155$0@3%116$1@$0@2|@|@2"])
  fun op num2slState_slState2num x = x
    val op num2slState_slState2num =
    ThmBind.DT(((("PlanPBType",69),[("PlanPBType",[68])]),["DISK_THM"]),
               [ThmBind.read"%105%22%120%180%197$0@3$0@|@"])
  fun op slState2num_num2slState x = x
    val op slState2num_num2slState =
    ThmBind.DT(((("PlanPBType",70),[("PlanPBType",[68])]),["DISK_THM"]),
               [ThmBind.read"%99%46%113%111$0@%153%144%144%173@5%114%197%180$0@3$0@2|@"])
  fun op num2slState_11 x = x
    val op num2slState_11 =
    ThmBind.DT(((("PlanPBType",71),
                [("PlanPBType",[68]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%99%46%99%47%122%111$1@%153%144%144%173@5%122%111$0@%153%144%144%173@5%113%120%180$1@2%180$0@3%114$1@$0@4|@|@"])
  fun op slState2num_11 x = x
    val op slState2num_11 =
    ThmBind.DT(((("PlanPBType",72),
                [("PlanPBType",[68]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%105%22%105%27%113%114%197$1@2%197$0@3%120$1@$0@2|@|@"])
  fun op num2slState_ONTO x = x
    val op num2slState_ONTO =
    ThmBind.DT(((("PlanPBType",73),
                [("PlanPBType",[68]),("bool",[25,62])]),["DISK_THM"]),
               [ThmBind.read"%105%22%135%46%109%120$1@%180$0@3%111$0@%153%144%144%173@5|@|@"])
  fun op slState2num_ONTO x = x
    val op slState2num_ONTO =
    ThmBind.DT(((("PlanPBType",74),
                [("PlanPBType",[68]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%99%46%113%111$0@%153%144%144%173@5%139%22%114$1@%197$0@2|@2|@"])
  fun op num2slState_thm x = x
    val op num2slState_thm =
    ThmBind.DT(((("PlanPBType",81),
                [("PlanPBType",[75,76,77,78,79,80])]),[]),
               [ThmBind.read"%109%120%180%110@2%158@2%109%120%180%153%143%173@4%171@2%109%120%180%153%144%173@4%163@2%109%120%180%153%143%143%173@5%151@2%109%120%180%153%144%143%173@5%159@2%120%180%153%143%144%173@5%146@6"])
  fun op slState2num_thm x = x
    val op slState2num_thm =
    ThmBind.DT(((("PlanPBType",82),
                [("PlanPBType",[70,75,76,77,78,79,80]),("bool",[25,53]),
                 ("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%109%114%197%158@2%110@2%109%114%197%171@2%153%143%173@4%109%114%197%163@2%153%144%173@4%109%114%197%151@2%153%143%143%173@5%109%114%197%159@2%153%144%143%173@5%114%197%146@2%153%143%144%173@9"])
  fun op slState_EQ_slState x = x
    val op slState_EQ_slState =
    ThmBind.DT(((("PlanPBType",83),
                [("PlanPBType",[72]),("bool",[57])]),["DISK_THM"]),
               [ThmBind.read"%105%22%105%27%113%120$1@$0@2%114%197$1@2%197$0@3|@|@"])
  fun op slState_case_def x = x
    val op slState_case_def =
    ThmBind.DT(((("PlanPBType",86),
                [("PlanPBType",[82,85]),("bool",[53,55,63]),
                 ("numeral",[3,6,7])]),["DISK_THM"]),
               [ThmBind.read"%109%89%60%89%62%89%64%89%66%89%68%89%70%112%198%158@$5@$4@$3@$2@$1@$0@2$5@|@|@|@|@|@|@2%109%89%60%89%62%89%64%89%66%89%68%89%70%112%198%171@$5@$4@$3@$2@$1@$0@2$4@|@|@|@|@|@|@2%109%89%60%89%62%89%64%89%66%89%68%89%70%112%198%163@$5@$4@$3@$2@$1@$0@2$3@|@|@|@|@|@|@2%109%89%60%89%62%89%64%89%66%89%68%89%70%112%198%151@$5@$4@$3@$2@$1@$0@2$2@|@|@|@|@|@|@2%109%89%60%89%62%89%64%89%66%89%68%89%70%112%198%159@$5@$4@$3@$2@$1@$0@2$1@|@|@|@|@|@|@2%89%60%89%62%89%64%89%66%89%68%89%70%112%198%146@$5@$4@$3@$2@$1@$0@2$0@|@|@|@|@|@|@6"])
  fun op datatype_slState x = x
    val op datatype_slState =
    ThmBind.DT(((("PlanPBType",87),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%150%57%158@%171@%163@%151@%159@%146@2"])
  fun op slState_distinct x = x
    val op slState_distinct =
    ThmBind.DT(((("PlanPBType",88),
                [("PlanPBType",[82,83]),("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%109%207%120%158@%171@3%109%207%120%158@%163@3%109%207%120%158@%151@3%109%207%120%158@%159@3%109%207%120%158@%146@3%109%207%120%171@%163@3%109%207%120%171@%151@3%109%207%120%171@%159@3%109%207%120%171@%146@3%109%207%120%163@%151@3%109%207%120%163@%159@3%109%207%120%163@%146@3%109%207%120%151@%159@3%109%207%120%151@%146@3%207%120%159@%146@16"])
  fun op slState_case_cong x = x
    val op slState_case_cong =
    ThmBind.DT(((("PlanPBType",89),
                [("PlanPBType",[73,75,76,77,78,79,80,86]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%105%5%105%11%89%60%89%62%89%64%89%66%89%68%89%70%122%109%120$7@$6@2%109%122%120$6@%158@2%112$5@%61@3%109%122%120$6@%171@2%112$4@%63@3%109%122%120$6@%163@2%112$3@%65@3%109%122%120$6@%151@2%112$2@%67@3%109%122%120$6@%159@2%112$1@%69@3%122%120$6@%146@2%112$0@%71@9%112%198$7@$5@$4@$3@$2@$1@$0@2%198$6@%61@%63@%65@%67@%69@%71@3|@|@|@|@|@|@|@|@"])
  fun op slState_nchotomy x = x
    val op slState_nchotomy =
    ThmBind.DT(((("PlanPBType",90),
                [("PlanPBType",[73,75,76,77,78,79,80]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%105%22%174%120$0@%158@2%174%120$0@%171@2%174%120$0@%163@2%174%120$0@%151@2%174%120$0@%159@2%120$0@%146@6|@"])
  fun op slState_Axiom x = x
    val op slState_Axiom =
    ThmBind.DT(((("PlanPBType",91),
                [("PlanPBType",[82]),("bool",[8,14,25,53,55,63]),
                 ("numeral",[3,8])]),["DISK_THM"]),
               [ThmBind.read"%89%81%89%82%89%83%89%84%89%85%89%86%131%33%109%112$0%158@2$6@2%109%112$0%171@2$5@2%109%112$0%163@2$4@2%109%112$0%151@2$3@2%109%112$0%159@2$2@2%112$0%146@2$1@6|@|@|@|@|@|@|@"])
  fun op slState_induction x = x
    val op slState_induction =
    ThmBind.DT(((("PlanPBType",92),
                [("PlanPBType",[73,75,76,77,78,79,80]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%97%17%122%109$0%146@2%109$0%151@2%109$0%158@2%109$0%159@2%109$0%163@2$0%171@7%105%22$1$0@|@2|@"])
  fun op slState_distinct_clauses x = x
    val op slState_distinct_clauses =
    ThmBind.DT(((("PlanPBType",93),
                [("PlanPBType",[82,83]),("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%109%207%120%158@%171@3%109%207%120%158@%163@3%109%207%120%158@%151@3%109%207%120%158@%159@3%109%207%120%158@%146@3%109%207%120%171@%163@3%109%207%120%171@%151@3%109%207%120%171@%159@3%109%207%120%171@%146@3%109%207%120%163@%151@3%109%207%120%163@%159@3%109%207%120%163@%146@3%109%207%120%151@%159@3%109%207%120%151@%146@3%207%120%159@%146@16"])
  fun op num2slOutput_slOutput2num x = x
    val op num2slOutput_slOutput2num =
    ThmBind.DT(((("PlanPBType",96),[("PlanPBType",[95])]),["DISK_THM"]),
               [ThmBind.read"%104%21%119%179%194$0@3$0@|@"])
  fun op slOutput2num_num2slOutput x = x
    val op slOutput2num_num2slOutput =
    ThmBind.DT(((("PlanPBType",97),[("PlanPBType",[95])]),["DISK_THM"]),
               [ThmBind.read"%99%46%113%111$0@%153%144%143%143%173@6%114%194%179$0@3$0@2|@"])
  fun op num2slOutput_11 x = x
    val op num2slOutput_11 =
    ThmBind.DT(((("PlanPBType",98),
                [("PlanPBType",[95]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%99%46%99%47%122%111$1@%153%144%143%143%173@6%122%111$0@%153%144%143%143%173@6%113%119%179$1@2%179$0@3%114$1@$0@4|@|@"])
  fun op slOutput2num_11 x = x
    val op slOutput2num_11 =
    ThmBind.DT(((("PlanPBType",99),
                [("PlanPBType",[95]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%104%21%104%26%113%114%194$1@2%194$0@3%119$1@$0@2|@|@"])
  fun op num2slOutput_ONTO x = x
    val op num2slOutput_ONTO =
    ThmBind.DT(((("PlanPBType",100),
                [("PlanPBType",[95]),("bool",[25,62])]),["DISK_THM"]),
               [ThmBind.read"%104%21%135%46%109%119$1@%179$0@3%111$0@%153%144%143%143%173@6|@|@"])
  fun op slOutput2num_ONTO x = x
    val op slOutput2num_ONTO =
    ThmBind.DT(((("PlanPBType",101),
                [("PlanPBType",[95]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%99%46%113%111$0@%153%144%143%143%173@6%138%21%114$1@%194$0@2|@2|@"])
  fun op num2slOutput_thm x = x
    val op num2slOutput_thm =
    ThmBind.DT(((("PlanPBType",110),
                [("PlanPBType",[102,103,104,105,106,107,108,109])]),[]),
               [ThmBind.read"%109%119%179%110@2%160@2%109%119%179%153%143%173@4%172@2%109%119%179%153%144%173@4%170@2%109%119%179%153%143%143%173@5%152@2%109%119%179%153%144%143%173@5%161@2%109%119%179%153%143%144%173@5%149@2%109%119%179%153%144%144%173@5%204@2%119%179%153%143%143%143%173@6%205@8"])
  fun op slOutput2num_thm x = x
    val op slOutput2num_thm =
    ThmBind.DT(((("PlanPBType",111),
                [("PlanPBType",[97,102,103,104,105,106,107,108,109]),
                 ("bool",[25,53]),("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%109%114%194%160@2%110@2%109%114%194%172@2%153%143%173@4%109%114%194%170@2%153%144%173@4%109%114%194%152@2%153%143%143%173@5%109%114%194%161@2%153%144%143%173@5%109%114%194%149@2%153%143%144%173@5%109%114%194%204@2%153%144%144%173@5%114%194%205@2%153%143%143%143%173@12"])
  fun op slOutput_EQ_slOutput x = x
    val op slOutput_EQ_slOutput =
    ThmBind.DT(((("PlanPBType",112),
                [("PlanPBType",[99]),("bool",[57])]),["DISK_THM"]),
               [ThmBind.read"%104%21%104%26%113%119$1@$0@2%114%194$1@2%194$0@3|@|@"])
  fun op slOutput_case_def x = x
    val op slOutput_case_def =
    ThmBind.DT(((("PlanPBType",115),
                [("PlanPBType",[111,114]),("bool",[53,55,63]),
                 ("numeral",[3,6,7])]),["DISK_THM"]),
               [ThmBind.read"%109%89%60%89%62%89%64%89%66%89%68%89%70%89%72%89%74%112%195%160@$7@$6@$5@$4@$3@$2@$1@$0@2$7@|@|@|@|@|@|@|@|@2%109%89%60%89%62%89%64%89%66%89%68%89%70%89%72%89%74%112%195%172@$7@$6@$5@$4@$3@$2@$1@$0@2$6@|@|@|@|@|@|@|@|@2%109%89%60%89%62%89%64%89%66%89%68%89%70%89%72%89%74%112%195%170@$7@$6@$5@$4@$3@$2@$1@$0@2$5@|@|@|@|@|@|@|@|@2%109%89%60%89%62%89%64%89%66%89%68%89%70%89%72%89%74%112%195%152@$7@$6@$5@$4@$3@$2@$1@$0@2$4@|@|@|@|@|@|@|@|@2%109%89%60%89%62%89%64%89%66%89%68%89%70%89%72%89%74%112%195%161@$7@$6@$5@$4@$3@$2@$1@$0@2$3@|@|@|@|@|@|@|@|@2%109%89%60%89%62%89%64%89%66%89%68%89%70%89%72%89%74%112%195%149@$7@$6@$5@$4@$3@$2@$1@$0@2$2@|@|@|@|@|@|@|@|@2%109%89%60%89%62%89%64%89%66%89%68%89%70%89%72%89%74%112%195%204@$7@$6@$5@$4@$3@$2@$1@$0@2$1@|@|@|@|@|@|@|@|@2%89%60%89%62%89%64%89%66%89%68%89%70%89%72%89%74%112%195%205@$7@$6@$5@$4@$3@$2@$1@$0@2$0@|@|@|@|@|@|@|@|@8"])
  fun op datatype_slOutput x = x
    val op datatype_slOutput =
    ThmBind.DT(((("PlanPBType",116),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%150%56%160@%172@%170@%152@%161@%149@%204@%205@2"])
  fun op slOutput_distinct x = x
    val op slOutput_distinct =
    ThmBind.DT(((("PlanPBType",117),
                [("PlanPBType",[111,112]),
                 ("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%109%207%119%160@%172@3%109%207%119%160@%170@3%109%207%119%160@%152@3%109%207%119%160@%161@3%109%207%119%160@%149@3%109%207%119%160@%204@3%109%207%119%160@%205@3%109%207%119%172@%170@3%109%207%119%172@%152@3%109%207%119%172@%161@3%109%207%119%172@%149@3%109%207%119%172@%204@3%109%207%119%172@%205@3%109%207%119%170@%152@3%109%207%119%170@%161@3%109%207%119%170@%149@3%109%207%119%170@%204@3%109%207%119%170@%205@3%109%207%119%152@%161@3%109%207%119%152@%149@3%109%207%119%152@%204@3%109%207%119%152@%205@3%109%207%119%161@%149@3%109%207%119%161@%204@3%109%207%119%161@%205@3%109%207%119%149@%204@3%109%207%119%149@%205@3%207%119%204@%205@29"])
  fun op slOutput_case_cong x = x
    val op slOutput_case_cong =
    ThmBind.DT(((("PlanPBType",118),
                [("PlanPBType",[100,102,103,104,105,106,107,108,109,115]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%104%4%104%10%89%60%89%62%89%64%89%66%89%68%89%70%89%72%89%74%122%109%119$9@$8@2%109%122%119$8@%160@2%112$7@%61@3%109%122%119$8@%172@2%112$6@%63@3%109%122%119$8@%170@2%112$5@%65@3%109%122%119$8@%152@2%112$4@%67@3%109%122%119$8@%161@2%112$3@%69@3%109%122%119$8@%149@2%112$2@%71@3%109%122%119$8@%204@2%112$1@%73@3%122%119$8@%205@2%112$0@%75@11%112%195$9@$7@$6@$5@$4@$3@$2@$1@$0@2%195$8@%61@%63@%65@%67@%69@%71@%73@%75@3|@|@|@|@|@|@|@|@|@|@"])
  fun op slOutput_nchotomy x = x
    val op slOutput_nchotomy =
    ThmBind.DT(((("PlanPBType",119),
                [("PlanPBType",[100,102,103,104,105,106,107,108,109]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%104%21%174%119$0@%160@2%174%119$0@%172@2%174%119$0@%170@2%174%119$0@%152@2%174%119$0@%161@2%174%119$0@%149@2%174%119$0@%204@2%119$0@%205@8|@"])
  fun op slOutput_Axiom x = x
    val op slOutput_Axiom =
    ThmBind.DT(((("PlanPBType",120),
                [("PlanPBType",[111]),("bool",[8,14,25,53,55,63]),
                 ("numeral",[3,8])]),["DISK_THM"]),
               [ThmBind.read"%89%81%89%82%89%83%89%84%89%85%89%86%89%87%89%88%129%32%109%112$0%160@2$8@2%109%112$0%172@2$7@2%109%112$0%170@2$6@2%109%112$0%152@2$5@2%109%112$0%161@2$4@2%109%112$0%149@2$3@2%109%112$0%204@2$2@2%112$0%205@2$1@8|@|@|@|@|@|@|@|@|@"])
  fun op slOutput_induction x = x
    val op slOutput_induction =
    ThmBind.DT(((("PlanPBType",121),
                [("PlanPBType",[100,102,103,104,105,106,107,108,109]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%96%16%122%109$0%149@2%109$0%152@2%109$0%160@2%109$0%161@2%109$0%170@2%109$0%172@2%109$0%204@2$0%205@9%104%21$1$0@|@2|@"])
  fun op slOutput_distinct_clauses x = x
    val op slOutput_distinct_clauses =
    ThmBind.DT(((("PlanPBType",122),
                [("PlanPBType",[111,112]),
                 ("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%109%207%119%160@%172@3%109%207%119%160@%170@3%109%207%119%160@%152@3%109%207%119%160@%161@3%109%207%119%160@%149@3%109%207%119%160@%204@3%109%207%119%160@%205@3%109%207%119%172@%170@3%109%207%119%172@%152@3%109%207%119%172@%161@3%109%207%119%172@%149@3%109%207%119%172@%204@3%109%207%119%172@%205@3%109%207%119%170@%152@3%109%207%119%170@%161@3%109%207%119%170@%149@3%109%207%119%170@%204@3%109%207%119%170@%205@3%109%207%119%152@%161@3%109%207%119%152@%149@3%109%207%119%152@%204@3%109%207%119%152@%205@3%109%207%119%161@%149@3%109%207%119%161@%204@3%109%207%119%161@%205@3%109%207%119%149@%204@3%109%207%119%149@%205@3%207%119%204@%205@29"])
  fun op num2stateRole_stateRole2num x = x
    val op num2stateRole_stateRole2num =
    ThmBind.DT(((("PlanPBType",125),[("PlanPBType",[124])]),["DISK_THM"]),
               [ThmBind.read"%106%23%121%181%200$0@3$0@|@"])
  fun op stateRole2num_num2stateRole x = x
    val op stateRole2num_num2stateRole =
    ThmBind.DT(((("PlanPBType",126),[("PlanPBType",[124])]),["DISK_THM"]),
               [ThmBind.read"%99%46%113%111$0@%153%144%173@4%114%200%181$0@3$0@2|@"])
  fun op num2stateRole_11 x = x
    val op num2stateRole_11 =
    ThmBind.DT(((("PlanPBType",127),
                [("PlanPBType",[124]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%99%46%99%47%122%111$1@%153%144%173@4%122%111$0@%153%144%173@4%113%121%181$1@2%181$0@3%114$1@$0@4|@|@"])
  fun op stateRole2num_11 x = x
    val op stateRole2num_11 =
    ThmBind.DT(((("PlanPBType",128),
                [("PlanPBType",[124]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%106%23%106%28%113%114%200$1@2%200$0@3%121$1@$0@2|@|@"])
  fun op num2stateRole_ONTO x = x
    val op num2stateRole_ONTO =
    ThmBind.DT(((("PlanPBType",129),
                [("PlanPBType",[124]),("bool",[25,62])]),["DISK_THM"]),
               [ThmBind.read"%106%23%135%46%109%121$1@%181$0@3%111$0@%153%144%173@4|@|@"])
  fun op stateRole2num_ONTO x = x
    val op stateRole2num_ONTO =
    ThmBind.DT(((("PlanPBType",130),
                [("PlanPBType",[124]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%99%46%113%111$0@%153%144%173@4%140%23%114$1@%200$0@2|@2|@"])
  fun op num2stateRole_thm x = x
    val op num2stateRole_thm =
    ThmBind.DT(((("PlanPBType",133),[("PlanPBType",[131,132])]),[]),
               [ThmBind.read"%109%121%181%110@2%156@2%121%181%153%143%173@4%157@2"])
  fun op stateRole2num_thm x = x
    val op stateRole2num_thm =
    ThmBind.DT(((("PlanPBType",134),
                [("PlanPBType",[126,131,132]),("bool",[25,53]),
                 ("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%109%114%200%156@2%110@2%114%200%157@2%153%143%173@4"])
  fun op stateRole_EQ_stateRole x = x
    val op stateRole_EQ_stateRole =
    ThmBind.DT(((("PlanPBType",135),
                [("PlanPBType",[128]),("bool",[57])]),["DISK_THM"]),
               [ThmBind.read"%106%23%106%28%113%121$1@$0@2%114%200$1@2%200$0@3|@|@"])
  fun op stateRole_case_def x = x
    val op stateRole_case_def =
    ThmBind.DT(((("PlanPBType",138),
                [("PlanPBType",[134,137]),("bool",[55,63]),
                 ("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%109%89%60%89%62%112%201%156@$1@$0@2$1@|@|@2%89%60%89%62%112%201%157@$1@$0@2$0@|@|@2"])
  fun op datatype_stateRole x = x
    val op datatype_stateRole =
    ThmBind.DT(((("PlanPBType",139),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%150%59%156@%157@2"])
  fun op stateRole_distinct x = x
    val op stateRole_distinct =
    ThmBind.DT(((("PlanPBType",140),
                [("PlanPBType",[134,135]),
                 ("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%207%121%156@%157@2"])
  fun op stateRole_case_cong x = x
    val op stateRole_case_cong =
    ThmBind.DT(((("PlanPBType",141),
                [("PlanPBType",[129,131,132,138]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%106%6%106%12%89%60%89%62%122%109%121$3@$2@2%109%122%121$2@%156@2%112$1@%61@3%122%121$2@%157@2%112$0@%63@5%112%201$3@$1@$0@2%201$2@%61@%63@3|@|@|@|@"])
  fun op stateRole_nchotomy x = x
    val op stateRole_nchotomy =
    ThmBind.DT(((("PlanPBType",142),
                [("PlanPBType",[129,131,132]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%106%23%174%121$0@%156@2%121$0@%157@2|@"])
  fun op stateRole_Axiom x = x
    val op stateRole_Axiom =
    ThmBind.DT(((("PlanPBType",143),
                [("PlanPBType",[134]),("bool",[8,14,25,55,63]),
                 ("numeral",[3,8])]),["DISK_THM"]),
               [ThmBind.read"%89%81%89%82%133%34%109%112$0%156@2$2@2%112$0%157@2$1@2|@|@|@"])
  fun op stateRole_induction x = x
    val op stateRole_induction =
    ThmBind.DT(((("PlanPBType",144),
                [("PlanPBType",[129,131,132]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%98%18%122%109$0%156@2$0%157@3%106%23$1$0@|@2|@"])
  fun op slRole_distinct_clauses x = x
    val op slRole_distinct_clauses =
    ThmBind.DT(((("PlanPBType",145),
                [("PlanPBType",[134,135]),
                 ("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%207%121%156@%157@2"])

  val _ = DB.bindl "PlanPBType"
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
    thy = "PlanPBType",
    thydataty = "TypeGrammarDeltas",
    read = ThmBind.read,
    data =
        "NTY10.PlanPBType,9.plCommandNTY10.PlanPBType,10.psgCommandNTY10.PlanPBType,9.slCommandNTY10.PlanPBType,7.slStateNTY10.PlanPBType,8.slOutputNTY10.PlanPBType,9.stateRole"
  }
  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "PlanPBType",
    thydataty = "TermGrammarDeltas",
    read = ThmBind.read,
    data =
        "OO13.plCommand2num4.%182OO13.num2plCommand4.%177OO14.receiveMission4.%190OO5.warno4.%206OO13.tentativePlan4.%203OO5.recon4.%191OO8.complete4.%175OO12.plIncomplete4.%185OO14.plCommand_size4.%184OO14.plCommand_CASE4.%183OO4.case4.%183OO14.psgCommand2num4.%186OO14.num2psgCommand4.%178OO16.initiateMovement4.%176OO13.psgIncomplete4.%189OO15.psgCommand_size4.%188OO15.psgCommand_CASE4.%187OO4.case4.%187OO2.PL4.%154OO3.PSG4.%155OO14.slCommand_CASE4.%192OO14.slCommand_size4.%193OO4.case4.%192OO11.slState2num4.%197OO11.num2slState4.%180OO15.RECEIVE_MISSION4.%158OO5.WARNO4.%171OO14.TENTATIVE_PLAN4.%163OO17.INITIATE_MOVEMENT4.%151OO5.RECON4.%159OO8.COMPLETE4.%146OO12.slState_size4.%199OO12.slState_CASE4.%198OO4.case4.%198OO12.slOutput2num4.%194OO12.num2slOutput4.%179OO14.ReceiveMission4.%160OO5.Warno4.%172OO13.TentativePlan4.%170OO16.InitiateMovement4.%152OO5.Recon4.%161OO8.Complete4.%149OO15.unAuthenticated4.%204OO12.unAuthorized4.%205OO13.slOutput_size4.%196OO13.slOutput_CASE4.%195OO4.case4.%195OO13.stateRole2num4.%200OO13.num2stateRole4.%181OO13.PlatoonLeader4.%156OO15.PlatoonSergeant4.%157OO14.stateRole_size4.%202OO14.stateRole_CASE4.%201OO4.case4.%201"
  }
  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val PlanPBType_grammars = merge_grammars ["indexedLists",
                                            "patternMatches"]
  local
  val (tyUDs, tmUDs) = GrammarDeltas.thy_deltas{thyname="PlanPBType"}
  val addtmUDs = term_grammar.add_deltas tmUDs
  val addtyUDs = type_grammar.apply_deltas tyUDs
  in
  val PlanPBType_grammars = 
    Portable.## (addtyUDs,addtmUDs) PlanPBType_grammars
  val _ = Parse.grammarDB_insert("PlanPBType",PlanPBType_grammars)
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
           size=SOME(Parse.Term`(PlanPBType$plCommand_size) :PlanPBType$plCommand -> num$num`,
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
           size=SOME(Parse.Term`(PlanPBType$psgCommand_size) :PlanPBType$psgCommand -> num$num`,
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
           size=SOME(Parse.Term`(PlanPBType$slCommand_size) :PlanPBType$slCommand -> num$num`,
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
           size=SOME(Parse.Term`(PlanPBType$slState_size) :PlanPBType$slState -> num$num`,
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
           size=SOME(Parse.Term`(PlanPBType$slOutput_size) :PlanPBType$slOutput -> num$num`,
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
           size=SOME(Parse.Term`(PlanPBType$stateRole_size) :PlanPBType$stateRole -> num$num`,
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
val _ = Theory.load_complete "PlanPBType"
end
