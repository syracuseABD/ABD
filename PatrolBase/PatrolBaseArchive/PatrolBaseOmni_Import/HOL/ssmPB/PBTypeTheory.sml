structure PBTypeTheory :> PBTypeTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading PBTypeTheory ... " else ()
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
          ("PBType",
          Arbnum.fromString "1500330077",
          Arbnum.fromString "425495")
          [("indexedLists",
           Arbnum.fromString "1480536572",
           Arbnum.fromString "423707"),
           ("patternMatches",
           Arbnum.fromString "1480536620",
           Arbnum.fromString "572815")];
  val _ = Theory.incorporate_types "PBType"
       [("stateRole", 0), ("slState", 0), ("slOutput", 0),
        ("slCommand", 0)];

  val idvector = 
    let fun ID(thy,oth) = {Thy = thy, Other = oth}
    in Vector.fromList
  [ID("PBType", "slOutput"), ID("min", "fun"), ID("num", "num"),
   ID("PBType", "stateRole"), ID("PBType", "slState"),
   ID("PBType", "slCommand"), ID("min", "bool"), ID("bool", "!"),
   ID("bool", "/\\"), ID("num", "0"), ID("prim_rec", "<"), ID("min", "="),
   ID("min", "==>"), ID("bool", "?"), ID("arithmetic", "BIT1"),
   ID("arithmetic", "BIT2"), ID("PBType", "COMPLETE_PB"),
   ID("bool", "COND"), ID("PBType", "CONDUCT_ORP"),
   ID("PBType", "CONDUCT_PB"), ID("PBType", "CompletePB"),
   ID("PBType", "ConductORP"), ID("PBType", "ConductPB"),
   ID("bool", "DATATYPE"), ID("PBType", "MOVE_TO_ORP"),
   ID("PBType", "MOVE_TO_PB"), ID("PBType", "MoveToORP"),
   ID("PBType", "MoveToPB"), ID("arithmetic", "NUMERAL"),
   ID("PBType", "PLAN_PB"), ID("PBType", "PlanPB"),
   ID("PBType", "PlatoonLeader"), ID("bool", "TYPE_DEFINITION"),
   ID("arithmetic", "ZERO"), ID("bool", "\\/"), ID("PBType", "completePB"),
   ID("PBType", "conductORP"), ID("PBType", "conductPB"),
   ID("PBType", "crossLD"), ID("PBType", "incomplete"),
   ID("PBType", "moveToPB"), ID("PBType", "num2slCommand"),
   ID("PBType", "num2slOutput"), ID("PBType", "num2slState"),
   ID("PBType", "num2stateRole"), ID("PBType", "slCommand2num"),
   ID("PBType", "slCommand_CASE"), ID("PBType", "slCommand_size"),
   ID("PBType", "slOutput2num"), ID("PBType", "slOutput_CASE"),
   ID("PBType", "slOutput_size"), ID("PBType", "slState2num"),
   ID("PBType", "slState_CASE"), ID("PBType", "slState_size"),
   ID("PBType", "stateRole2num"), ID("PBType", "stateRole_CASE"),
   ID("PBType", "stateRole_size"), ID("PBType", "unAuthenticated"),
   ID("PBType", "unAuthorized"), ID("bool", "~")]
  end;
  local open SharingTables
  in
  val tyvector = build_type_vector idvector
  [TYOP [0], TYOP [2], TYOP [3], TYOP [1, 2, 1], TYV "'a", TYOP [1, 4, 4],
   TYOP [1, 2, 5], TYOP [4], TYOP [1, 7, 1], TYOP [1, 4, 5],
   TYOP [1, 4, 9], TYOP [1, 4, 10], TYOP [1, 4, 11], TYOP [1, 4, 12],
   TYOP [1, 7, 13], TYOP [1, 0, 1], TYOP [1, 4, 13], TYOP [1, 4, 16],
   TYOP [1, 0, 17], TYOP [5], TYOP [1, 19, 1], TYOP [1, 19, 13],
   TYOP [1, 1, 2], TYOP [1, 1, 7], TYOP [1, 1, 0], TYOP [1, 1, 19],
   TYOP [6], TYOP [1, 19, 26], TYOP [1, 0, 26], TYOP [1, 7, 26],
   TYOP [1, 2, 26], TYOP [1, 19, 4], TYOP [1, 0, 4], TYOP [1, 7, 4],
   TYOP [1, 2, 4], TYOP [1, 19, 27], TYOP [1, 19, 35], TYOP [1, 19, 36],
   TYOP [1, 19, 37], TYOP [1, 19, 38], TYOP [1, 0, 28], TYOP [1, 0, 40],
   TYOP [1, 0, 41], TYOP [1, 0, 42], TYOP [1, 0, 43], TYOP [1, 0, 44],
   TYOP [1, 0, 45], TYOP [1, 7, 29], TYOP [1, 7, 47], TYOP [1, 7, 48],
   TYOP [1, 7, 49], TYOP [1, 7, 50], TYOP [1, 4, 26], TYOP [1, 52, 26],
   TYOP [1, 27, 26], TYOP [1, 54, 26], TYOP [1, 28, 26], TYOP [1, 56, 26],
   TYOP [1, 29, 26], TYOP [1, 58, 26], TYOP [1, 30, 26], TYOP [1, 60, 26],
   TYOP [1, 1, 26], TYOP [1, 62, 26], TYOP [1, 26, 26], TYOP [1, 26, 64],
   TYOP [1, 1, 62], TYOP [1, 4, 52], TYOP [1, 2, 30], TYOP [1, 31, 26],
   TYOP [1, 69, 26], TYOP [1, 20, 26], TYOP [1, 71, 26], TYOP [1, 32, 26],
   TYOP [1, 73, 26], TYOP [1, 15, 26], TYOP [1, 75, 26], TYOP [1, 33, 26],
   TYOP [1, 77, 26], TYOP [1, 8, 26], TYOP [1, 79, 26], TYOP [1, 34, 26],
   TYOP [1, 81, 26], TYOP [1, 3, 26], TYOP [1, 83, 26], TYOP [1, 1, 1],
   TYOP [1, 26, 9], TYOP [1, 62, 71], TYOP [1, 62, 75], TYOP [1, 62, 79],
   TYOP [1, 62, 83]]
  end
  val _ = Theory.incorporate_consts "PBType" tyvector
     [("unAuthorized", 0), ("unAuthenticated", 0), ("stateRole_size", 3),
      ("stateRole_CASE", 6), ("stateRole2num", 3), ("slState_size", 8),
      ("slState_CASE", 14), ("slState2num", 8), ("slOutput_size", 15),
      ("slOutput_CASE", 18), ("slOutput2num", 15), ("slCommand_size", 20),
      ("slCommand_CASE", 21), ("slCommand2num", 20), ("num2stateRole", 22),
      ("num2slState", 23), ("num2slOutput", 24), ("num2slCommand", 25),
      ("moveToPB", 19), ("incomplete", 19), ("crossLD", 19),
      ("conductPB", 19), ("conductORP", 19), ("completePB", 19),
      ("PlatoonLeader", 2), ("PlanPB", 0), ("PLAN_PB", 7), ("MoveToPB", 0),
      ("MoveToORP", 0), ("MOVE_TO_PB", 7), ("MOVE_TO_ORP", 7),
      ("ConductPB", 0), ("ConductORP", 0), ("CompletePB", 0),
      ("CONDUCT_PB", 7), ("CONDUCT_ORP", 7), ("COMPLETE_PB", 7)];

  local open SharingTables
  in
  val tmvector = build_term_vector idvector tyvector
  [TMV("M", 19), TMV("M", 0), TMV("M", 7), TMV("M", 2), TMV("M'", 19),
   TMV("M'", 0), TMV("M'", 7), TMV("M'", 2), TMV("P", 27), TMV("P", 28),
   TMV("P", 29), TMV("P", 30), TMV("a", 19), TMV("a", 0), TMV("a", 7),
   TMV("a", 2), TMV("a'", 19), TMV("a'", 0), TMV("a'", 7), TMV("a'", 2),
   TMV("f", 31), TMV("f", 32), TMV("f", 33), TMV("f", 34), TMV("m", 1),
   TMV("n", 1), TMV("r", 1), TMV("r'", 1), TMV("rep", 20), TMV("rep", 15),
   TMV("rep", 8), TMV("rep", 3), TMV("slCommand", 39), TMV("slOutput", 46),
   TMV("slState", 51), TMV("stateRole", 30), TMV("v0", 4), TMV("v0'", 4),
   TMV("v1", 4), TMV("v1'", 4), TMV("v2", 4), TMV("v2'", 4), TMV("v3", 4),
   TMV("v3'", 4), TMV("v4", 4), TMV("v4'", 4), TMV("v5", 4), TMV("v5'", 4),
   TMV("v6", 4), TMV("v6'", 4), TMV("v7", 4), TMV("v7'", 4), TMV("x", 19),
   TMV("x", 0), TMV("x", 7), TMV("x", 2), TMV("x0", 4), TMV("x1", 4),
   TMV("x2", 4), TMV("x3", 4), TMV("x4", 4), TMV("x5", 4), TMV("x6", 4),
   TMV("x7", 4), TMC(7, 53), TMC(7, 55), TMC(7, 57), TMC(7, 59),
   TMC(7, 61), TMC(7, 63), TMC(7, 54), TMC(7, 56), TMC(7, 58), TMC(7, 60),
   TMC(8, 65), TMC(9, 1), TMC(10, 66), TMC(11, 67), TMC(11, 65),
   TMC(11, 66), TMC(11, 35), TMC(11, 40), TMC(11, 47), TMC(11, 68),
   TMC(12, 65), TMC(13, 70), TMC(13, 72), TMC(13, 74), TMC(13, 76),
   TMC(13, 78), TMC(13, 80), TMC(13, 82), TMC(13, 84), TMC(13, 63),
   TMC(13, 54), TMC(13, 56), TMC(13, 58), TMC(13, 60), TMC(14, 85),
   TMC(15, 85), TMC(16, 7), TMC(17, 86), TMC(18, 7), TMC(19, 7),
   TMC(20, 0), TMC(21, 0), TMC(22, 0), TMC(23, 64), TMC(24, 7), TMC(25, 7),
   TMC(26, 0), TMC(27, 0), TMC(28, 85), TMC(29, 7), TMC(30, 0), TMC(31, 2),
   TMC(32, 87), TMC(32, 88), TMC(32, 89), TMC(32, 90), TMC(33, 1),
   TMC(34, 65), TMC(35, 19), TMC(36, 19), TMC(37, 19), TMC(38, 19),
   TMC(39, 19), TMC(40, 19), TMC(41, 25), TMC(42, 24), TMC(43, 23),
   TMC(44, 22), TMC(45, 20), TMC(46, 21), TMC(47, 20), TMC(48, 15),
   TMC(49, 18), TMC(50, 15), TMC(51, 8), TMC(52, 14), TMC(53, 8),
   TMC(54, 3), TMC(55, 6), TMC(56, 3), TMC(57, 0), TMC(58, 0), TMC(59, 64)]
  end
  structure ThmBind = struct
    val DT = Thm.disk_thm
    val read = Term.read_raw tmvector
  end
  fun op slCommand_TY_DEF x = x
    val op slCommand_TY_DEF =
    ThmBind.DT(((("PBType",0),
                [("bool",[25]),("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%86%28%116%25%76$0@%112%99%99%120@4|@$0@|@"])
  fun op slCommand_BIJ x = x
    val op slCommand_BIJ =
    ThmBind.DT(((("PBType",1),
                [("PBType",[0]),("bool",[116])]),["DISK_THM"]),
               [ThmBind.read"%74%70%12%80%128%132$0@3$0@|@2%69%26%78%25%76$0@%112%99%99%120@4|$0@2%79%132%128$0@3$0@2|@2"])






  fun op slCommand_size_def x = x
    val op slCommand_size_def =
    ThmBind.DT(((("PBType",17),[]),[]),
               [ThmBind.read"%70%52%79%134$0@2%75@|@"])
  fun op slCommand_CASE x = x
    val op slCommand_CASE =
    ThmBind.DT(((("PBType",18),[]),[]),
               [ThmBind.read"%70%52%64%36%64%38%64%40%64%42%64%44%64%46%77%133$6@$5@$4@$3@$2@$1@$0@2%24%101%76$0@%112%99%120@4%101%79$0@%75@2$6@$5@2%101%76$0@%112%98%98%120@5$4@%101%76$0@%112%99%98%120@5$3@%101%79$0@%112%99%98%120@5$2@$1@4|%132$6@3|@|@|@|@|@|@|@"])
  fun op slState_TY_DEF x = x
    val op slState_TY_DEF =
    ThmBind.DT(((("PBType",27),
                [("bool",[25]),("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%90%30%118%25%76$0@%112%99%99%120@4|@$0@|@"])
  fun op slState_BIJ x = x
    val op slState_BIJ =
    ThmBind.DT(((("PBType",28),
                [("PBType",[27]),("bool",[116])]),["DISK_THM"]),
               [ThmBind.read"%74%72%14%82%130%138$0@3$0@|@2%69%26%78%25%76$0@%112%99%99%120@4|$0@2%79%138%130$0@3$0@2|@2"])






  fun op slState_size_def x = x
    val op slState_size_def =
    ThmBind.DT(((("PBType",44),[]),[]),
               [ThmBind.read"%72%54%79%140$0@2%75@|@"])
  fun op slState_CASE x = x
    val op slState_CASE =
    ThmBind.DT(((("PBType",45),[]),[]),
               [ThmBind.read"%72%54%64%36%64%38%64%40%64%42%64%44%64%46%77%139$6@$5@$4@$3@$2@$1@$0@2%24%101%76$0@%112%99%120@4%101%79$0@%75@2$6@$5@2%101%76$0@%112%98%98%120@5$4@%101%76$0@%112%99%98%120@5$3@%101%79$0@%112%99%98%120@5$2@$1@4|%138$6@3|@|@|@|@|@|@|@"])
  fun op slOutput_TY_DEF x = x
    val op slOutput_TY_DEF =
    ThmBind.DT(((("PBType",54),
                [("bool",[25]),("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%88%29%117%25%76$0@%112%99%98%98%120@5|@$0@|@"])
  fun op slOutput_BIJ x = x
    val op slOutput_BIJ =
    ThmBind.DT(((("PBType",55),
                [("PBType",[54]),("bool",[116])]),["DISK_THM"]),
               [ThmBind.read"%74%71%13%81%129%135$0@3$0@|@2%69%26%78%25%76$0@%112%99%98%98%120@5|$0@2%79%135%129$0@3$0@2|@2"])








  fun op slOutput_size_def x = x
    val op slOutput_size_def =
    ThmBind.DT(((("PBType",73),[]),[]),
               [ThmBind.read"%71%53%79%137$0@2%75@|@"])
  fun op slOutput_CASE x = x
    val op slOutput_CASE =
    ThmBind.DT(((("PBType",74),[]),[]),
               [ThmBind.read"%71%53%64%36%64%38%64%40%64%42%64%44%64%46%64%48%64%50%77%136$8@$7@$6@$5@$4@$3@$2@$1@$0@2%24%101%76$0@%112%98%98%120@5%101%76$0@%112%98%120@4$8@%101%79$0@%112%98%120@4$7@$6@3%101%76$0@%112%98%99%120@5%101%79$0@%112%98%98%120@5$5@$4@2%101%76$0@%112%99%99%120@5$3@%101%79$0@%112%99%99%120@5$2@$1@4|%135$8@3|@|@|@|@|@|@|@|@|@"])
  fun op stateRole_TY_DEF x = x
    val op stateRole_TY_DEF =
    ThmBind.DT(((("PBType",83),
                [("bool",[25]),("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%92%31%119%25%76$0@%112%98%120@3|@$0@|@"])
  fun op stateRole_BIJ x = x
    val op stateRole_BIJ =
    ThmBind.DT(((("PBType",84),
                [("PBType",[83]),("bool",[116])]),["DISK_THM"]),
               [ThmBind.read"%74%73%15%83%131%141$0@3$0@|@2%69%26%78%25%76$0@%112%98%120@3|$0@2%79%141%131$0@3$0@2|@2"])

  fun op stateRole_size_def x = x
    val op stateRole_size_def =
    ThmBind.DT(((("PBType",95),[]),[]),
               [ThmBind.read"%73%55%79%143$0@2%75@|@"])
  fun op stateRole_CASE x = x
    val op stateRole_CASE =
    ThmBind.DT(((("PBType",96),[]),[]),
               [ThmBind.read"%73%55%64%36%77%142$1@$0@2%24$1|%141$1@3|@|@"])
  fun op num2slCommand_slCommand2num x = x
    val op num2slCommand_slCommand2num =
    ThmBind.DT(((("PBType",2),[("PBType",[1])]),["DISK_THM"]),
               [ThmBind.read"%70%12%80%128%132$0@3$0@|@"])
  fun op slCommand2num_num2slCommand x = x
    val op slCommand2num_num2slCommand =
    ThmBind.DT(((("PBType",3),[("PBType",[1])]),["DISK_THM"]),
               [ThmBind.read"%69%26%78%76$0@%112%99%99%120@5%79%132%128$0@3$0@2|@"])
  fun op num2slCommand_11 x = x
    val op num2slCommand_11 =
    ThmBind.DT(((("PBType",4),
                [("PBType",[1]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%69%26%69%27%84%76$1@%112%99%99%120@5%84%76$0@%112%99%99%120@5%78%80%128$1@2%128$0@3%79$1@$0@4|@|@"])
  fun op slCommand2num_11 x = x
    val op slCommand2num_11 =
    ThmBind.DT(((("PBType",5),
                [("PBType",[1]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%70%12%70%16%78%79%132$1@2%132$0@3%80$1@$0@2|@|@"])
  fun op num2slCommand_ONTO x = x
    val op num2slCommand_ONTO =
    ThmBind.DT(((("PBType",6),
                [("PBType",[1]),("bool",[25,62])]),["DISK_THM"]),
               [ThmBind.read"%70%12%93%26%74%80$1@%128$0@3%76$0@%112%99%99%120@5|@|@"])
  fun op slCommand2num_ONTO x = x
    val op slCommand2num_ONTO =
    ThmBind.DT(((("PBType",7),
                [("PBType",[1]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%69%26%78%76$0@%112%99%99%120@5%94%12%79$1@%132$0@2|@2|@"])
  fun op num2slCommand_thm x = x
    val op num2slCommand_thm =
    ThmBind.DT(((("PBType",14),[("PBType",[8,9,10,11,12,13])]),[]),
               [ThmBind.read"%74%80%128%75@2%125@2%74%80%128%112%98%120@4%123@2%74%80%128%112%99%120@4%127@2%74%80%128%112%98%98%120@5%124@2%74%80%128%112%99%98%120@5%122@2%80%128%112%98%99%120@5%126@6"])
  fun op slCommand2num_thm x = x
    val op slCommand2num_thm =
    ThmBind.DT(((("PBType",15),
                [("PBType",[3,8,9,10,11,12,13]),("bool",[25,53]),
                 ("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%74%79%132%125@2%75@2%74%79%132%123@2%112%98%120@4%74%79%132%127@2%112%99%120@4%74%79%132%124@2%112%98%98%120@5%74%79%132%122@2%112%99%98%120@5%79%132%126@2%112%98%99%120@9"])
  fun op slCommand_EQ_slCommand x = x
    val op slCommand_EQ_slCommand =
    ThmBind.DT(((("PBType",16),
                [("PBType",[5]),("bool",[57])]),["DISK_THM"]),
               [ThmBind.read"%70%12%70%16%78%80$1@$0@2%79%132$1@2%132$0@3|@|@"])
  fun op slCommand_case_def x = x
    val op slCommand_case_def =
    ThmBind.DT(((("PBType",19),
                [("PBType",[15,18]),("bool",[53,55,63]),
                 ("numeral",[3,6,7])]),["DISK_THM"]),
               [ThmBind.read"%74%64%36%64%38%64%40%64%42%64%44%64%46%77%133%125@$5@$4@$3@$2@$1@$0@2$5@|@|@|@|@|@|@2%74%64%36%64%38%64%40%64%42%64%44%64%46%77%133%123@$5@$4@$3@$2@$1@$0@2$4@|@|@|@|@|@|@2%74%64%36%64%38%64%40%64%42%64%44%64%46%77%133%127@$5@$4@$3@$2@$1@$0@2$3@|@|@|@|@|@|@2%74%64%36%64%38%64%40%64%42%64%44%64%46%77%133%124@$5@$4@$3@$2@$1@$0@2$2@|@|@|@|@|@|@2%74%64%36%64%38%64%40%64%42%64%44%64%46%77%133%122@$5@$4@$3@$2@$1@$0@2$1@|@|@|@|@|@|@2%64%36%64%38%64%40%64%42%64%44%64%46%77%133%126@$5@$4@$3@$2@$1@$0@2$0@|@|@|@|@|@|@6"])
  fun op datatype_slCommand x = x
    val op datatype_slCommand =
    ThmBind.DT(((("PBType",20),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%107%32%125@%123@%127@%124@%122@%126@2"])
  fun op slCommand_distinct x = x
    val op slCommand_distinct =
    ThmBind.DT(((("PBType",21),
                [("PBType",[15,16]),("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%74%146%80%125@%123@3%74%146%80%125@%127@3%74%146%80%125@%124@3%74%146%80%125@%122@3%74%146%80%125@%126@3%74%146%80%123@%127@3%74%146%80%123@%124@3%74%146%80%123@%122@3%74%146%80%123@%126@3%74%146%80%127@%124@3%74%146%80%127@%122@3%74%146%80%127@%126@3%74%146%80%124@%122@3%74%146%80%124@%126@3%146%80%122@%126@16"])
  fun op slCommand_case_cong x = x
    val op slCommand_case_cong =
    ThmBind.DT(((("PBType",22),
                [("PBType",[6,8,9,10,11,12,13,19]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%70%0%70%4%64%36%64%38%64%40%64%42%64%44%64%46%84%74%80$7@$6@2%74%84%80$6@%125@2%77$5@%37@3%74%84%80$6@%123@2%77$4@%39@3%74%84%80$6@%127@2%77$3@%41@3%74%84%80$6@%124@2%77$2@%43@3%74%84%80$6@%122@2%77$1@%45@3%84%80$6@%126@2%77$0@%47@9%77%133$7@$5@$4@$3@$2@$1@$0@2%133$6@%37@%39@%41@%43@%45@%47@3|@|@|@|@|@|@|@|@"])
  fun op slCommand_nchotomy x = x
    val op slCommand_nchotomy =
    ThmBind.DT(((("PBType",23),
                [("PBType",[6,8,9,10,11,12,13]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%70%12%121%80$0@%125@2%121%80$0@%123@2%121%80$0@%127@2%121%80$0@%124@2%121%80$0@%122@2%80$0@%126@6|@"])
  fun op slCommand_Axiom x = x
    val op slCommand_Axiom =
    ThmBind.DT(((("PBType",24),
                [("PBType",[15]),("bool",[8,14,25,53,55,63]),
                 ("numeral",[3,8])]),["DISK_THM"]),
               [ThmBind.read"%64%56%64%57%64%58%64%59%64%60%64%61%85%20%74%77$0%125@2$6@2%74%77$0%123@2$5@2%74%77$0%127@2$4@2%74%77$0%124@2$3@2%74%77$0%122@2$2@2%77$0%126@2$1@6|@|@|@|@|@|@|@"])
  fun op slCommand_induction x = x
    val op slCommand_induction =
    ThmBind.DT(((("PBType",25),
                [("PBType",[6,8,9,10,11,12,13]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%65%8%84%74$0%122@2%74$0%123@2%74$0%124@2%74$0%125@2%74$0%126@2$0%127@7%70%12$1$0@|@2|@"])
  fun op slCommand_distinct_clauses x = x
    val op slCommand_distinct_clauses =
    ThmBind.DT(((("PBType",26),
                [("PBType",[15,16]),("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%74%146%80%125@%123@3%74%146%80%125@%127@3%74%146%80%125@%124@3%74%146%80%125@%122@3%74%146%80%125@%126@3%74%146%80%123@%127@3%74%146%80%123@%124@3%74%146%80%123@%122@3%74%146%80%123@%126@3%74%146%80%127@%124@3%74%146%80%127@%122@3%74%146%80%127@%126@3%74%146%80%124@%122@3%74%146%80%124@%126@3%146%80%122@%126@16"])
  fun op num2slState_slState2num x = x
    val op num2slState_slState2num =
    ThmBind.DT(((("PBType",29),[("PBType",[28])]),["DISK_THM"]),
               [ThmBind.read"%72%14%82%130%138$0@3$0@|@"])
  fun op slState2num_num2slState x = x
    val op slState2num_num2slState =
    ThmBind.DT(((("PBType",30),[("PBType",[28])]),["DISK_THM"]),
               [ThmBind.read"%69%26%78%76$0@%112%99%99%120@5%79%138%130$0@3$0@2|@"])
  fun op num2slState_11 x = x
    val op num2slState_11 =
    ThmBind.DT(((("PBType",31),
                [("PBType",[28]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%69%26%69%27%84%76$1@%112%99%99%120@5%84%76$0@%112%99%99%120@5%78%82%130$1@2%130$0@3%79$1@$0@4|@|@"])
  fun op slState2num_11 x = x
    val op slState2num_11 =
    ThmBind.DT(((("PBType",32),
                [("PBType",[28]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%72%14%72%18%78%79%138$1@2%138$0@3%82$1@$0@2|@|@"])
  fun op num2slState_ONTO x = x
    val op num2slState_ONTO =
    ThmBind.DT(((("PBType",33),
                [("PBType",[28]),("bool",[25,62])]),["DISK_THM"]),
               [ThmBind.read"%72%14%93%26%74%82$1@%130$0@3%76$0@%112%99%99%120@5|@|@"])
  fun op slState2num_ONTO x = x
    val op slState2num_ONTO =
    ThmBind.DT(((("PBType",34),
                [("PBType",[28]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%69%26%78%76$0@%112%99%99%120@5%96%14%79$1@%138$0@2|@2|@"])
  fun op num2slState_thm x = x
    val op num2slState_thm =
    ThmBind.DT(((("PBType",41),[("PBType",[35,36,37,38,39,40])]),[]),
               [ThmBind.read"%74%82%130%75@2%113@2%74%82%130%112%98%120@4%108@2%74%82%130%112%99%120@4%102@2%74%82%130%112%98%98%120@5%109@2%74%82%130%112%99%98%120@5%103@2%82%130%112%98%99%120@5%100@6"])
  fun op slState2num_thm x = x
    val op slState2num_thm =
    ThmBind.DT(((("PBType",42),
                [("PBType",[30,35,36,37,38,39,40]),("bool",[25,53]),
                 ("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%74%79%138%113@2%75@2%74%79%138%108@2%112%98%120@4%74%79%138%102@2%112%99%120@4%74%79%138%109@2%112%98%98%120@5%74%79%138%103@2%112%99%98%120@5%79%138%100@2%112%98%99%120@9"])
  fun op slState_EQ_slState x = x
    val op slState_EQ_slState =
    ThmBind.DT(((("PBType",43),
                [("PBType",[32]),("bool",[57])]),["DISK_THM"]),
               [ThmBind.read"%72%14%72%18%78%82$1@$0@2%79%138$1@2%138$0@3|@|@"])
  fun op slState_case_def x = x
    val op slState_case_def =
    ThmBind.DT(((("PBType",46),
                [("PBType",[42,45]),("bool",[53,55,63]),
                 ("numeral",[3,6,7])]),["DISK_THM"]),
               [ThmBind.read"%74%64%36%64%38%64%40%64%42%64%44%64%46%77%139%113@$5@$4@$3@$2@$1@$0@2$5@|@|@|@|@|@|@2%74%64%36%64%38%64%40%64%42%64%44%64%46%77%139%108@$5@$4@$3@$2@$1@$0@2$4@|@|@|@|@|@|@2%74%64%36%64%38%64%40%64%42%64%44%64%46%77%139%102@$5@$4@$3@$2@$1@$0@2$3@|@|@|@|@|@|@2%74%64%36%64%38%64%40%64%42%64%44%64%46%77%139%109@$5@$4@$3@$2@$1@$0@2$2@|@|@|@|@|@|@2%74%64%36%64%38%64%40%64%42%64%44%64%46%77%139%103@$5@$4@$3@$2@$1@$0@2$1@|@|@|@|@|@|@2%64%36%64%38%64%40%64%42%64%44%64%46%77%139%100@$5@$4@$3@$2@$1@$0@2$0@|@|@|@|@|@|@6"])
  fun op datatype_slState x = x
    val op datatype_slState =
    ThmBind.DT(((("PBType",47),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%107%34%113@%108@%102@%109@%103@%100@2"])
  fun op slState_distinct x = x
    val op slState_distinct =
    ThmBind.DT(((("PBType",48),
                [("PBType",[42,43]),("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%74%146%82%113@%108@3%74%146%82%113@%102@3%74%146%82%113@%109@3%74%146%82%113@%103@3%74%146%82%113@%100@3%74%146%82%108@%102@3%74%146%82%108@%109@3%74%146%82%108@%103@3%74%146%82%108@%100@3%74%146%82%102@%109@3%74%146%82%102@%103@3%74%146%82%102@%100@3%74%146%82%109@%103@3%74%146%82%109@%100@3%146%82%103@%100@16"])
  fun op slState_case_cong x = x
    val op slState_case_cong =
    ThmBind.DT(((("PBType",49),
                [("PBType",[33,35,36,37,38,39,40,46]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%72%2%72%6%64%36%64%38%64%40%64%42%64%44%64%46%84%74%82$7@$6@2%74%84%82$6@%113@2%77$5@%37@3%74%84%82$6@%108@2%77$4@%39@3%74%84%82$6@%102@2%77$3@%41@3%74%84%82$6@%109@2%77$2@%43@3%74%84%82$6@%103@2%77$1@%45@3%84%82$6@%100@2%77$0@%47@9%77%139$7@$5@$4@$3@$2@$1@$0@2%139$6@%37@%39@%41@%43@%45@%47@3|@|@|@|@|@|@|@|@"])
  fun op slState_nchotomy x = x
    val op slState_nchotomy =
    ThmBind.DT(((("PBType",50),
                [("PBType",[33,35,36,37,38,39,40]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%72%14%121%82$0@%113@2%121%82$0@%108@2%121%82$0@%102@2%121%82$0@%109@2%121%82$0@%103@2%82$0@%100@6|@"])
  fun op slState_Axiom x = x
    val op slState_Axiom =
    ThmBind.DT(((("PBType",51),
                [("PBType",[42]),("bool",[8,14,25,53,55,63]),
                 ("numeral",[3,8])]),["DISK_THM"]),
               [ThmBind.read"%64%56%64%57%64%58%64%59%64%60%64%61%89%22%74%77$0%113@2$6@2%74%77$0%108@2$5@2%74%77$0%102@2$4@2%74%77$0%109@2$3@2%74%77$0%103@2$2@2%77$0%100@2$1@6|@|@|@|@|@|@|@"])
  fun op slState_induction x = x
    val op slState_induction =
    ThmBind.DT(((("PBType",52),
                [("PBType",[33,35,36,37,38,39,40]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%67%10%84%74$0%100@2%74$0%102@2%74$0%103@2%74$0%108@2%74$0%109@2$0%113@7%72%14$1$0@|@2|@"])
  fun op slState_distinct_clauses x = x
    val op slState_distinct_clauses =
    ThmBind.DT(((("PBType",53),
                [("PBType",[42,43]),("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%74%146%82%113@%108@3%74%146%82%113@%102@3%74%146%82%113@%109@3%74%146%82%113@%103@3%74%146%82%113@%100@3%74%146%82%108@%102@3%74%146%82%108@%109@3%74%146%82%108@%103@3%74%146%82%108@%100@3%74%146%82%102@%109@3%74%146%82%102@%103@3%74%146%82%102@%100@3%74%146%82%109@%103@3%74%146%82%109@%100@3%146%82%103@%100@16"])
  fun op num2slOutput_slOutput2num x = x
    val op num2slOutput_slOutput2num =
    ThmBind.DT(((("PBType",56),[("PBType",[55])]),["DISK_THM"]),
               [ThmBind.read"%71%13%81%129%135$0@3$0@|@"])
  fun op slOutput2num_num2slOutput x = x
    val op slOutput2num_num2slOutput =
    ThmBind.DT(((("PBType",57),[("PBType",[55])]),["DISK_THM"]),
               [ThmBind.read"%69%26%78%76$0@%112%99%98%98%120@6%79%135%129$0@3$0@2|@"])
  fun op num2slOutput_11 x = x
    val op num2slOutput_11 =
    ThmBind.DT(((("PBType",58),
                [("PBType",[55]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%69%26%69%27%84%76$1@%112%99%98%98%120@6%84%76$0@%112%99%98%98%120@6%78%81%129$1@2%129$0@3%79$1@$0@4|@|@"])
  fun op slOutput2num_11 x = x
    val op slOutput2num_11 =
    ThmBind.DT(((("PBType",59),
                [("PBType",[55]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%71%13%71%17%78%79%135$1@2%135$0@3%81$1@$0@2|@|@"])
  fun op num2slOutput_ONTO x = x
    val op num2slOutput_ONTO =
    ThmBind.DT(((("PBType",60),
                [("PBType",[55]),("bool",[25,62])]),["DISK_THM"]),
               [ThmBind.read"%71%13%93%26%74%81$1@%129$0@3%76$0@%112%99%98%98%120@6|@|@"])
  fun op slOutput2num_ONTO x = x
    val op slOutput2num_ONTO =
    ThmBind.DT(((("PBType",61),
                [("PBType",[55]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%69%26%78%76$0@%112%99%98%98%120@6%95%13%79$1@%135$0@2|@2|@"])
  fun op num2slOutput_thm x = x
    val op num2slOutput_thm =
    ThmBind.DT(((("PBType",70),[("PBType",[62,63,64,65,66,67,68,69])]),[]),
               [ThmBind.read"%74%81%129%75@2%114@2%74%81%129%112%98%120@4%110@2%74%81%129%112%99%120@4%105@2%74%81%129%112%98%98%120@5%111@2%74%81%129%112%99%98%120@5%106@2%74%81%129%112%98%99%120@5%104@2%74%81%129%112%99%99%120@5%144@2%81%129%112%98%98%98%120@6%145@8"])
  fun op slOutput2num_thm x = x
    val op slOutput2num_thm =
    ThmBind.DT(((("PBType",71),
                [("PBType",[57,62,63,64,65,66,67,68,69]),("bool",[25,53]),
                 ("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%74%79%135%114@2%75@2%74%79%135%110@2%112%98%120@4%74%79%135%105@2%112%99%120@4%74%79%135%111@2%112%98%98%120@5%74%79%135%106@2%112%99%98%120@5%74%79%135%104@2%112%98%99%120@5%74%79%135%144@2%112%99%99%120@5%79%135%145@2%112%98%98%98%120@12"])
  fun op slOutput_EQ_slOutput x = x
    val op slOutput_EQ_slOutput =
    ThmBind.DT(((("PBType",72),
                [("PBType",[59]),("bool",[57])]),["DISK_THM"]),
               [ThmBind.read"%71%13%71%17%78%81$1@$0@2%79%135$1@2%135$0@3|@|@"])
  fun op slOutput_case_def x = x
    val op slOutput_case_def =
    ThmBind.DT(((("PBType",75),
                [("PBType",[71,74]),("bool",[53,55,63]),
                 ("numeral",[3,6,7])]),["DISK_THM"]),
               [ThmBind.read"%74%64%36%64%38%64%40%64%42%64%44%64%46%64%48%64%50%77%136%114@$7@$6@$5@$4@$3@$2@$1@$0@2$7@|@|@|@|@|@|@|@|@2%74%64%36%64%38%64%40%64%42%64%44%64%46%64%48%64%50%77%136%110@$7@$6@$5@$4@$3@$2@$1@$0@2$6@|@|@|@|@|@|@|@|@2%74%64%36%64%38%64%40%64%42%64%44%64%46%64%48%64%50%77%136%105@$7@$6@$5@$4@$3@$2@$1@$0@2$5@|@|@|@|@|@|@|@|@2%74%64%36%64%38%64%40%64%42%64%44%64%46%64%48%64%50%77%136%111@$7@$6@$5@$4@$3@$2@$1@$0@2$4@|@|@|@|@|@|@|@|@2%74%64%36%64%38%64%40%64%42%64%44%64%46%64%48%64%50%77%136%106@$7@$6@$5@$4@$3@$2@$1@$0@2$3@|@|@|@|@|@|@|@|@2%74%64%36%64%38%64%40%64%42%64%44%64%46%64%48%64%50%77%136%104@$7@$6@$5@$4@$3@$2@$1@$0@2$2@|@|@|@|@|@|@|@|@2%74%64%36%64%38%64%40%64%42%64%44%64%46%64%48%64%50%77%136%144@$7@$6@$5@$4@$3@$2@$1@$0@2$1@|@|@|@|@|@|@|@|@2%64%36%64%38%64%40%64%42%64%44%64%46%64%48%64%50%77%136%145@$7@$6@$5@$4@$3@$2@$1@$0@2$0@|@|@|@|@|@|@|@|@8"])
  fun op datatype_slOutput x = x
    val op datatype_slOutput =
    ThmBind.DT(((("PBType",76),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%107%33%114@%110@%105@%111@%106@%104@%144@%145@2"])
  fun op slOutput_distinct x = x
    val op slOutput_distinct =
    ThmBind.DT(((("PBType",77),
                [("PBType",[71,72]),("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%74%146%81%114@%110@3%74%146%81%114@%105@3%74%146%81%114@%111@3%74%146%81%114@%106@3%74%146%81%114@%104@3%74%146%81%114@%144@3%74%146%81%114@%145@3%74%146%81%110@%105@3%74%146%81%110@%111@3%74%146%81%110@%106@3%74%146%81%110@%104@3%74%146%81%110@%144@3%74%146%81%110@%145@3%74%146%81%105@%111@3%74%146%81%105@%106@3%74%146%81%105@%104@3%74%146%81%105@%144@3%74%146%81%105@%145@3%74%146%81%111@%106@3%74%146%81%111@%104@3%74%146%81%111@%144@3%74%146%81%111@%145@3%74%146%81%106@%104@3%74%146%81%106@%144@3%74%146%81%106@%145@3%74%146%81%104@%144@3%74%146%81%104@%145@3%146%81%144@%145@29"])
  fun op slOutput_case_cong x = x
    val op slOutput_case_cong =
    ThmBind.DT(((("PBType",78),
                [("PBType",[60,62,63,64,65,66,67,68,69,75]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%71%1%71%5%64%36%64%38%64%40%64%42%64%44%64%46%64%48%64%50%84%74%81$9@$8@2%74%84%81$8@%114@2%77$7@%37@3%74%84%81$8@%110@2%77$6@%39@3%74%84%81$8@%105@2%77$5@%41@3%74%84%81$8@%111@2%77$4@%43@3%74%84%81$8@%106@2%77$3@%45@3%74%84%81$8@%104@2%77$2@%47@3%74%84%81$8@%144@2%77$1@%49@3%84%81$8@%145@2%77$0@%51@11%77%136$9@$7@$6@$5@$4@$3@$2@$1@$0@2%136$8@%37@%39@%41@%43@%45@%47@%49@%51@3|@|@|@|@|@|@|@|@|@|@"])
  fun op slOutput_nchotomy x = x
    val op slOutput_nchotomy =
    ThmBind.DT(((("PBType",79),
                [("PBType",[60,62,63,64,65,66,67,68,69]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%71%13%121%81$0@%114@2%121%81$0@%110@2%121%81$0@%105@2%121%81$0@%111@2%121%81$0@%106@2%121%81$0@%104@2%121%81$0@%144@2%81$0@%145@8|@"])
  fun op slOutput_Axiom x = x
    val op slOutput_Axiom =
    ThmBind.DT(((("PBType",80),
                [("PBType",[71]),("bool",[8,14,25,53,55,63]),
                 ("numeral",[3,8])]),["DISK_THM"]),
               [ThmBind.read"%64%56%64%57%64%58%64%59%64%60%64%61%64%62%64%63%87%21%74%77$0%114@2$8@2%74%77$0%110@2$7@2%74%77$0%105@2$6@2%74%77$0%111@2$5@2%74%77$0%106@2$4@2%74%77$0%104@2$3@2%74%77$0%144@2$2@2%77$0%145@2$1@8|@|@|@|@|@|@|@|@|@"])
  fun op slOutput_induction x = x
    val op slOutput_induction =
    ThmBind.DT(((("PBType",81),
                [("PBType",[60,62,63,64,65,66,67,68,69]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%66%9%84%74$0%104@2%74$0%105@2%74$0%106@2%74$0%110@2%74$0%111@2%74$0%114@2%74$0%144@2$0%145@9%71%13$1$0@|@2|@"])
  fun op slOutput_distinct_clauses x = x
    val op slOutput_distinct_clauses =
    ThmBind.DT(((("PBType",82),
                [("PBType",[71,72]),("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%74%146%81%114@%110@3%74%146%81%114@%105@3%74%146%81%114@%111@3%74%146%81%114@%106@3%74%146%81%114@%104@3%74%146%81%114@%144@3%74%146%81%114@%145@3%74%146%81%110@%105@3%74%146%81%110@%111@3%74%146%81%110@%106@3%74%146%81%110@%104@3%74%146%81%110@%144@3%74%146%81%110@%145@3%74%146%81%105@%111@3%74%146%81%105@%106@3%74%146%81%105@%104@3%74%146%81%105@%144@3%74%146%81%105@%145@3%74%146%81%111@%106@3%74%146%81%111@%104@3%74%146%81%111@%144@3%74%146%81%111@%145@3%74%146%81%106@%104@3%74%146%81%106@%144@3%74%146%81%106@%145@3%74%146%81%104@%144@3%74%146%81%104@%145@3%146%81%144@%145@29"])
  fun op num2stateRole_stateRole2num x = x
    val op num2stateRole_stateRole2num =
    ThmBind.DT(((("PBType",85),[("PBType",[84])]),["DISK_THM"]),
               [ThmBind.read"%73%15%83%131%141$0@3$0@|@"])
  fun op stateRole2num_num2stateRole x = x
    val op stateRole2num_num2stateRole =
    ThmBind.DT(((("PBType",86),[("PBType",[84])]),["DISK_THM"]),
               [ThmBind.read"%69%26%78%76$0@%112%98%120@4%79%141%131$0@3$0@2|@"])
  fun op num2stateRole_11 x = x
    val op num2stateRole_11 =
    ThmBind.DT(((("PBType",87),
                [("PBType",[84]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%69%26%69%27%84%76$1@%112%98%120@4%84%76$0@%112%98%120@4%78%83%131$1@2%131$0@3%79$1@$0@4|@|@"])
  fun op stateRole2num_11 x = x
    val op stateRole2num_11 =
    ThmBind.DT(((("PBType",88),
                [("PBType",[84]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%73%15%73%19%78%79%141$1@2%141$0@3%83$1@$0@2|@|@"])
  fun op num2stateRole_ONTO x = x
    val op num2stateRole_ONTO =
    ThmBind.DT(((("PBType",89),
                [("PBType",[84]),("bool",[25,62])]),["DISK_THM"]),
               [ThmBind.read"%73%15%93%26%74%83$1@%131$0@3%76$0@%112%98%120@4|@|@"])
  fun op stateRole2num_ONTO x = x
    val op stateRole2num_ONTO =
    ThmBind.DT(((("PBType",90),
                [("PBType",[84]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%69%26%78%76$0@%112%98%120@4%97%15%79$1@%141$0@2|@2|@"])
  fun op num2stateRole_thm x = x
    val op num2stateRole_thm =
    ThmBind.DT(((("PBType",92),[("PBType",[91])]),[]),
               [ThmBind.read"%83%131%75@2%115@"])
  fun op stateRole2num_thm x = x
    val op stateRole2num_thm =
    ThmBind.DT(((("PBType",93),
                [("PBType",[86,91]),("bool",[25]),
                 ("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%79%141%115@2%75@"])
  fun op stateRole_EQ_stateRole x = x
    val op stateRole_EQ_stateRole =
    ThmBind.DT(((("PBType",94),
                [("PBType",[88]),("bool",[57])]),["DISK_THM"]),
               [ThmBind.read"%73%15%73%19%78%83$1@$0@2%79%141$1@2%141$0@3|@|@"])
  fun op stateRole_case_def x = x
    val op stateRole_case_def =
    ThmBind.DT(((("PBType",97),[("PBType",[93,96])]),["DISK_THM"]),
               [ThmBind.read"%64%36%77%142%115@$0@2$0@|@"])
  fun op datatype_stateRole x = x
    val op datatype_stateRole =
    ThmBind.DT(((("PBType",98),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%107%35%115@2"])
  fun op stateRole_case_cong x = x
    val op stateRole_case_cong =
    ThmBind.DT(((("PBType",99),
                [("PBType",[89,91,97]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,16]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%73%3%73%7%64%36%84%74%83$2@$1@2%84%83$1@%115@2%77$0@%37@4%77%142$2@$0@2%142$1@%37@3|@|@|@"])
  fun op stateRole_nchotomy x = x
    val op stateRole_nchotomy =
    ThmBind.DT(((("PBType",100),
                [("PBType",[89,91]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,16]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%73%15%83$0@%115@|@"])
  fun op stateRole_Axiom x = x
    val op stateRole_Axiom =
    ThmBind.DT(((("PBType",101),
                [("PBType",[93]),("bool",[8,25,55])]),["DISK_THM"]),
               [ThmBind.read"%64%56%91%23%77$0%115@2$1@|@|@"])
  fun op stateRole_induction x = x
    val op stateRole_induction =
    ThmBind.DT(((("PBType",102),
                [("PBType",[89,91]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,16]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%68%11%84$0%115@2%73%15$1$0@|@2|@"])

  val _ = DB.bindl "PBType"
  [("slCommand_TY_DEF",slCommand_TY_DEF,DB.Def),
   ("slCommand_BIJ",slCommand_BIJ,DB.Def),
   ("slCommand_size_def",slCommand_size_def,DB.Def),
   ("slCommand_CASE",slCommand_CASE,DB.Def),
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
   ("num2slCommand_slCommand2num",num2slCommand_slCommand2num,DB.Thm),
   ("slCommand2num_num2slCommand",slCommand2num_num2slCommand,DB.Thm),
   ("num2slCommand_11",num2slCommand_11,DB.Thm),
   ("slCommand2num_11",slCommand2num_11,DB.Thm),
   ("num2slCommand_ONTO",num2slCommand_ONTO,DB.Thm),
   ("slCommand2num_ONTO",slCommand2num_ONTO,DB.Thm),
   ("num2slCommand_thm",num2slCommand_thm,DB.Thm),
   ("slCommand2num_thm",slCommand2num_thm,DB.Thm),
   ("slCommand_EQ_slCommand",slCommand_EQ_slCommand,DB.Thm),
   ("slCommand_case_def",slCommand_case_def,DB.Thm),
   ("datatype_slCommand",datatype_slCommand,DB.Thm),
   ("slCommand_distinct",slCommand_distinct,DB.Thm),
   ("slCommand_case_cong",slCommand_case_cong,DB.Thm),
   ("slCommand_nchotomy",slCommand_nchotomy,DB.Thm),
   ("slCommand_Axiom",slCommand_Axiom,DB.Thm),
   ("slCommand_induction",slCommand_induction,DB.Thm),
   ("slCommand_distinct_clauses",slCommand_distinct_clauses,DB.Thm),
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
   ("stateRole_case_cong",stateRole_case_cong,DB.Thm),
   ("stateRole_nchotomy",stateRole_nchotomy,DB.Thm),
   ("stateRole_Axiom",stateRole_Axiom,DB.Thm),
   ("stateRole_induction",stateRole_induction,DB.Thm)]

  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "PBType",
    thydataty = "TypeGrammarDeltas",
    read = ThmBind.read,
    data =
        "NTY6.PBType,9.slCommandNTY6.PBType,7.slStateNTY6.PBType,8.slOutputNTY6.PBType,9.stateRole"
  }
  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "PBType",
    thydataty = "TermGrammarDeltas",
    read = ThmBind.read,
    data =
        "OO13.slCommand2num4.%132OO13.num2slCommand4.%128OO7.crossLD4.%125OO10.conductORP4.%123OO8.moveToPB4.%127OO9.conductPB4.%124OO10.completePB4.%122OO10.incomplete4.%126OO14.slCommand_size4.%134OO14.slCommand_CASE4.%133OO4.case4.%133OO11.slState2num4.%138OO11.num2slState4.%130OO7.PLAN_PB4.%113OO11.MOVE_TO_ORP4.%108OO11.CONDUCT_ORP4.%102OO10.MOVE_TO_PB4.%109OO10.CONDUCT_PB4.%103OO11.COMPLETE_PB4.%100OO12.slState_size4.%140OO12.slState_CASE4.%139OO4.case4.%139OO12.slOutput2num4.%135OO12.num2slOutput4.%129OO6.PlanPB4.%114OO9.MoveToORP4.%110OO10.ConductORP4.%105OO8.MoveToPB4.%111OO9.ConductPB4.%106OO10.CompletePB4.%104OO15.unAuthenticated4.%144OO12.unAuthorized4.%145OO13.slOutput_size4.%137OO13.slOutput_CASE4.%136OO4.case4.%136OO13.stateRole2num4.%141OO13.num2stateRole4.%131OO13.PlatoonLeader4.%115OO14.stateRole_size4.%143OO14.stateRole_CASE4.%142OO4.case4.%142"
  }
  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val PBType_grammars = merge_grammars ["indexedLists", "patternMatches"]
  local
  val (tyUDs, tmUDs) = GrammarDeltas.thy_deltas{thyname="PBType"}
  val addtmUDs = term_grammar.add_deltas tmUDs
  val addtyUDs = type_grammar.apply_deltas tyUDs
  in
  val PBType_grammars = 
    Portable.## (addtyUDs,addtmUDs) PBType_grammars
  val _ = Parse.grammarDB_insert("PBType",PBType_grammars)
  val _ = Parse.temp_set_grammars (addtyUDs (Parse.type_grammar()), addtmUDs (Parse.term_grammar()))
  end (* addUDs local *)
  end


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
           size=SOME(Parse.Term`(PBType$slCommand_size) :PBType$slCommand -> num$num`,
                     ORIG slCommand_size_def),
           encode = NONE,
           lift=NONE,
           one_one=NONE,
           distinct=SOME slCommand_distinct,
           fields=let fun T t s A = mk_thy_type{Thy=t,Tyop=s,Args=A}
    val U = mk_vartype
in
[] end,
           accessors=[],
           updates=[],
           recognizers=[],
           destructors=[]}
        val tyinfo0 = EnumType.update_tyinfo num2slCommand_thm slCommand2num_thm NONE tyinfo0
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
           size=SOME(Parse.Term`(PBType$slState_size) :PBType$slState -> num$num`,
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
           size=SOME(Parse.Term`(PBType$slOutput_size) :PBType$slOutput -> num$num`,
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
           size=SOME(Parse.Term`(PBType$stateRole_size) :PBType$stateRole -> num$num`,
                     ORIG stateRole_size_def),
           encode = NONE,
           lift=NONE,
           one_one=NONE,
           distinct=NONE,
           fields=let fun T t s A = mk_thy_type{Thy=t,Tyop=s,Args=A}
    val U = mk_vartype
in
[] end,
           accessors=[],
           updates=[],
           recognizers=[],
           destructors=[]}
        val tyinfo0 = EnumType.update_tyinfo num2stateRole_thm stateRole2num_thm (SOME ("stateRole", stateRole_EQ_stateRole)) tyinfo0
        val () = computeLib.write_datatype_info tyinfo0
      in
        tyinfo0
      end
    ];

val _ = if !Globals.print_thy_loads then print "done\n" else ()
val _ = Theory.load_complete "PBType"
end
