structure MoveToPBTypeTheory :> MoveToPBTypeTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading MoveToPBTypeTheory ... " else ()
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
          ("MoveToPBType",
          Arbnum.fromString "1500249964",
          Arbnum.fromString "26560")
          [("indexedLists",
           Arbnum.fromString "1480536572",
           Arbnum.fromString "423707"),
           ("patternMatches",
           Arbnum.fromString "1480536620",
           Arbnum.fromString "572815")];
  val _ = Theory.incorporate_types "MoveToPBType"
       [("stateRole", 0), ("slState", 0), ("slOutput", 0),
        ("slCommand", 0)];

  val idvector = 
    let fun ID(thy,oth) = {Thy = thy, Other = oth}
    in Vector.fromList
  [ID("MoveToPBType", "slOutput"), ID("min", "fun"), ID("num", "num"),
   ID("MoveToPBType", "stateRole"), ID("MoveToPBType", "slState"),
   ID("MoveToPBType", "slCommand"), ID("min", "bool"), ID("bool", "!"),
   ID("bool", "/\\"), ID("num", "0"), ID("prim_rec", "<"), ID("min", "="),
   ID("min", "==>"), ID("bool", "?"), ID("arithmetic", "BIT1"),
   ID("arithmetic", "BIT2"), ID("MoveToPBType", "COMPLETE"),
   ID("bool", "COND"), ID("MoveToPBType", "Complete"),
   ID("bool", "DATATYPE"), ID("arithmetic", "NUMERAL"),
   ID("MoveToPBType", "PLAN_PB"), ID("MoveToPBType", "PLTForm"),
   ID("MoveToPBType", "PLTHalt"), ID("MoveToPBType", "PLTMove"),
   ID("MoveToPBType", "PLTPlan"), ID("MoveToPBType", "PLT_FORM"),
   ID("MoveToPBType", "PLT_HALT"), ID("MoveToPBType", "PLT_MOVE"),
   ID("MoveToPBType", "PlatoonLeader"), ID("bool", "TYPE_DEFINITION"),
   ID("arithmetic", "ZERO"), ID("bool", "\\/"),
   ID("MoveToPBType", "complete"), ID("MoveToPBType", "incomplete"),
   ID("MoveToPBType", "num2slCommand"), ID("MoveToPBType", "num2slOutput"),
   ID("MoveToPBType", "num2slState"), ID("MoveToPBType", "num2stateRole"),
   ID("MoveToPBType", "pltForm"), ID("MoveToPBType", "pltHalt"),
   ID("MoveToPBType", "pltMove"), ID("MoveToPBType", "slCommand2num"),
   ID("MoveToPBType", "slCommand_CASE"),
   ID("MoveToPBType", "slCommand_size"),
   ID("MoveToPBType", "slOutput2num"), ID("MoveToPBType", "slOutput_CASE"),
   ID("MoveToPBType", "slOutput_size"), ID("MoveToPBType", "slState2num"),
   ID("MoveToPBType", "slState_CASE"), ID("MoveToPBType", "slState_size"),
   ID("MoveToPBType", "stateRole2num"),
   ID("MoveToPBType", "stateRole_CASE"),
   ID("MoveToPBType", "stateRole_size"),
   ID("MoveToPBType", "unAuthenticated"),
   ID("MoveToPBType", "unAuthorized"), ID("bool", "~")]
  end;
  local open SharingTables
  in
  val tyvector = build_type_vector idvector
  [TYOP [0], TYOP [2], TYOP [3], TYOP [1, 2, 1], TYV "'a", TYOP [1, 4, 4],
   TYOP [1, 2, 5], TYOP [4], TYOP [1, 7, 1], TYOP [1, 4, 5],
   TYOP [1, 4, 9], TYOP [1, 4, 10], TYOP [1, 4, 11], TYOP [1, 7, 12],
   TYOP [1, 0, 1], TYOP [1, 4, 12], TYOP [1, 4, 15], TYOP [1, 0, 16],
   TYOP [5], TYOP [1, 18, 1], TYOP [1, 18, 12], TYOP [1, 1, 2],
   TYOP [1, 1, 7], TYOP [1, 1, 0], TYOP [1, 1, 18], TYOP [6],
   TYOP [1, 18, 25], TYOP [1, 0, 25], TYOP [1, 7, 25], TYOP [1, 2, 25],
   TYOP [1, 18, 4], TYOP [1, 0, 4], TYOP [1, 7, 4], TYOP [1, 2, 4],
   TYOP [1, 18, 26], TYOP [1, 18, 34], TYOP [1, 18, 35], TYOP [1, 18, 36],
   TYOP [1, 0, 27], TYOP [1, 0, 38], TYOP [1, 0, 39], TYOP [1, 0, 40],
   TYOP [1, 0, 41], TYOP [1, 0, 42], TYOP [1, 7, 28], TYOP [1, 7, 44],
   TYOP [1, 7, 45], TYOP [1, 7, 46], TYOP [1, 4, 25], TYOP [1, 48, 25],
   TYOP [1, 26, 25], TYOP [1, 50, 25], TYOP [1, 27, 25], TYOP [1, 52, 25],
   TYOP [1, 28, 25], TYOP [1, 54, 25], TYOP [1, 29, 25], TYOP [1, 56, 25],
   TYOP [1, 1, 25], TYOP [1, 58, 25], TYOP [1, 25, 25], TYOP [1, 25, 60],
   TYOP [1, 1, 58], TYOP [1, 4, 48], TYOP [1, 2, 29], TYOP [1, 30, 25],
   TYOP [1, 65, 25], TYOP [1, 19, 25], TYOP [1, 67, 25], TYOP [1, 31, 25],
   TYOP [1, 69, 25], TYOP [1, 14, 25], TYOP [1, 71, 25], TYOP [1, 32, 25],
   TYOP [1, 73, 25], TYOP [1, 8, 25], TYOP [1, 75, 25], TYOP [1, 33, 25],
   TYOP [1, 77, 25], TYOP [1, 3, 25], TYOP [1, 79, 25], TYOP [1, 1, 1],
   TYOP [1, 25, 9], TYOP [1, 58, 67], TYOP [1, 58, 71], TYOP [1, 58, 75],
   TYOP [1, 58, 79]]
  end
  val _ = Theory.incorporate_consts "MoveToPBType" tyvector
     [("unAuthorized", 0), ("unAuthenticated", 0), ("stateRole_size", 3),
      ("stateRole_CASE", 6), ("stateRole2num", 3), ("slState_size", 8),
      ("slState_CASE", 13), ("slState2num", 8), ("slOutput_size", 14),
      ("slOutput_CASE", 17), ("slOutput2num", 14), ("slCommand_size", 19),
      ("slCommand_CASE", 20), ("slCommand2num", 19), ("pltMove", 18),
      ("pltHalt", 18), ("pltForm", 18), ("num2stateRole", 21),
      ("num2slState", 22), ("num2slOutput", 23), ("num2slCommand", 24),
      ("incomplete", 18), ("complete", 18), ("PlatoonLeader", 2),
      ("PLT_MOVE", 7), ("PLT_HALT", 7), ("PLT_FORM", 7), ("PLTPlan", 0),
      ("PLTMove", 0), ("PLTHalt", 0), ("PLTForm", 0), ("PLAN_PB", 7),
      ("Complete", 0), ("COMPLETE", 7)];

  local open SharingTables
  in
  val tmvector = build_term_vector idvector tyvector
  [TMV("M", 18), TMV("M", 0), TMV("M", 7), TMV("M", 2), TMV("M'", 18),
   TMV("M'", 0), TMV("M'", 7), TMV("M'", 2), TMV("P", 26), TMV("P", 27),
   TMV("P", 28), TMV("P", 29), TMV("a", 18), TMV("a", 0), TMV("a", 7),
   TMV("a", 2), TMV("a'", 18), TMV("a'", 0), TMV("a'", 7), TMV("a'", 2),
   TMV("f", 30), TMV("f", 31), TMV("f", 32), TMV("f", 33), TMV("m", 1),
   TMV("n", 1), TMV("r", 1), TMV("r'", 1), TMV("rep", 19), TMV("rep", 14),
   TMV("rep", 8), TMV("rep", 3), TMV("slCommand", 37), TMV("slOutput", 43),
   TMV("slState", 47), TMV("stateRole", 29), TMV("v0", 4), TMV("v0'", 4),
   TMV("v1", 4), TMV("v1'", 4), TMV("v2", 4), TMV("v2'", 4), TMV("v3", 4),
   TMV("v3'", 4), TMV("v4", 4), TMV("v4'", 4), TMV("v5", 4), TMV("v5'", 4),
   TMV("v6", 4), TMV("v6'", 4), TMV("x", 18), TMV("x", 0), TMV("x", 7),
   TMV("x", 2), TMV("x0", 4), TMV("x1", 4), TMV("x2", 4), TMV("x3", 4),
   TMV("x4", 4), TMV("x5", 4), TMV("x6", 4), TMC(7, 49), TMC(7, 51),
   TMC(7, 53), TMC(7, 55), TMC(7, 57), TMC(7, 59), TMC(7, 50), TMC(7, 52),
   TMC(7, 54), TMC(7, 56), TMC(8, 61), TMC(9, 1), TMC(10, 62), TMC(11, 63),
   TMC(11, 61), TMC(11, 62), TMC(11, 34), TMC(11, 38), TMC(11, 44),
   TMC(11, 64), TMC(12, 61), TMC(13, 66), TMC(13, 68), TMC(13, 70),
   TMC(13, 72), TMC(13, 74), TMC(13, 76), TMC(13, 78), TMC(13, 80),
   TMC(13, 59), TMC(13, 50), TMC(13, 52), TMC(13, 54), TMC(13, 56),
   TMC(14, 81), TMC(15, 81), TMC(16, 7), TMC(17, 82), TMC(18, 0),
   TMC(19, 60), TMC(20, 81), TMC(21, 7), TMC(22, 0), TMC(23, 0),
   TMC(24, 0), TMC(25, 0), TMC(26, 7), TMC(27, 7), TMC(28, 7), TMC(29, 2),
   TMC(30, 83), TMC(30, 84), TMC(30, 85), TMC(30, 86), TMC(31, 1),
   TMC(32, 61), TMC(33, 18), TMC(34, 18), TMC(35, 24), TMC(36, 23),
   TMC(37, 22), TMC(38, 21), TMC(39, 18), TMC(40, 18), TMC(41, 18),
   TMC(42, 19), TMC(43, 20), TMC(44, 19), TMC(45, 14), TMC(46, 17),
   TMC(47, 14), TMC(48, 8), TMC(49, 13), TMC(50, 8), TMC(51, 3),
   TMC(52, 6), TMC(53, 3), TMC(54, 0), TMC(55, 0), TMC(56, 60)]
  end
  structure ThmBind = struct
    val DT = Thm.disk_thm
    val read = Term.read_raw tmvector
  end
  fun op slCommand_TY_DEF x = x
    val op slCommand_TY_DEF =
    ThmBind.DT(((("MoveToPBType",0),
                [("bool",[25]),("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%83%28%111%25%73$0@%101%95%96%115@4|@$0@|@"])
  fun op slCommand_BIJ x = x
    val op slCommand_BIJ =
    ThmBind.DT(((("MoveToPBType",1),
                [("MoveToPBType",[0]),("bool",[116])]),["DISK_THM"]),
               [ThmBind.read"%71%67%12%77%119%126$0@3$0@|@2%66%26%75%25%73$0@%101%95%96%115@4|$0@2%76%126%119$0@3$0@2|@2"])





  fun op slCommand_size_def x = x
    val op slCommand_size_def =
    ThmBind.DT(((("MoveToPBType",16),[]),[]),
               [ThmBind.read"%67%50%76%128$0@2%72@|@"])
  fun op slCommand_CASE x = x
    val op slCommand_CASE =
    ThmBind.DT(((("MoveToPBType",17),[]),[]),
               [ThmBind.read"%67%50%61%36%61%38%61%40%61%42%61%44%74%127$5@$4@$3@$2@$1@$0@2%24%98%73$0@%101%96%115@4%98%76$0@%72@2$5@$4@2%98%73$0@%101%95%95%115@5$3@%98%76$0@%101%95%95%115@5$2@$1@3|%126$5@3|@|@|@|@|@|@"])
  fun op slState_TY_DEF x = x
    val op slState_TY_DEF =
    ThmBind.DT(((("MoveToPBType",26),
                [("bool",[25]),("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%87%30%113%25%73$0@%101%95%96%115@4|@$0@|@"])
  fun op slState_BIJ x = x
    val op slState_BIJ =
    ThmBind.DT(((("MoveToPBType",27),
                [("MoveToPBType",[26]),("bool",[116])]),["DISK_THM"]),
               [ThmBind.read"%71%69%14%79%121%132$0@3$0@|@2%66%26%75%25%73$0@%101%95%96%115@4|$0@2%76%132%121$0@3$0@2|@2"])





  fun op slState_size_def x = x
    val op slState_size_def =
    ThmBind.DT(((("MoveToPBType",42),[]),[]),
               [ThmBind.read"%69%52%76%134$0@2%72@|@"])
  fun op slState_CASE x = x
    val op slState_CASE =
    ThmBind.DT(((("MoveToPBType",43),[]),[]),
               [ThmBind.read"%69%52%61%36%61%38%61%40%61%42%61%44%74%133$5@$4@$3@$2@$1@$0@2%24%98%73$0@%101%96%115@4%98%76$0@%72@2$5@$4@2%98%73$0@%101%95%95%115@5$3@%98%76$0@%101%95%95%115@5$2@$1@3|%132$5@3|@|@|@|@|@|@"])
  fun op slOutput_TY_DEF x = x
    val op slOutput_TY_DEF =
    ThmBind.DT(((("MoveToPBType",52),
                [("bool",[25]),("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%85%29%112%25%73$0@%101%95%95%95%115@5|@$0@|@"])
  fun op slOutput_BIJ x = x
    val op slOutput_BIJ =
    ThmBind.DT(((("MoveToPBType",53),
                [("MoveToPBType",[52]),("bool",[116])]),["DISK_THM"]),
               [ThmBind.read"%71%68%13%78%120%129$0@3$0@|@2%66%26%75%25%73$0@%101%95%95%95%115@5|$0@2%76%129%120$0@3$0@2|@2"])







  fun op slOutput_size_def x = x
    val op slOutput_size_def =
    ThmBind.DT(((("MoveToPBType",70),[]),[]),
               [ThmBind.read"%68%51%76%131$0@2%72@|@"])
  fun op slOutput_CASE x = x
    val op slOutput_CASE =
    ThmBind.DT(((("MoveToPBType",71),[]),[]),
               [ThmBind.read"%68%51%61%36%61%38%61%40%61%42%61%44%61%46%61%48%74%130$7@$6@$5@$4@$3@$2@$1@$0@2%24%98%73$0@%101%95%95%115@5%98%73$0@%101%95%115@4$7@%98%76$0@%101%95%115@4$6@$5@3%98%73$0@%101%96%95%115@5$4@%98%73$0@%101%95%96%115@5$3@%98%76$0@%101%95%96%115@5$2@$1@4|%129$7@3|@|@|@|@|@|@|@|@"])
  fun op stateRole_TY_DEF x = x
    val op stateRole_TY_DEF =
    ThmBind.DT(((("MoveToPBType",80),
                [("bool",[25]),("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%89%31%114%25%73$0@%101%95%115@3|@$0@|@"])
  fun op stateRole_BIJ x = x
    val op stateRole_BIJ =
    ThmBind.DT(((("MoveToPBType",81),
                [("MoveToPBType",[80]),("bool",[116])]),["DISK_THM"]),
               [ThmBind.read"%71%70%15%80%122%135$0@3$0@|@2%66%26%75%25%73$0@%101%95%115@3|$0@2%76%135%122$0@3$0@2|@2"])

  fun op stateRole_size_def x = x
    val op stateRole_size_def =
    ThmBind.DT(((("MoveToPBType",92),[]),[]),
               [ThmBind.read"%70%53%76%137$0@2%72@|@"])
  fun op stateRole_CASE x = x
    val op stateRole_CASE =
    ThmBind.DT(((("MoveToPBType",93),[]),[]),
               [ThmBind.read"%70%53%61%36%74%136$1@$0@2%24$1|%135$1@3|@|@"])
  fun op num2slCommand_slCommand2num x = x
    val op num2slCommand_slCommand2num =
    ThmBind.DT(((("MoveToPBType",2),[("MoveToPBType",[1])]),["DISK_THM"]),
               [ThmBind.read"%67%12%77%119%126$0@3$0@|@"])
  fun op slCommand2num_num2slCommand x = x
    val op slCommand2num_num2slCommand =
    ThmBind.DT(((("MoveToPBType",3),[("MoveToPBType",[1])]),["DISK_THM"]),
               [ThmBind.read"%66%26%75%73$0@%101%95%96%115@5%76%126%119$0@3$0@2|@"])
  fun op num2slCommand_11 x = x
    val op num2slCommand_11 =
    ThmBind.DT(((("MoveToPBType",4),
                [("MoveToPBType",[1]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%66%26%66%27%81%73$1@%101%95%96%115@5%81%73$0@%101%95%96%115@5%75%77%119$1@2%119$0@3%76$1@$0@4|@|@"])
  fun op slCommand2num_11 x = x
    val op slCommand2num_11 =
    ThmBind.DT(((("MoveToPBType",5),
                [("MoveToPBType",[1]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%67%12%67%16%75%76%126$1@2%126$0@3%77$1@$0@2|@|@"])
  fun op num2slCommand_ONTO x = x
    val op num2slCommand_ONTO =
    ThmBind.DT(((("MoveToPBType",6),
                [("MoveToPBType",[1]),("bool",[25,62])]),["DISK_THM"]),
               [ThmBind.read"%67%12%90%26%71%77$1@%119$0@3%73$0@%101%95%96%115@5|@|@"])
  fun op slCommand2num_ONTO x = x
    val op slCommand2num_ONTO =
    ThmBind.DT(((("MoveToPBType",7),
                [("MoveToPBType",[1]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%66%26%75%73$0@%101%95%96%115@5%91%12%76$1@%126$0@2|@2|@"])
  fun op num2slCommand_thm x = x
    val op num2slCommand_thm =
    ThmBind.DT(((("MoveToPBType",13),
                [("MoveToPBType",[8,9,10,11,12])]),[]),
               [ThmBind.read"%71%77%119%72@2%123@2%71%77%119%101%95%115@4%125@2%71%77%119%101%96%115@4%124@2%71%77%119%101%95%95%115@5%117@2%77%119%101%96%95%115@5%118@5"])
  fun op slCommand2num_thm x = x
    val op slCommand2num_thm =
    ThmBind.DT(((("MoveToPBType",14),
                [("MoveToPBType",[3,8,9,10,11,12]),("bool",[25,53]),
                 ("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%71%76%126%123@2%72@2%71%76%126%125@2%101%95%115@4%71%76%126%124@2%101%96%115@4%71%76%126%117@2%101%95%95%115@5%76%126%118@2%101%96%95%115@8"])
  fun op slCommand_EQ_slCommand x = x
    val op slCommand_EQ_slCommand =
    ThmBind.DT(((("MoveToPBType",15),
                [("MoveToPBType",[5]),("bool",[57])]),["DISK_THM"]),
               [ThmBind.read"%67%12%67%16%75%77$1@$0@2%76%126$1@2%126$0@3|@|@"])
  fun op slCommand_case_def x = x
    val op slCommand_case_def =
    ThmBind.DT(((("MoveToPBType",18),
                [("MoveToPBType",[14,17]),("bool",[53,55,63]),
                 ("numeral",[3,6,7])]),["DISK_THM"]),
               [ThmBind.read"%71%61%36%61%38%61%40%61%42%61%44%74%127%123@$4@$3@$2@$1@$0@2$4@|@|@|@|@|@2%71%61%36%61%38%61%40%61%42%61%44%74%127%125@$4@$3@$2@$1@$0@2$3@|@|@|@|@|@2%71%61%36%61%38%61%40%61%42%61%44%74%127%124@$4@$3@$2@$1@$0@2$2@|@|@|@|@|@2%71%61%36%61%38%61%40%61%42%61%44%74%127%117@$4@$3@$2@$1@$0@2$1@|@|@|@|@|@2%61%36%61%38%61%40%61%42%61%44%74%127%118@$4@$3@$2@$1@$0@2$0@|@|@|@|@|@5"])
  fun op datatype_slCommand x = x
    val op datatype_slCommand =
    ThmBind.DT(((("MoveToPBType",19),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%100%32%123@%125@%124@%117@%118@2"])
  fun op slCommand_distinct x = x
    val op slCommand_distinct =
    ThmBind.DT(((("MoveToPBType",20),
                [("MoveToPBType",[14,15]),
                 ("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%71%140%77%123@%125@3%71%140%77%123@%124@3%71%140%77%123@%117@3%71%140%77%123@%118@3%71%140%77%125@%124@3%71%140%77%125@%117@3%71%140%77%125@%118@3%71%140%77%124@%117@3%71%140%77%124@%118@3%140%77%117@%118@11"])
  fun op slCommand_case_cong x = x
    val op slCommand_case_cong =
    ThmBind.DT(((("MoveToPBType",21),
                [("MoveToPBType",[6,8,9,10,11,12,18]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%67%0%67%4%61%36%61%38%61%40%61%42%61%44%81%71%77$6@$5@2%71%81%77$5@%123@2%74$4@%37@3%71%81%77$5@%125@2%74$3@%39@3%71%81%77$5@%124@2%74$2@%41@3%71%81%77$5@%117@2%74$1@%43@3%81%77$5@%118@2%74$0@%45@8%74%127$6@$4@$3@$2@$1@$0@2%127$5@%37@%39@%41@%43@%45@3|@|@|@|@|@|@|@"])
  fun op slCommand_nchotomy x = x
    val op slCommand_nchotomy =
    ThmBind.DT(((("MoveToPBType",22),
                [("MoveToPBType",[6,8,9,10,11,12]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%67%12%116%77$0@%123@2%116%77$0@%125@2%116%77$0@%124@2%116%77$0@%117@2%77$0@%118@5|@"])
  fun op slCommand_Axiom x = x
    val op slCommand_Axiom =
    ThmBind.DT(((("MoveToPBType",23),
                [("MoveToPBType",[14]),("bool",[8,14,25,53,55,63]),
                 ("numeral",[3,8])]),["DISK_THM"]),
               [ThmBind.read"%61%54%61%55%61%56%61%57%61%58%82%20%71%74$0%123@2$5@2%71%74$0%125@2$4@2%71%74$0%124@2$3@2%71%74$0%117@2$2@2%74$0%118@2$1@5|@|@|@|@|@|@"])
  fun op slCommand_induction x = x
    val op slCommand_induction =
    ThmBind.DT(((("MoveToPBType",24),
                [("MoveToPBType",[6,8,9,10,11,12]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%62%8%81%71$0%117@2%71$0%118@2%71$0%123@2%71$0%124@2$0%125@6%67%12$1$0@|@2|@"])
  fun op slCommand_distinct_clauses x = x
    val op slCommand_distinct_clauses =
    ThmBind.DT(((("MoveToPBType",25),
                [("MoveToPBType",[14,15]),
                 ("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%71%140%77%123@%125@3%71%140%77%123@%124@3%71%140%77%123@%117@3%71%140%77%123@%118@3%71%140%77%125@%124@3%71%140%77%125@%117@3%71%140%77%125@%118@3%71%140%77%124@%117@3%71%140%77%124@%118@3%140%77%117@%118@11"])
  fun op num2slState_slState2num x = x
    val op num2slState_slState2num =
    ThmBind.DT(((("MoveToPBType",28),
                [("MoveToPBType",[27])]),["DISK_THM"]),
               [ThmBind.read"%69%14%79%121%132$0@3$0@|@"])
  fun op slState2num_num2slState x = x
    val op slState2num_num2slState =
    ThmBind.DT(((("MoveToPBType",29),
                [("MoveToPBType",[27])]),["DISK_THM"]),
               [ThmBind.read"%66%26%75%73$0@%101%95%96%115@5%76%132%121$0@3$0@2|@"])
  fun op num2slState_11 x = x
    val op num2slState_11 =
    ThmBind.DT(((("MoveToPBType",30),
                [("MoveToPBType",[27]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%66%26%66%27%81%73$1@%101%95%96%115@5%81%73$0@%101%95%96%115@5%75%79%121$1@2%121$0@3%76$1@$0@4|@|@"])
  fun op slState2num_11 x = x
    val op slState2num_11 =
    ThmBind.DT(((("MoveToPBType",31),
                [("MoveToPBType",[27]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%69%14%69%18%75%76%132$1@2%132$0@3%79$1@$0@2|@|@"])
  fun op num2slState_ONTO x = x
    val op num2slState_ONTO =
    ThmBind.DT(((("MoveToPBType",32),
                [("MoveToPBType",[27]),("bool",[25,62])]),["DISK_THM"]),
               [ThmBind.read"%69%14%90%26%71%79$1@%121$0@3%73$0@%101%95%96%115@5|@|@"])
  fun op slState2num_ONTO x = x
    val op slState2num_ONTO =
    ThmBind.DT(((("MoveToPBType",33),
                [("MoveToPBType",[27]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%66%26%75%73$0@%101%95%96%115@5%93%14%76$1@%132$0@2|@2|@"])
  fun op num2slState_thm x = x
    val op num2slState_thm =
    ThmBind.DT(((("MoveToPBType",39),
                [("MoveToPBType",[34,35,36,37,38])]),[]),
               [ThmBind.read"%71%79%121%72@2%102@2%71%79%121%101%95%115@4%107@2%71%79%121%101%96%115@4%109@2%71%79%121%101%95%95%115@5%108@2%79%121%101%96%95%115@5%97@5"])
  fun op slState2num_thm x = x
    val op slState2num_thm =
    ThmBind.DT(((("MoveToPBType",40),
                [("MoveToPBType",[29,34,35,36,37,38]),("bool",[25,53]),
                 ("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%71%76%132%102@2%72@2%71%76%132%107@2%101%95%115@4%71%76%132%109@2%101%96%115@4%71%76%132%108@2%101%95%95%115@5%76%132%97@2%101%96%95%115@8"])
  fun op slState_EQ_slState x = x
    val op slState_EQ_slState =
    ThmBind.DT(((("MoveToPBType",41),
                [("MoveToPBType",[31]),("bool",[57])]),["DISK_THM"]),
               [ThmBind.read"%69%14%69%18%75%79$1@$0@2%76%132$1@2%132$0@3|@|@"])
  fun op slState_case_def x = x
    val op slState_case_def =
    ThmBind.DT(((("MoveToPBType",44),
                [("MoveToPBType",[40,43]),("bool",[53,55,63]),
                 ("numeral",[3,6,7])]),["DISK_THM"]),
               [ThmBind.read"%71%61%36%61%38%61%40%61%42%61%44%74%133%102@$4@$3@$2@$1@$0@2$4@|@|@|@|@|@2%71%61%36%61%38%61%40%61%42%61%44%74%133%107@$4@$3@$2@$1@$0@2$3@|@|@|@|@|@2%71%61%36%61%38%61%40%61%42%61%44%74%133%109@$4@$3@$2@$1@$0@2$2@|@|@|@|@|@2%71%61%36%61%38%61%40%61%42%61%44%74%133%108@$4@$3@$2@$1@$0@2$1@|@|@|@|@|@2%61%36%61%38%61%40%61%42%61%44%74%133%97@$4@$3@$2@$1@$0@2$0@|@|@|@|@|@5"])
  fun op datatype_slState x = x
    val op datatype_slState =
    ThmBind.DT(((("MoveToPBType",45),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%100%34%102@%107@%109@%108@%97@2"])
  fun op slState_distinct x = x
    val op slState_distinct =
    ThmBind.DT(((("MoveToPBType",46),
                [("MoveToPBType",[40,41]),
                 ("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%71%140%79%102@%107@3%71%140%79%102@%109@3%71%140%79%102@%108@3%71%140%79%102@%97@3%71%140%79%107@%109@3%71%140%79%107@%108@3%71%140%79%107@%97@3%71%140%79%109@%108@3%71%140%79%109@%97@3%140%79%108@%97@11"])
  fun op slState_case_cong x = x
    val op slState_case_cong =
    ThmBind.DT(((("MoveToPBType",47),
                [("MoveToPBType",[32,34,35,36,37,38,44]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%69%2%69%6%61%36%61%38%61%40%61%42%61%44%81%71%79$6@$5@2%71%81%79$5@%102@2%74$4@%37@3%71%81%79$5@%107@2%74$3@%39@3%71%81%79$5@%109@2%74$2@%41@3%71%81%79$5@%108@2%74$1@%43@3%81%79$5@%97@2%74$0@%45@8%74%133$6@$4@$3@$2@$1@$0@2%133$5@%37@%39@%41@%43@%45@3|@|@|@|@|@|@|@"])
  fun op slState_nchotomy x = x
    val op slState_nchotomy =
    ThmBind.DT(((("MoveToPBType",48),
                [("MoveToPBType",[32,34,35,36,37,38]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%69%14%116%79$0@%102@2%116%79$0@%107@2%116%79$0@%109@2%116%79$0@%108@2%79$0@%97@5|@"])
  fun op slState_Axiom x = x
    val op slState_Axiom =
    ThmBind.DT(((("MoveToPBType",49),
                [("MoveToPBType",[40]),("bool",[8,14,25,53,55,63]),
                 ("numeral",[3,8])]),["DISK_THM"]),
               [ThmBind.read"%61%54%61%55%61%56%61%57%61%58%86%22%71%74$0%102@2$5@2%71%74$0%107@2$4@2%71%74$0%109@2$3@2%71%74$0%108@2$2@2%74$0%97@2$1@5|@|@|@|@|@|@"])
  fun op slState_induction x = x
    val op slState_induction =
    ThmBind.DT(((("MoveToPBType",50),
                [("MoveToPBType",[32,34,35,36,37,38]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%64%10%81%71$0%97@2%71$0%102@2%71$0%107@2%71$0%108@2$0%109@6%69%14$1$0@|@2|@"])
  fun op slState_distinct_clauses x = x
    val op slState_distinct_clauses =
    ThmBind.DT(((("MoveToPBType",51),
                [("MoveToPBType",[40,41]),
                 ("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%71%140%79%102@%107@3%71%140%79%102@%109@3%71%140%79%102@%108@3%71%140%79%102@%97@3%71%140%79%107@%109@3%71%140%79%107@%108@3%71%140%79%107@%97@3%71%140%79%109@%108@3%71%140%79%109@%97@3%140%79%108@%97@11"])
  fun op num2slOutput_slOutput2num x = x
    val op num2slOutput_slOutput2num =
    ThmBind.DT(((("MoveToPBType",54),
                [("MoveToPBType",[53])]),["DISK_THM"]),
               [ThmBind.read"%68%13%78%120%129$0@3$0@|@"])
  fun op slOutput2num_num2slOutput x = x
    val op slOutput2num_num2slOutput =
    ThmBind.DT(((("MoveToPBType",55),
                [("MoveToPBType",[53])]),["DISK_THM"]),
               [ThmBind.read"%66%26%75%73$0@%101%95%95%95%115@6%76%129%120$0@3$0@2|@"])
  fun op num2slOutput_11 x = x
    val op num2slOutput_11 =
    ThmBind.DT(((("MoveToPBType",56),
                [("MoveToPBType",[53]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%66%26%66%27%81%73$1@%101%95%95%95%115@6%81%73$0@%101%95%95%95%115@6%75%78%120$1@2%120$0@3%76$1@$0@4|@|@"])
  fun op slOutput2num_11 x = x
    val op slOutput2num_11 =
    ThmBind.DT(((("MoveToPBType",57),
                [("MoveToPBType",[53]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%68%13%68%17%75%76%129$1@2%129$0@3%78$1@$0@2|@|@"])
  fun op num2slOutput_ONTO x = x
    val op num2slOutput_ONTO =
    ThmBind.DT(((("MoveToPBType",58),
                [("MoveToPBType",[53]),("bool",[25,62])]),["DISK_THM"]),
               [ThmBind.read"%68%13%90%26%71%78$1@%120$0@3%73$0@%101%95%95%95%115@6|@|@"])
  fun op slOutput2num_ONTO x = x
    val op slOutput2num_ONTO =
    ThmBind.DT(((("MoveToPBType",59),
                [("MoveToPBType",[53]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%66%26%75%73$0@%101%95%95%95%115@6%92%13%76$1@%129$0@2|@2|@"])
  fun op num2slOutput_thm x = x
    val op num2slOutput_thm =
    ThmBind.DT(((("MoveToPBType",67),
                [("MoveToPBType",[60,61,62,63,64,65,66])]),[]),
               [ThmBind.read"%71%78%120%72@2%106@2%71%78%120%101%95%115@4%103@2%71%78%120%101%96%115@4%105@2%71%78%120%101%95%95%115@5%104@2%71%78%120%101%96%95%115@5%99@2%71%78%120%101%95%96%115@5%139@2%78%120%101%96%96%115@5%138@7"])
  fun op slOutput2num_thm x = x
    val op slOutput2num_thm =
    ThmBind.DT(((("MoveToPBType",68),
                [("MoveToPBType",[55,60,61,62,63,64,65,66]),("bool",[25]),
                 ("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%71%76%129%106@2%72@2%71%76%129%103@2%101%95%115@4%71%76%129%105@2%101%96%115@4%71%76%129%104@2%101%95%95%115@5%71%76%129%99@2%101%96%95%115@5%71%76%129%139@2%101%95%96%115@5%76%129%138@2%101%96%96%115@10"])
  fun op slOutput_EQ_slOutput x = x
    val op slOutput_EQ_slOutput =
    ThmBind.DT(((("MoveToPBType",69),
                [("MoveToPBType",[57]),("bool",[57])]),["DISK_THM"]),
               [ThmBind.read"%68%13%68%17%75%78$1@$0@2%76%129$1@2%129$0@3|@|@"])
  fun op slOutput_case_def x = x
    val op slOutput_case_def =
    ThmBind.DT(((("MoveToPBType",72),
                [("MoveToPBType",[68,71]),("bool",[53,55,63]),
                 ("numeral",[3,6,7])]),["DISK_THM"]),
               [ThmBind.read"%71%61%36%61%38%61%40%61%42%61%44%61%46%61%48%74%130%106@$6@$5@$4@$3@$2@$1@$0@2$6@|@|@|@|@|@|@|@2%71%61%36%61%38%61%40%61%42%61%44%61%46%61%48%74%130%103@$6@$5@$4@$3@$2@$1@$0@2$5@|@|@|@|@|@|@|@2%71%61%36%61%38%61%40%61%42%61%44%61%46%61%48%74%130%105@$6@$5@$4@$3@$2@$1@$0@2$4@|@|@|@|@|@|@|@2%71%61%36%61%38%61%40%61%42%61%44%61%46%61%48%74%130%104@$6@$5@$4@$3@$2@$1@$0@2$3@|@|@|@|@|@|@|@2%71%61%36%61%38%61%40%61%42%61%44%61%46%61%48%74%130%99@$6@$5@$4@$3@$2@$1@$0@2$2@|@|@|@|@|@|@|@2%71%61%36%61%38%61%40%61%42%61%44%61%46%61%48%74%130%139@$6@$5@$4@$3@$2@$1@$0@2$1@|@|@|@|@|@|@|@2%61%36%61%38%61%40%61%42%61%44%61%46%61%48%74%130%138@$6@$5@$4@$3@$2@$1@$0@2$0@|@|@|@|@|@|@|@7"])
  fun op datatype_slOutput x = x
    val op datatype_slOutput =
    ThmBind.DT(((("MoveToPBType",73),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%100%33%106@%103@%105@%104@%99@%139@%138@2"])
  fun op slOutput_distinct x = x
    val op slOutput_distinct =
    ThmBind.DT(((("MoveToPBType",74),
                [("MoveToPBType",[68,69]),
                 ("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%71%140%78%106@%103@3%71%140%78%106@%105@3%71%140%78%106@%104@3%71%140%78%106@%99@3%71%140%78%106@%139@3%71%140%78%106@%138@3%71%140%78%103@%105@3%71%140%78%103@%104@3%71%140%78%103@%99@3%71%140%78%103@%139@3%71%140%78%103@%138@3%71%140%78%105@%104@3%71%140%78%105@%99@3%71%140%78%105@%139@3%71%140%78%105@%138@3%71%140%78%104@%99@3%71%140%78%104@%139@3%71%140%78%104@%138@3%71%140%78%99@%139@3%71%140%78%99@%138@3%140%78%139@%138@22"])
  fun op slOutput_case_cong x = x
    val op slOutput_case_cong =
    ThmBind.DT(((("MoveToPBType",75),
                [("MoveToPBType",[58,60,61,62,63,64,65,66,72]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%68%1%68%5%61%36%61%38%61%40%61%42%61%44%61%46%61%48%81%71%78$8@$7@2%71%81%78$7@%106@2%74$6@%37@3%71%81%78$7@%103@2%74$5@%39@3%71%81%78$7@%105@2%74$4@%41@3%71%81%78$7@%104@2%74$3@%43@3%71%81%78$7@%99@2%74$2@%45@3%71%81%78$7@%139@2%74$1@%47@3%81%78$7@%138@2%74$0@%49@10%74%130$8@$6@$5@$4@$3@$2@$1@$0@2%130$7@%37@%39@%41@%43@%45@%47@%49@3|@|@|@|@|@|@|@|@|@"])
  fun op slOutput_nchotomy x = x
    val op slOutput_nchotomy =
    ThmBind.DT(((("MoveToPBType",76),
                [("MoveToPBType",[58,60,61,62,63,64,65,66]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%68%13%116%78$0@%106@2%116%78$0@%103@2%116%78$0@%105@2%116%78$0@%104@2%116%78$0@%99@2%116%78$0@%139@2%78$0@%138@7|@"])
  fun op slOutput_Axiom x = x
    val op slOutput_Axiom =
    ThmBind.DT(((("MoveToPBType",77),
                [("MoveToPBType",[68]),("bool",[8,14,25,53,55,63]),
                 ("numeral",[3,8])]),["DISK_THM"]),
               [ThmBind.read"%61%54%61%55%61%56%61%57%61%58%61%59%61%60%84%21%71%74$0%106@2$7@2%71%74$0%103@2$6@2%71%74$0%105@2$5@2%71%74$0%104@2$4@2%71%74$0%99@2$3@2%71%74$0%139@2$2@2%74$0%138@2$1@7|@|@|@|@|@|@|@|@"])
  fun op slOutput_induction x = x
    val op slOutput_induction =
    ThmBind.DT(((("MoveToPBType",78),
                [("MoveToPBType",[58,60,61,62,63,64,65,66]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%63%9%81%71$0%99@2%71$0%103@2%71$0%104@2%71$0%105@2%71$0%106@2%71$0%138@2$0%139@8%68%13$1$0@|@2|@"])
  fun op slOutput_distinct_clauses x = x
    val op slOutput_distinct_clauses =
    ThmBind.DT(((("MoveToPBType",79),
                [("MoveToPBType",[68,69]),
                 ("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%71%140%78%106@%103@3%71%140%78%106@%105@3%71%140%78%106@%104@3%71%140%78%106@%99@3%71%140%78%106@%139@3%71%140%78%106@%138@3%71%140%78%103@%105@3%71%140%78%103@%104@3%71%140%78%103@%99@3%71%140%78%103@%139@3%71%140%78%103@%138@3%71%140%78%105@%104@3%71%140%78%105@%99@3%71%140%78%105@%139@3%71%140%78%105@%138@3%71%140%78%104@%99@3%71%140%78%104@%139@3%71%140%78%104@%138@3%71%140%78%99@%139@3%71%140%78%99@%138@3%140%78%139@%138@22"])
  fun op num2stateRole_stateRole2num x = x
    val op num2stateRole_stateRole2num =
    ThmBind.DT(((("MoveToPBType",82),
                [("MoveToPBType",[81])]),["DISK_THM"]),
               [ThmBind.read"%70%15%80%122%135$0@3$0@|@"])
  fun op stateRole2num_num2stateRole x = x
    val op stateRole2num_num2stateRole =
    ThmBind.DT(((("MoveToPBType",83),
                [("MoveToPBType",[81])]),["DISK_THM"]),
               [ThmBind.read"%66%26%75%73$0@%101%95%115@4%76%135%122$0@3$0@2|@"])
  fun op num2stateRole_11 x = x
    val op num2stateRole_11 =
    ThmBind.DT(((("MoveToPBType",84),
                [("MoveToPBType",[81]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%66%26%66%27%81%73$1@%101%95%115@4%81%73$0@%101%95%115@4%75%80%122$1@2%122$0@3%76$1@$0@4|@|@"])
  fun op stateRole2num_11 x = x
    val op stateRole2num_11 =
    ThmBind.DT(((("MoveToPBType",85),
                [("MoveToPBType",[81]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%70%15%70%19%75%76%135$1@2%135$0@3%80$1@$0@2|@|@"])
  fun op num2stateRole_ONTO x = x
    val op num2stateRole_ONTO =
    ThmBind.DT(((("MoveToPBType",86),
                [("MoveToPBType",[81]),("bool",[25,62])]),["DISK_THM"]),
               [ThmBind.read"%70%15%90%26%71%80$1@%122$0@3%73$0@%101%95%115@4|@|@"])
  fun op stateRole2num_ONTO x = x
    val op stateRole2num_ONTO =
    ThmBind.DT(((("MoveToPBType",87),
                [("MoveToPBType",[81]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%66%26%75%73$0@%101%95%115@4%94%15%76$1@%135$0@2|@2|@"])
  fun op num2stateRole_thm x = x
    val op num2stateRole_thm =
    ThmBind.DT(((("MoveToPBType",89),[("MoveToPBType",[88])]),[]),
               [ThmBind.read"%80%122%72@2%110@"])
  fun op stateRole2num_thm x = x
    val op stateRole2num_thm =
    ThmBind.DT(((("MoveToPBType",90),
                [("MoveToPBType",[83,88]),("bool",[25]),
                 ("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%76%135%110@2%72@"])
  fun op stateRole_EQ_stateRole x = x
    val op stateRole_EQ_stateRole =
    ThmBind.DT(((("MoveToPBType",91),
                [("MoveToPBType",[85]),("bool",[57])]),["DISK_THM"]),
               [ThmBind.read"%70%15%70%19%75%80$1@$0@2%76%135$1@2%135$0@3|@|@"])
  fun op stateRole_case_def x = x
    val op stateRole_case_def =
    ThmBind.DT(((("MoveToPBType",94),
                [("MoveToPBType",[90,93])]),["DISK_THM"]),
               [ThmBind.read"%61%36%74%136%110@$0@2$0@|@"])
  fun op datatype_stateRole x = x
    val op datatype_stateRole =
    ThmBind.DT(((("MoveToPBType",95),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%100%35%110@2"])
  fun op stateRole_case_cong x = x
    val op stateRole_case_cong =
    ThmBind.DT(((("MoveToPBType",96),
                [("MoveToPBType",[86,88,94]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,16]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%70%3%70%7%61%36%81%71%80$2@$1@2%81%80$1@%110@2%74$0@%37@4%74%136$2@$0@2%136$1@%37@3|@|@|@"])
  fun op stateRole_nchotomy x = x
    val op stateRole_nchotomy =
    ThmBind.DT(((("MoveToPBType",97),
                [("MoveToPBType",[86,88]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,16]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%70%15%80$0@%110@|@"])
  fun op stateRole_Axiom x = x
    val op stateRole_Axiom =
    ThmBind.DT(((("MoveToPBType",98),
                [("MoveToPBType",[90]),("bool",[8,25,55])]),["DISK_THM"]),
               [ThmBind.read"%61%54%88%23%74$0%110@2$1@|@|@"])
  fun op stateRole_induction x = x
    val op stateRole_induction =
    ThmBind.DT(((("MoveToPBType",99),
                [("MoveToPBType",[86,88]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,177,178,182,185,274]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,16]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%65%11%81$0%110@2%70%15$1$0@|@2|@"])

  val _ = DB.bindl "MoveToPBType"
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
    thy = "MoveToPBType",
    thydataty = "TypeGrammarDeltas",
    read = ThmBind.read,
    data =
        "NTY12.MoveToPBType,9.slCommandNTY12.MoveToPBType,7.slStateNTY12.MoveToPBType,8.slOutputNTY12.MoveToPBType,9.stateRole"
  }
  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "MoveToPBType",
    thydataty = "TermGrammarDeltas",
    read = ThmBind.read,
    data =
        "OO13.slCommand2num4.%126OO13.num2slCommand4.%119OO7.pltForm4.%123OO7.pltMove4.%125OO7.pltHalt4.%124OO8.complete4.%117OO10.incomplete4.%118OO14.slCommand_size4.%128OO14.slCommand_CASE4.%127OO4.case4.%127OO11.slState2num4.%132OO11.num2slState4.%121OO7.PLAN_PB4.%102OO8.PLT_FORM4.%107OO8.PLT_MOVE4.%109OO8.PLT_HALT4.%108OO8.COMPLETE3.%97OO12.slState_size4.%134OO12.slState_CASE4.%133OO4.case4.%133OO12.slOutput2num4.%129OO12.num2slOutput4.%120OO7.PLTPlan4.%106OO7.PLTForm4.%103OO7.PLTMove4.%105OO7.PLTHalt4.%104OO8.Complete3.%99OO12.unAuthorized4.%139OO15.unAuthenticated4.%138OO13.slOutput_size4.%131OO13.slOutput_CASE4.%130OO4.case4.%130OO13.stateRole2num4.%135OO13.num2stateRole4.%122OO13.PlatoonLeader4.%110OO14.stateRole_size4.%137OO14.stateRole_CASE4.%136OO4.case4.%136"
  }
  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val MoveToPBType_grammars = merge_grammars ["indexedLists",
                                              "patternMatches"]
  local
  val (tyUDs, tmUDs) = GrammarDeltas.thy_deltas{thyname="MoveToPBType"}
  val addtmUDs = term_grammar.add_deltas tmUDs
  val addtyUDs = type_grammar.apply_deltas tyUDs
  in
  val MoveToPBType_grammars = 
    Portable.## (addtyUDs,addtmUDs) MoveToPBType_grammars
  val _ = Parse.grammarDB_insert("MoveToPBType",MoveToPBType_grammars)
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
           size=SOME(Parse.Term`(MoveToPBType$slCommand_size) :MoveToPBType$slCommand -> num$num`,
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
           size=SOME(Parse.Term`(MoveToPBType$slState_size) :MoveToPBType$slState -> num$num`,
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
           size=SOME(Parse.Term`(MoveToPBType$slOutput_size) :MoveToPBType$slOutput -> num$num`,
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
           size=SOME(Parse.Term`(MoveToPBType$stateRole_size) :MoveToPBType$stateRole -> num$num`,
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
val _ = Theory.load_complete "MoveToPBType"
end
