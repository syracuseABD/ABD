structure OMNITypeTheory :> OMNITypeTheory =
struct
  val _ = if !Globals.print_thy_loads then TextIO.print "Loading OMNITypeTheory ... " else ()
  open Type Term Thm
  infixr -->

  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  (* Parents and ML dependencies *)
  local open indexedListsTheory patternMatchesTheory
  in end;
  val _ = Theory.link_parents
          ("OMNIType",
          Arbnum.fromString "1503359458",
          Arbnum.fromString "91129")
          [("indexedLists",
           Arbnum.fromString "1497837441",
           Arbnum.fromString "85466"),
           ("patternMatches",
           Arbnum.fromString "1497837479",
           Arbnum.fromString "270614")];
  val _ = Theory.incorporate_types "OMNIType"
       [("state", 1), ("principal", 1), ("output", 1), ("escState", 0),
        ("escOutput", 0), ("escCommand", 0), ("command", 1)];

  val idvector = 
    let fun ID(thy,oth) = {Thy = thy, Other = oth}
    in Vector.fromList
  [ID("min", "fun"), ID("num", "num"), ID("OMNIType", "state"),
   ID("OMNIType", "escState"), ID("OMNIType", "escCommand"),
   ID("OMNIType", "principal"), ID("OMNIType", "output"),
   ID("OMNIType", "escOutput"), ID("OMNIType", "command"),
   ID("min", "bool"), ID("ind_type", "recspace"), ID("pair", "prod"),
   ID("bool", "!"), ID("arithmetic", "+"), ID("pair", ","),
   ID("bool", "/\\"), ID("num", "0"), ID("prim_rec", "<"), ID("min", "="),
   ID("min", "==>"), ID("bool", "?"), ID("bool", "ARB"),
   ID("arithmetic", "BIT1"), ID("arithmetic", "BIT2"),
   ID("ind_type", "BOTTOM"), ID("OMNIType", "CM"), ID("bool", "COND"),
   ID("ind_type", "CONSTR"), ID("OMNIType", "ChangeMission"),
   ID("bool", "DATATYPE"), ID("OMNIType", "ESCc"), ID("OMNIType", "ESCo"),
   ID("OMNIType", "ESCs"), ID("arithmetic", "NUMERAL"),
   ID("OMNIType", "RESUPPLY"), ID("OMNIType", "RTB"),
   ID("OMNIType", "RTC"), ID("OMNIType", "ReactToContact"),
   ID("OMNIType", "Resupply"), ID("OMNIType", "ReturnToBase"),
   ID("OMNIType", "SLc"), ID("OMNIType", "SLo"), ID("OMNIType", "SLs"),
   ID("OMNIType", "SR"), ID("num", "SUC"), ID("bool", "TYPE_DEFINITION"),
   ID("arithmetic", "ZERO"), ID("bool", "\\/"),
   ID("OMNIType", "changeMission"), ID("OMNIType", "command_CASE"),
   ID("OMNIType", "command_size"), ID("OMNIType", "escCommand2num"),
   ID("OMNIType", "escCommand_CASE"), ID("OMNIType", "escCommand_size"),
   ID("OMNIType", "escOutput2num"), ID("OMNIType", "escOutput_CASE"),
   ID("OMNIType", "escOutput_size"), ID("OMNIType", "escState2num"),
   ID("OMNIType", "escState_CASE"), ID("OMNIType", "escState_size"),
   ID("OMNIType", "num2escCommand"), ID("OMNIType", "num2escOutput"),
   ID("OMNIType", "num2escState"), ID("OMNIType", "output_CASE"),
   ID("OMNIType", "output_size"), ID("OMNIType", "principal_CASE"),
   ID("OMNIType", "principal_size"), ID("OMNIType", "reactToContact"),
   ID("OMNIType", "resupply"), ID("OMNIType", "returnToBase"),
   ID("OMNIType", "state_CASE"), ID("OMNIType", "state_size"),
   ID("bool", "~")]
  end;
  local open SharingTables
  in
  val tyvector = build_type_vector idvector
  [TYOP [1], TYV "'slState", TYOP [2, 1], TYOP [0, 2, 0], TYOP [0, 1, 0],
   TYOP [0, 4, 3], TYV "'a", TYOP [0, 1, 6], TYOP [0, 7, 6], TYOP [3],
   TYOP [0, 9, 6], TYOP [0, 10, 8], TYOP [0, 2, 11], TYOP [4],
   TYV "'stateRole", TYOP [5, 14], TYOP [0, 15, 0], TYOP [0, 14, 0],
   TYOP [0, 17, 16], TYOP [0, 14, 6], TYOP [0, 19, 6], TYOP [0, 15, 20],
   TYV "'slOutput", TYOP [6, 22], TYOP [0, 23, 0], TYOP [0, 22, 0],
   TYOP [0, 25, 24], TYOP [0, 22, 6], TYOP [0, 27, 6], TYOP [7],
   TYOP [0, 29, 6], TYOP [0, 30, 28], TYOP [0, 23, 31], TYOP [0, 0, 9],
   TYOP [0, 0, 29], TYOP [0, 0, 13], TYOP [0, 9, 0], TYOP [0, 6, 6],
   TYOP [0, 6, 37], TYOP [0, 6, 38], TYOP [0, 6, 39], TYOP [0, 9, 40],
   TYOP [0, 29, 0], TYOP [0, 29, 40], TYOP [0, 13, 0], TYOP [0, 13, 40],
   TYV "'slCommand", TYOP [8, 46], TYOP [0, 47, 0], TYOP [0, 46, 0],
   TYOP [0, 49, 48], TYOP [0, 46, 6], TYOP [0, 51, 6], TYOP [0, 13, 6],
   TYOP [0, 53, 52], TYOP [0, 47, 54], TYOP [0, 14, 15], TYOP [0, 1, 2],
   TYOP [0, 22, 23], TYOP [0, 46, 47], TYOP [0, 9, 2], TYOP [0, 29, 23],
   TYOP [0, 13, 47], TYOP [9], TYOP [11, 13, 46], TYOP [10, 64],
   TYOP [0, 65, 63], TYOP [11, 29, 22], TYOP [10, 67], TYOP [0, 68, 63],
   TYOP [10, 14], TYOP [0, 70, 63], TYOP [11, 9, 1], TYOP [10, 72],
   TYOP [0, 73, 63], TYOP [0, 47, 63], TYOP [0, 13, 63], TYOP [0, 29, 63],
   TYOP [0, 9, 63], TYOP [0, 23, 63], TYOP [0, 15, 63], TYOP [0, 2, 63],
   TYOP [0, 59, 63], TYOP [0, 62, 82], TYOP [0, 13, 76], TYOP [0, 13, 84],
   TYOP [0, 13, 85], TYOP [0, 29, 77], TYOP [0, 29, 87], TYOP [0, 29, 88],
   TYOP [0, 9, 78], TYOP [0, 9, 90], TYOP [0, 9, 91], TYOP [0, 47, 6],
   TYOP [0, 23, 6], TYOP [0, 15, 6], TYOP [0, 2, 6], TYOP [0, 58, 63],
   TYOP [0, 61, 97], TYOP [0, 56, 63], TYOP [0, 47, 65], TYOP [0, 23, 68],
   TYOP [0, 15, 70], TYOP [0, 2, 73], TYOP [0, 57, 63], TYOP [0, 60, 104],
   TYOP [0, 6, 63], TYOP [0, 106, 63], TYOP [0, 46, 63], TYOP [0, 108, 63],
   TYOP [0, 22, 63], TYOP [0, 110, 63], TYOP [0, 1, 63], TYOP [0, 112, 63],
   TYOP [0, 14, 63], TYOP [0, 114, 63], TYOP [0, 75, 63], TYOP [0, 76, 63],
   TYOP [0, 77, 63], TYOP [0, 78, 63], TYOP [0, 51, 63], TYOP [0, 120, 63],
   TYOP [0, 49, 63], TYOP [0, 122, 63], TYOP [0, 27, 63],
   TYOP [0, 124, 63], TYOP [0, 25, 63], TYOP [0, 126, 63], TYOP [0, 7, 63],
   TYOP [0, 128, 63], TYOP [0, 4, 63], TYOP [0, 130, 63], TYOP [0, 19, 63],
   TYOP [0, 132, 63], TYOP [0, 17, 63], TYOP [0, 134, 63],
   TYOP [0, 116, 63], TYOP [0, 53, 63], TYOP [0, 137, 63],
   TYOP [0, 117, 63], TYOP [0, 30, 63], TYOP [0, 140, 63],
   TYOP [0, 118, 63], TYOP [0, 10, 63], TYOP [0, 143, 63],
   TYOP [0, 119, 63], TYOP [0, 79, 63], TYOP [0, 146, 63],
   TYOP [0, 80, 63], TYOP [0, 148, 63], TYOP [0, 71, 63],
   TYOP [0, 150, 63], TYOP [0, 66, 63], TYOP [0, 152, 63],
   TYOP [0, 69, 63], TYOP [0, 154, 63], TYOP [0, 74, 63],
   TYOP [0, 156, 63], TYOP [0, 81, 63], TYOP [0, 158, 63], TYOP [0, 0, 63],
   TYOP [0, 160, 63], TYOP [0, 0, 0], TYOP [0, 0, 162], TYOP [0, 46, 64],
   TYOP [0, 13, 164], TYOP [0, 22, 67], TYOP [0, 29, 166], TYOP [0, 1, 72],
   TYOP [0, 9, 168], TYOP [0, 63, 63], TYOP [0, 63, 170], TYOP [0, 0, 160],
   TYOP [0, 6, 106], TYOP [0, 46, 108], TYOP [0, 22, 110],
   TYOP [0, 1, 112], TYOP [0, 14, 114], TYOP [0, 47, 75], TYOP [0, 23, 79],
   TYOP [0, 15, 80], TYOP [0, 70, 71], TYOP [0, 65, 66], TYOP [0, 68, 69],
   TYOP [0, 73, 74], TYOP [0, 2, 81], TYOP [0, 93, 63], TYOP [0, 186, 63],
   TYOP [0, 100, 63], TYOP [0, 188, 63], TYOP [0, 44, 63],
   TYOP [0, 190, 63], TYOP [0, 42, 63], TYOP [0, 192, 63],
   TYOP [0, 36, 63], TYOP [0, 194, 63], TYOP [0, 94, 63],
   TYOP [0, 196, 63], TYOP [0, 101, 63], TYOP [0, 198, 63],
   TYOP [0, 95, 63], TYOP [0, 200, 63], TYOP [0, 102, 63],
   TYOP [0, 202, 63], TYOP [0, 96, 63], TYOP [0, 204, 63],
   TYOP [0, 103, 63], TYOP [0, 206, 63], TYOP [0, 63, 38], TYOP [0, 0, 70],
   TYOP [0, 209, 70], TYOP [0, 14, 210], TYOP [0, 0, 211], TYOP [0, 0, 65],
   TYOP [0, 213, 65], TYOP [0, 64, 214], TYOP [0, 0, 215], TYOP [0, 0, 68],
   TYOP [0, 217, 68], TYOP [0, 67, 218], TYOP [0, 0, 219], TYOP [0, 0, 73],
   TYOP [0, 221, 73], TYOP [0, 72, 222], TYOP [0, 0, 223],
   TYOP [0, 160, 190], TYOP [0, 160, 192], TYOP [0, 160, 194],
   TYOP [0, 71, 202], TYOP [0, 66, 188], TYOP [0, 69, 198],
   TYOP [0, 74, 206]]
  end
  val _ = Theory.incorporate_consts "OMNIType" tyvector
     [("state_size", 5), ("state_CASE", 12), ("returnToBase", 13),
      ("resupply", 13), ("reactToContact", 13), ("principal_size", 18),
      ("principal_CASE", 21), ("output_size", 26), ("output_CASE", 32),
      ("num2escState", 33), ("num2escOutput", 34), ("num2escCommand", 35),
      ("escState_size", 36), ("escState_CASE", 41), ("escState2num", 36),
      ("escOutput_size", 42), ("escOutput_CASE", 43),
      ("escOutput2num", 42), ("escCommand_size", 44),
      ("escCommand_CASE", 45), ("escCommand2num", 44),
      ("command_size", 50), ("command_CASE", 55), ("changeMission", 13),
      ("SR", 56), ("SLs", 57), ("SLo", 58), ("SLc", 59),
      ("ReturnToBase", 29), ("Resupply", 29), ("ReactToContact", 29),
      ("RTC", 9), ("RTB", 9), ("RESUPPLY", 9), ("ESCs", 60), ("ESCo", 61),
      ("ESCc", 62), ("ChangeMission", 29), ("CM", 9)];

  local open SharingTables
  in
  val tmvector = build_term_vector idvector tyvector
  [TMV("'command'", 66), TMV("'output'", 69), TMV("'principal'", 71),
   TMV("'state'", 74), TMV("M", 47), TMV("M", 13), TMV("M", 29),
   TMV("M", 9), TMV("M", 23), TMV("M", 15), TMV("M", 2), TMV("M'", 47),
   TMV("M'", 13), TMV("M'", 29), TMV("M'", 9), TMV("M'", 23),
   TMV("M'", 15), TMV("M'", 2), TMV("P", 75), TMV("P", 76), TMV("P", 77),
   TMV("P", 78), TMV("P", 79), TMV("P", 80), TMV("P", 81), TMV("a", 46),
   TMV("a", 22), TMV("a", 1), TMV("a", 14), TMV("a", 13), TMV("a", 29),
   TMV("a", 9), TMV("a'", 46), TMV("a'", 22), TMV("a'", 1), TMV("a'", 14),
   TMV("a'", 13), TMV("a'", 29), TMV("a'", 9), TMV("a0", 70),
   TMV("a0", 65), TMV("a0", 68), TMV("a0", 73), TMV("c", 47),
   TMV("cc", 47), TMV("command", 83), TMV("e", 13), TMV("e", 29),
   TMV("e", 9), TMV("escCommand", 86), TMV("escOutput", 89),
   TMV("escState", 92), TMV("f", 49), TMV("f", 25), TMV("f", 4),
   TMV("f", 19), TMV("f", 17), TMV("f", 53), TMV("f", 30), TMV("f", 10),
   TMV("f'", 19), TMV("f'", 53), TMV("f'", 30), TMV("f'", 10),
   TMV("f0", 53), TMV("f0", 30), TMV("f0", 10), TMV("f1", 51),
   TMV("f1", 27), TMV("f1", 7), TMV("f1'", 51), TMV("f1'", 27),
   TMV("f1'", 7), TMV("fn", 93), TMV("fn", 94), TMV("fn", 95),
   TMV("fn", 96), TMV("m", 0), TMV("n", 0), TMV("o", 23), TMV("oo", 23),
   TMV("output", 98), TMV("p", 15), TMV("pp", 15), TMV("principal", 99),
   TMV("r", 0), TMV("r'", 0), TMV("rep", 100), TMV("rep", 44),
   TMV("rep", 42), TMV("rep", 36), TMV("rep", 101), TMV("rep", 102),
   TMV("rep", 103), TMV("s", 46), TMV("s", 22), TMV("s", 1), TMV("s", 14),
   TMV("s", 2), TMV("ss", 2), TMV("state", 105), TMV("v0", 6),
   TMV("v0'", 6), TMV("v1", 6), TMV("v1'", 6), TMV("v2", 6), TMV("v2'", 6),
   TMV("v3", 6), TMV("v3'", 6), TMV("x", 13), TMV("x", 29), TMV("x", 9),
   TMV("x0", 6), TMV("x1", 6), TMV("x2", 6), TMV("x3", 6), TMC(12, 107),
   TMC(12, 109), TMC(12, 111), TMC(12, 113), TMC(12, 115), TMC(12, 116),
   TMC(12, 117), TMC(12, 118), TMC(12, 119), TMC(12, 121), TMC(12, 123),
   TMC(12, 125), TMC(12, 127), TMC(12, 129), TMC(12, 131), TMC(12, 133),
   TMC(12, 135), TMC(12, 136), TMC(12, 138), TMC(12, 139), TMC(12, 141),
   TMC(12, 142), TMC(12, 144), TMC(12, 145), TMC(12, 147), TMC(12, 149),
   TMC(12, 151), TMC(12, 153), TMC(12, 155), TMC(12, 157), TMC(12, 159),
   TMC(12, 161), TMC(12, 146), TMC(12, 148), TMC(12, 150), TMC(12, 152),
   TMC(12, 154), TMC(12, 156), TMC(12, 158), TMC(13, 163), TMC(14, 165),
   TMC(14, 167), TMC(14, 169), TMC(15, 171), TMC(16, 0), TMC(17, 172),
   TMC(18, 173), TMC(18, 174), TMC(18, 175), TMC(18, 176), TMC(18, 177),
   TMC(18, 171), TMC(18, 178), TMC(18, 84), TMC(18, 87), TMC(18, 90),
   TMC(18, 172), TMC(18, 179), TMC(18, 180), TMC(18, 181), TMC(18, 182),
   TMC(18, 183), TMC(18, 184), TMC(18, 185), TMC(19, 171), TMC(20, 109),
   TMC(20, 111), TMC(20, 113), TMC(20, 115), TMC(20, 117), TMC(20, 118),
   TMC(20, 119), TMC(20, 187), TMC(20, 189), TMC(20, 138), TMC(20, 191),
   TMC(20, 141), TMC(20, 193), TMC(20, 144), TMC(20, 195), TMC(20, 197),
   TMC(20, 199), TMC(20, 201), TMC(20, 203), TMC(20, 205), TMC(20, 207),
   TMC(20, 161), TMC(21, 46), TMC(21, 22), TMC(21, 1), TMC(21, 13),
   TMC(21, 29), TMC(21, 9), TMC(22, 162), TMC(23, 162), TMC(24, 70),
   TMC(24, 65), TMC(24, 68), TMC(24, 73), TMC(25, 9), TMC(26, 208),
   TMC(27, 212), TMC(27, 216), TMC(27, 220), TMC(27, 224), TMC(28, 29),
   TMC(29, 170), TMC(30, 62), TMC(31, 61), TMC(32, 60), TMC(33, 162),
   TMC(34, 9), TMC(35, 9), TMC(36, 9), TMC(37, 29), TMC(38, 29),
   TMC(39, 29), TMC(40, 59), TMC(41, 58), TMC(42, 57), TMC(43, 56),
   TMC(44, 162), TMC(45, 225), TMC(45, 226), TMC(45, 227), TMC(45, 228),
   TMC(45, 229), TMC(45, 230), TMC(45, 231), TMC(46, 0), TMC(47, 171),
   TMC(48, 13), TMC(49, 55), TMC(50, 50), TMC(51, 44), TMC(52, 45),
   TMC(53, 44), TMC(54, 42), TMC(55, 43), TMC(56, 42), TMC(57, 36),
   TMC(58, 41), TMC(59, 36), TMC(60, 35), TMC(61, 34), TMC(62, 33),
   TMC(63, 32), TMC(64, 26), TMC(65, 21), TMC(66, 18), TMC(67, 13),
   TMC(68, 13), TMC(69, 13), TMC(70, 12), TMC(71, 5), TMC(72, 170)]
  end
  structure ThmBind = struct
    val DT = Thm.disk_thm
    val read = Term.read_raw tmvector
  end
  fun op escCommand_TY_DEF x = x
    val op escCommand_TY_DEF =
    ThmBind.DT(((("OMNIType",0),
                [("bool",[25]),("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%191%88%238%78%161$0@%226%210%209%245@4|@$0@|@"])
  fun op escCommand_BIJ x = x
    val op escCommand_BIJ =
    ThmBind.DT(((("OMNIType",1),
                [("OMNIType",[0]),("bool",[116])]),["DISK_THM"]),
               [ThmBind.read"%159%122%29%169%259%250$0@3$0@|@2%147%85%167%78%161$0@%226%210%209%245@4|$0@2%172%250%259$0@3$0@2|@2"])




  fun op escCommand_size_def x = x
    val op escCommand_size_def =
    ThmBind.DT(((("OMNIType",15),[]),[]),
               [ThmBind.read"%122%109%172%252$0@2%160@|@"])
  fun op escCommand_CASE x = x
    val op escCommand_CASE =
    ThmBind.DT(((("OMNIType",16),[]),[]),
               [ThmBind.read"%122%109%116%101%116%103%116%105%116%107%162%251$4@$3@$2@$1@$0@2%77%216%161$0@%226%209%245@4$4@%216%161$0@%226%210%245@4$3@%216%172$0@%226%210%245@4$2@$1@3|%250$4@3|@|@|@|@|@"])
  fun op command_TY_DEF x = x
    val op command_TY_DEF =
    ThmBind.DT(((("OMNIType",24),[("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%189%87%242%40%143%0%180%151%40%180%246%185%29%176$1@%29%218%160@%156$0@%203@2%78%212|@|$0@2|@2%181%25%176$1@%25%218%237%160@2%156%206@$0@2%78%212|@|$0@2|@3$1$0@2|@2$0$1@2|@|@$0@|@"])
  fun op command_case_def x = x
    val op command_case_def =
    ThmBind.DT(((("OMNIType",30),
                [("OMNIType",[25,26,27,28,29]),("bool",[26,180]),
                 ("ind_type",[33,34]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%159%122%29%134%57%125%67%162%248%223$2@2$1@$0@2$1$2@2|@|@|@2%117%25%134%57%125%67%162%248%233$2@2$1@$0@2$0$2@2|@|@|@2"])
  fun op command_size_def x = x
    val op command_size_def =
    ThmBind.DT(((("OMNIType",31),
                [("OMNIType",[25,26,27,28,29]),("bool",[26,180]),
                 ("ind_type",[33,34]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%159%126%52%122%29%172%249$1@%223$0@3%155%226%209%245@3%252$0@3|@|@2%126%52%117%25%172%249$1@%233$0@3%155%226%209%245@3$1$0@3|@|@2"])
  fun op escState_TY_DEF x = x
    val op escState_TY_DEF =
    ThmBind.DT(((("OMNIType",42),
                [("bool",[25]),("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%195%90%240%78%161$0@%226%210%209%245@4|@$0@|@"])
  fun op escState_BIJ x = x
    val op escState_BIJ =
    ThmBind.DT(((("OMNIType",43),
                [("OMNIType",[42]),("bool",[116])]),["DISK_THM"]),
               [ThmBind.read"%159%124%31%171%261%256$0@3$0@|@2%147%85%167%78%161$0@%226%210%209%245@4|$0@2%172%256%261$0@3$0@2|@2"])




  fun op escState_size_def x = x
    val op escState_size_def =
    ThmBind.DT(((("OMNIType",57),[]),[]),
               [ThmBind.read"%124%111%172%258$0@2%160@|@"])
  fun op escState_CASE x = x
    val op escState_CASE =
    ThmBind.DT(((("OMNIType",58),[]),[]),
               [ThmBind.read"%124%111%116%101%116%103%116%105%116%107%162%257$4@$3@$2@$1@$0@2%77%216%161$0@%226%209%245@4$4@%216%161$0@%226%210%245@4$3@%216%172$0@%226%210%245@4$2@$1@3|%256$4@3|@|@|@|@|@"])
  fun op state_TY_DEF x = x
    val op state_TY_DEF =
    ThmBind.DT(((("OMNIType",67),[("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%201%93%244%42%145%3%180%153%42%180%246%187%31%178$1@%31%220%160@%158$0@%205@2%78%214|@|$0@2|@2%183%27%178$1@%27%220%237%160@2%158%208@$0@2%78%214|@|$0@2|@3$1$0@2|@2$0$1@2|@|@$0@|@"])
  fun op state_case_def x = x
    val op state_case_def =
    ThmBind.DT(((("OMNIType",73),
                [("OMNIType",[68,69,70,71,72]),("bool",[26,180]),
                 ("ind_type",[33,34]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%159%124%31%138%59%129%69%162%269%225$2@2$1@$0@2$1$2@2|@|@|@2%119%27%138%59%129%69%162%269%235$2@2$1@$0@2$0$2@2|@|@|@2"])
  fun op state_size_def x = x
    val op state_size_def =
    ThmBind.DT(((("OMNIType",74),
                [("OMNIType",[68,69,70,71,72]),("bool",[26,180]),
                 ("ind_type",[33,34]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%159%130%54%124%31%172%270$1@%225$0@3%155%226%209%245@3%258$0@3|@|@2%130%54%119%27%172%270$1@%235$0@3%155%226%209%245@3$1$0@3|@|@2"])
  fun op escOutput_TY_DEF x = x
    val op escOutput_TY_DEF =
    ThmBind.DT(((("OMNIType",84),
                [("bool",[25]),("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%193%89%239%78%161$0@%226%210%209%245@4|@$0@|@"])
  fun op escOutput_BIJ x = x
    val op escOutput_BIJ =
    ThmBind.DT(((("OMNIType",85),
                [("OMNIType",[84]),("bool",[116])]),["DISK_THM"]),
               [ThmBind.read"%159%123%30%170%260%253$0@3$0@|@2%147%85%167%78%161$0@%226%210%209%245@4|$0@2%172%253%260$0@3$0@2|@2"])




  fun op escOutput_size_def x = x
    val op escOutput_size_def =
    ThmBind.DT(((("OMNIType",99),[]),[]),
               [ThmBind.read"%123%110%172%255$0@2%160@|@"])
  fun op escOutput_CASE x = x
    val op escOutput_CASE =
    ThmBind.DT(((("OMNIType",100),[]),[]),
               [ThmBind.read"%123%110%116%101%116%103%116%105%116%107%162%254$4@$3@$2@$1@$0@2%77%216%161$0@%226%209%245@4$4@%216%161$0@%226%210%245@4$3@%216%172$0@%226%210%245@4$2@$1@3|%253$4@3|@|@|@|@|@"])
  fun op output_TY_DEF x = x
    val op output_TY_DEF =
    ThmBind.DT(((("OMNIType",109),[("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%197%91%243%41%144%1%180%152%41%180%246%186%30%177$1@%30%219%160@%157$0@%204@2%78%213|@|$0@2|@2%182%26%177$1@%26%219%237%160@2%157%207@$0@2%78%213|@|$0@2|@3$1$0@2|@2$0$1@2|@|@$0@|@"])
  fun op output_case_def x = x
    val op output_case_def =
    ThmBind.DT(((("OMNIType",115),
                [("OMNIType",[110,111,112,113,114]),("bool",[26,180]),
                 ("ind_type",[33,34]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%159%123%30%136%58%127%68%162%262%224$2@2$1@$0@2$1$2@2|@|@|@2%118%26%136%58%127%68%162%262%234$2@2$1@$0@2$0$2@2|@|@|@2"])
  fun op output_size_def x = x
    val op output_size_def =
    ThmBind.DT(((("OMNIType",116),
                [("OMNIType",[110,111,112,113,114]),("bool",[26,180]),
                 ("ind_type",[33,34]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%159%128%53%123%30%172%263$1@%224$0@3%155%226%209%245@3%255$0@3|@|@2%128%53%118%26%172%263$1@%234$0@3%155%226%209%245@3$1$0@3|@|@2"])
  fun op principal_TY_DEF x = x
    val op principal_TY_DEF =
    ThmBind.DT(((("OMNIType",126),[("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%199%92%241%39%142%2%180%150%39%180%184%28%175$1@%28%217%160@$0@%78%211|@|$0@2|@2$1$0@2|@2$0$1@2|@|@$0@|@"])
  fun op principal_case_def x = x
    val op principal_case_def =
    ThmBind.DT(((("OMNIType",130),
                [("OMNIType",[127,128,129]),("bool",[26,180]),
                 ("ind_type",[33,34])]),["DISK_THM"]),
               [ThmBind.read"%120%28%131%55%162%264%236$1@2$0@2$0$1@2|@|@"])
  fun op principal_size_def x = x
    val op principal_size_def =
    ThmBind.DT(((("OMNIType",131),
                [("OMNIType",[127,128,129]),("bool",[26,180]),
                 ("ind_type",[33,34])]),["DISK_THM"]),
               [ThmBind.read"%132%56%120%28%172%265$1@%236$0@3%155%226%209%245@3$1$0@3|@|@"])
  fun op num2escCommand_escCommand2num x = x
    val op num2escCommand_escCommand2num =
    ThmBind.DT(((("OMNIType",2),[("OMNIType",[1])]),["DISK_THM"]),
               [ThmBind.read"%122%29%169%259%250$0@3$0@|@"])
  fun op escCommand2num_num2escCommand x = x
    val op escCommand2num_num2escCommand =
    ThmBind.DT(((("OMNIType",3),[("OMNIType",[1])]),["DISK_THM"]),
               [ThmBind.read"%147%85%167%161$0@%226%210%209%245@5%172%250%259$0@3$0@2|@"])
  fun op num2escCommand_11 x = x
    val op num2escCommand_11 =
    ThmBind.DT(((("OMNIType",4),
                [("OMNIType",[1]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%147%85%147%86%180%161$1@%226%210%209%245@5%180%161$0@%226%210%209%245@5%167%169%259$1@2%259$0@3%172$1@$0@4|@|@"])
  fun op escCommand2num_11 x = x
    val op escCommand2num_11 =
    ThmBind.DT(((("OMNIType",5),
                [("OMNIType",[1]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%122%29%122%36%167%172%250$1@2%250$0@3%169$1@$0@2|@|@"])
  fun op num2escCommand_ONTO x = x
    val op num2escCommand_ONTO =
    ThmBind.DT(((("OMNIType",6),
                [("OMNIType",[1]),("bool",[25,62])]),["DISK_THM"]),
               [ThmBind.read"%122%29%202%85%159%169$1@%259$0@3%161$0@%226%210%209%245@5|@|@"])
  fun op escCommand2num_ONTO x = x
    val op escCommand2num_ONTO =
    ThmBind.DT(((("OMNIType",7),
                [("OMNIType",[1]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%147%85%167%161$0@%226%210%209%245@5%185%29%172$1@%250$0@2|@2|@"])
  fun op num2escCommand_thm x = x
    val op num2escCommand_thm =
    ThmBind.DT(((("OMNIType",12),[("OMNIType",[8,9,10,11])]),[]),
               [ThmBind.read"%159%169%259%160@2%268@2%159%169%259%226%209%245@4%247@2%159%169%259%226%210%245@4%267@2%169%259%226%209%209%245@5%266@4"])
  fun op escCommand2num_thm x = x
    val op escCommand2num_thm =
    ThmBind.DT(((("OMNIType",13),
                [("OMNIType",[3,8,9,10,11]),("bool",[25,53]),
                 ("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%159%172%250%268@2%160@2%159%172%250%247@2%226%209%245@4%159%172%250%267@2%226%210%245@4%172%250%266@2%226%209%209%245@7"])
  fun op escCommand_EQ_escCommand x = x
    val op escCommand_EQ_escCommand =
    ThmBind.DT(((("OMNIType",14),
                [("OMNIType",[5]),("bool",[57])]),["DISK_THM"]),
               [ThmBind.read"%122%29%122%36%167%169$1@$0@2%172%250$1@2%250$0@3|@|@"])
  fun op escCommand_case_def x = x
    val op escCommand_case_def =
    ThmBind.DT(((("OMNIType",17),
                [("OMNIType",[13,16]),("bool",[53,55,63]),
                 ("numeral",[3,6,7])]),["DISK_THM"]),
               [ThmBind.read"%159%116%101%116%103%116%105%116%107%162%251%268@$3@$2@$1@$0@2$3@|@|@|@|@2%159%116%101%116%103%116%105%116%107%162%251%247@$3@$2@$1@$0@2$2@|@|@|@|@2%159%116%101%116%103%116%105%116%107%162%251%267@$3@$2@$1@$0@2$1@|@|@|@|@2%116%101%116%103%116%105%116%107%162%251%266@$3@$2@$1@$0@2$0@|@|@|@|@4"])
  fun op datatype_escCommand x = x
    val op datatype_escCommand =
    ThmBind.DT(((("OMNIType",18),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%222%49%268@%247@%267@%266@2"])
  fun op escCommand_distinct x = x
    val op escCommand_distinct =
    ThmBind.DT(((("OMNIType",19),
                [("OMNIType",[13,14]),("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%159%271%169%268@%247@3%159%271%169%268@%267@3%159%271%169%268@%266@3%159%271%169%247@%267@3%159%271%169%247@%266@3%271%169%267@%266@7"])
  fun op escCommand_case_cong x = x
    val op escCommand_case_cong =
    ThmBind.DT(((("OMNIType",20),
                [("OMNIType",[6,8,9,10,11,17]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,178,179,183,186,275]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%122%5%122%12%116%101%116%103%116%105%116%107%180%159%169$5@$4@2%159%180%169$4@%268@2%162$3@%102@3%159%180%169$4@%247@2%162$2@%104@3%159%180%169$4@%267@2%162$1@%106@3%180%169$4@%266@2%162$0@%108@7%162%251$5@$3@$2@$1@$0@2%251$4@%102@%104@%106@%108@3|@|@|@|@|@|@"])
  fun op escCommand_nchotomy x = x
    val op escCommand_nchotomy =
    ThmBind.DT(((("OMNIType",21),
                [("OMNIType",[6,8,9,10,11]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,178,179,183,186,275]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%122%29%246%169$0@%268@2%246%169$0@%247@2%246%169$0@%267@2%169$0@%266@4|@"])
  fun op escCommand_Axiom x = x
    val op escCommand_Axiom =
    ThmBind.DT(((("OMNIType",22),
                [("OMNIType",[13]),("bool",[8,14,25,53,55,63]),
                 ("numeral",[3,8])]),["DISK_THM"]),
               [ThmBind.read"%116%112%116%113%116%114%116%115%190%57%159%162$0%268@2$4@2%159%162$0%247@2$3@2%159%162$0%267@2$2@2%162$0%266@2$1@4|@|@|@|@|@"])
  fun op escCommand_induction x = x
    val op escCommand_induction =
    ThmBind.DT(((("OMNIType",23),
                [("OMNIType",[6,8,9,10,11]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,178,179,183,186,275]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%135%19%180%159$0%247@2%159$0%266@2%159$0%267@2$0%268@5%122%29$1$0@|@2|@"])
  fun op datatype_command x = x
    val op datatype_command =
    ThmBind.DT(((("OMNIType",32),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%222%45%223@%233@2"])
  fun op command_11 x = x
    val op command_11 =
    ThmBind.DT(((("OMNIType",33),
                [("OMNIType",[25,26,27,28,29]),("bool",[26,55,62,180]),
                 ("ind_type",[33,34]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%159%122%29%122%36%167%168%223$1@2%223$0@3%169$1@$0@2|@|@2%117%25%117%32%167%168%233$1@2%233$0@3%163$1@$0@2|@|@2"])
  fun op command_distinct x = x
    val op command_distinct =
    ThmBind.DT(((("OMNIType",34),
                [("OMNIType",[25,26,27,28,29]),
                 ("bool",[25,26,46,53,62,180]),("ind_type",[33,34]),
                 ("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%117%32%122%29%271%168%223$0@2%233$1@3|@|@"])
  fun op command_case_cong x = x
    val op command_case_cong =
    ThmBind.DT(((("OMNIType",35),
                [("OMNIType",[25,26,27,28,29,30]),
                 ("bool",[26,180])]),["DISK_THM"]),
               [ThmBind.read"%121%4%121%11%134%57%125%67%180%159%168$3@$2@2%159%122%29%180%168$3@%223$0@3%162$2$0@2%61$0@3|@2%117%25%180%168$3@%233$0@3%162$1$0@2%70$0@3|@4%162%248$3@$1@$0@2%248$2@%61@%70@3|@|@|@|@"])
  fun op command_nchotomy x = x
    val op command_nchotomy =
    ThmBind.DT(((("OMNIType",36),
                [("OMNIType",[25,26,27,28,29]),
                 ("bool",[26,180])]),["DISK_THM"]),
               [ThmBind.read"%121%44%246%185%46%168$1@%223$0@2|@2%181%94%168$1@%233$0@2|@2|@"])
  fun op command_Axiom x = x
    val op command_Axiom =
    ThmBind.DT(((("OMNIType",37),
                [("OMNIType",[25,26,27,28,29]),("bool",[26,180]),
                 ("ind_type",[33,34]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%134%64%125%67%188%73%159%122%29%162$1%223$0@3$3$0@2|@2%117%25%162$1%233$0@3$2$0@2|@2|@|@|@"])
  fun op command_induction x = x
    val op command_induction =
    ThmBind.DT(((("OMNIType",38),
                [("OMNIType",[25,26,27,28,29]),
                 ("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%133%18%180%159%122%46$1%223$0@2|@2%117%94$1%233$0@2|@3%121%43$1$0@|@2|@"])
  fun op escCommand_distinct_clauses x = x
    val op escCommand_distinct_clauses =
    ThmBind.DT(((("OMNIType",39),
                [("OMNIType",[13,14]),("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%159%271%169%268@%247@3%159%271%169%268@%267@3%159%271%169%268@%266@3%159%271%169%247@%267@3%159%271%169%247@%266@3%271%169%267@%266@7"])
  fun op command_distinct_clauses x = x
    val op command_distinct_clauses =
    ThmBind.DT(((("OMNIType",40),
                [("OMNIType",[25,26,27,28,29]),
                 ("bool",[25,26,46,53,62,180]),("ind_type",[33,34]),
                 ("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%117%32%122%29%271%168%223$0@2%233$1@3|@|@"])
  fun op command_one_one x = x
    val op command_one_one =
    ThmBind.DT(((("OMNIType",41),
                [("OMNIType",[25,26,27,28,29]),("bool",[26,55,62,180]),
                 ("ind_type",[33,34]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%159%122%29%122%36%167%168%223$1@2%223$0@3%169$1@$0@2|@|@2%117%25%117%32%167%168%233$1@2%233$0@3%163$1@$0@2|@|@2"])
  fun op num2escState_escState2num x = x
    val op num2escState_escState2num =
    ThmBind.DT(((("OMNIType",44),[("OMNIType",[43])]),["DISK_THM"]),
               [ThmBind.read"%124%31%171%261%256$0@3$0@|@"])
  fun op escState2num_num2escState x = x
    val op escState2num_num2escState =
    ThmBind.DT(((("OMNIType",45),[("OMNIType",[43])]),["DISK_THM"]),
               [ThmBind.read"%147%85%167%161$0@%226%210%209%245@5%172%256%261$0@3$0@2|@"])
  fun op num2escState_11 x = x
    val op num2escState_11 =
    ThmBind.DT(((("OMNIType",46),
                [("OMNIType",[43]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%147%85%147%86%180%161$1@%226%210%209%245@5%180%161$0@%226%210%209%245@5%167%171%261$1@2%261$0@3%172$1@$0@4|@|@"])
  fun op escState2num_11 x = x
    val op escState2num_11 =
    ThmBind.DT(((("OMNIType",47),
                [("OMNIType",[43]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%124%31%124%38%167%172%256$1@2%256$0@3%171$1@$0@2|@|@"])
  fun op num2escState_ONTO x = x
    val op num2escState_ONTO =
    ThmBind.DT(((("OMNIType",48),
                [("OMNIType",[43]),("bool",[25,62])]),["DISK_THM"]),
               [ThmBind.read"%124%31%202%85%159%171$1@%261$0@3%161$0@%226%210%209%245@5|@|@"])
  fun op escState2num_ONTO x = x
    val op escState2num_ONTO =
    ThmBind.DT(((("OMNIType",49),
                [("OMNIType",[43]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%147%85%167%161$0@%226%210%209%245@5%187%31%172$1@%256$0@2|@2|@"])
  fun op num2escState_thm x = x
    val op num2escState_thm =
    ThmBind.DT(((("OMNIType",54),[("OMNIType",[50,51,52,53])]),[]),
               [ThmBind.read"%159%171%261%160@2%228@2%159%171%261%226%209%245@4%215@2%159%171%261%226%210%245@4%227@2%171%261%226%209%209%245@5%229@4"])
  fun op escState2num_thm x = x
    val op escState2num_thm =
    ThmBind.DT(((("OMNIType",55),
                [("OMNIType",[45,50,51,52,53]),("bool",[25,53]),
                 ("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%159%172%256%228@2%160@2%159%172%256%215@2%226%209%245@4%159%172%256%227@2%226%210%245@4%172%256%229@2%226%209%209%245@7"])
  fun op escState_EQ_escState x = x
    val op escState_EQ_escState =
    ThmBind.DT(((("OMNIType",56),
                [("OMNIType",[47]),("bool",[57])]),["DISK_THM"]),
               [ThmBind.read"%124%31%124%38%167%171$1@$0@2%172%256$1@2%256$0@3|@|@"])
  fun op escState_case_def x = x
    val op escState_case_def =
    ThmBind.DT(((("OMNIType",59),
                [("OMNIType",[55,58]),("bool",[53,55,63]),
                 ("numeral",[3,6,7])]),["DISK_THM"]),
               [ThmBind.read"%159%116%101%116%103%116%105%116%107%162%257%228@$3@$2@$1@$0@2$3@|@|@|@|@2%159%116%101%116%103%116%105%116%107%162%257%215@$3@$2@$1@$0@2$2@|@|@|@|@2%159%116%101%116%103%116%105%116%107%162%257%227@$3@$2@$1@$0@2$1@|@|@|@|@2%116%101%116%103%116%105%116%107%162%257%229@$3@$2@$1@$0@2$0@|@|@|@|@4"])
  fun op datatype_escState x = x
    val op datatype_escState =
    ThmBind.DT(((("OMNIType",60),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%222%51%228@%215@%227@%229@2"])
  fun op escState_distinct x = x
    val op escState_distinct =
    ThmBind.DT(((("OMNIType",61),
                [("OMNIType",[55,56]),("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%159%271%171%228@%215@3%159%271%171%228@%227@3%159%271%171%228@%229@3%159%271%171%215@%227@3%159%271%171%215@%229@3%271%171%227@%229@7"])
  fun op escState_case_cong x = x
    val op escState_case_cong =
    ThmBind.DT(((("OMNIType",62),
                [("OMNIType",[48,50,51,52,53,59]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,178,179,183,186,275]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%124%7%124%14%116%101%116%103%116%105%116%107%180%159%171$5@$4@2%159%180%171$4@%228@2%162$3@%102@3%159%180%171$4@%215@2%162$2@%104@3%159%180%171$4@%227@2%162$1@%106@3%180%171$4@%229@2%162$0@%108@7%162%257$5@$3@$2@$1@$0@2%257$4@%102@%104@%106@%108@3|@|@|@|@|@|@"])
  fun op escState_nchotomy x = x
    val op escState_nchotomy =
    ThmBind.DT(((("OMNIType",63),
                [("OMNIType",[48,50,51,52,53]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,178,179,183,186,275]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%124%31%246%171$0@%228@2%246%171$0@%215@2%246%171$0@%227@2%171$0@%229@4|@"])
  fun op escState_Axiom x = x
    val op escState_Axiom =
    ThmBind.DT(((("OMNIType",64),
                [("OMNIType",[55]),("bool",[8,14,25,53,55,63]),
                 ("numeral",[3,8])]),["DISK_THM"]),
               [ThmBind.read"%116%112%116%113%116%114%116%115%194%59%159%162$0%228@2$4@2%159%162$0%215@2$3@2%159%162$0%227@2$2@2%162$0%229@2$1@4|@|@|@|@|@"])
  fun op escState_induction x = x
    val op escState_induction =
    ThmBind.DT(((("OMNIType",65),
                [("OMNIType",[48,50,51,52,53]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,178,179,183,186,275]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%139%21%180%159$0%215@2%159$0%227@2%159$0%228@2$0%229@5%124%31$1$0@|@2|@"])
  fun op escState_distinct_clauses x = x
    val op escState_distinct_clauses =
    ThmBind.DT(((("OMNIType",66),
                [("OMNIType",[55,56]),("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%159%271%171%228@%215@3%159%271%171%228@%227@3%159%271%171%228@%229@3%159%271%171%215@%227@3%159%271%171%215@%229@3%271%171%227@%229@7"])
  fun op datatype_state x = x
    val op datatype_state =
    ThmBind.DT(((("OMNIType",75),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%222%100%225@%235@2"])
  fun op state_11 x = x
    val op state_11 =
    ThmBind.DT(((("OMNIType",76),
                [("OMNIType",[68,69,70,71,72]),("bool",[26,55,62,180]),
                 ("ind_type",[33,34]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%159%124%31%124%38%167%179%225$1@2%225$0@3%171$1@$0@2|@|@2%119%27%119%34%167%179%235$1@2%235$0@3%165$1@$0@2|@|@2"])
  fun op state_distinct x = x
    val op state_distinct =
    ThmBind.DT(((("OMNIType",77),
                [("OMNIType",[68,69,70,71,72]),
                 ("bool",[25,26,46,53,62,180]),("ind_type",[33,34]),
                 ("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%119%34%124%31%271%179%225$0@2%235$1@3|@|@"])
  fun op state_case_cong x = x
    val op state_case_cong =
    ThmBind.DT(((("OMNIType",78),
                [("OMNIType",[68,69,70,71,72,73]),
                 ("bool",[26,180])]),["DISK_THM"]),
               [ThmBind.read"%154%10%154%17%138%59%129%69%180%159%179$3@$2@2%159%124%31%180%179$3@%225$0@3%162$2$0@2%63$0@3|@2%119%27%180%179$3@%235$0@3%162$1$0@2%72$0@3|@4%162%269$3@$1@$0@2%269$2@%63@%72@3|@|@|@|@"])
  fun op state_nchotomy x = x
    val op state_nchotomy =
    ThmBind.DT(((("OMNIType",79),
                [("OMNIType",[68,69,70,71,72]),
                 ("bool",[26,180])]),["DISK_THM"]),
               [ThmBind.read"%154%99%246%187%48%179$1@%225$0@2|@2%183%96%179$1@%235$0@2|@2|@"])
  fun op state_Axiom x = x
    val op state_Axiom =
    ThmBind.DT(((("OMNIType",80),
                [("OMNIType",[68,69,70,71,72]),("bool",[26,180]),
                 ("ind_type",[33,34]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%138%66%129%69%200%76%159%124%31%162$1%225$0@3$3$0@2|@2%119%27%162$1%235$0@3$2$0@2|@2|@|@|@"])
  fun op state_induction x = x
    val op state_induction =
    ThmBind.DT(((("OMNIType",81),
                [("OMNIType",[68,69,70,71,72]),
                 ("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%146%24%180%159%124%48$1%225$0@2|@2%119%96$1%235$0@2|@3%154%98$1$0@|@2|@"])
  fun op state_distinct_clauses x = x
    val op state_distinct_clauses =
    ThmBind.DT(((("OMNIType",82),
                [("OMNIType",[68,69,70,71,72]),
                 ("bool",[25,26,46,53,62,180]),("ind_type",[33,34]),
                 ("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%119%34%124%31%271%179%225$0@2%235$1@3|@|@"])
  fun op state_one_one x = x
    val op state_one_one =
    ThmBind.DT(((("OMNIType",83),
                [("OMNIType",[68,69,70,71,72]),("bool",[26,55,62,180]),
                 ("ind_type",[33,34]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%159%124%31%124%38%167%179%225$1@2%225$0@3%171$1@$0@2|@|@2%119%27%119%34%167%179%235$1@2%235$0@3%165$1@$0@2|@|@2"])
  fun op num2escOutput_escOutput2num x = x
    val op num2escOutput_escOutput2num =
    ThmBind.DT(((("OMNIType",86),[("OMNIType",[85])]),["DISK_THM"]),
               [ThmBind.read"%123%30%170%260%253$0@3$0@|@"])
  fun op escOutput2num_num2escOutput x = x
    val op escOutput2num_num2escOutput =
    ThmBind.DT(((("OMNIType",87),[("OMNIType",[85])]),["DISK_THM"]),
               [ThmBind.read"%147%85%167%161$0@%226%210%209%245@5%172%253%260$0@3$0@2|@"])
  fun op num2escOutput_11 x = x
    val op num2escOutput_11 =
    ThmBind.DT(((("OMNIType",88),
                [("OMNIType",[85]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%147%85%147%86%180%161$1@%226%210%209%245@5%180%161$0@%226%210%209%245@5%167%170%260$1@2%260$0@3%172$1@$0@4|@|@"])
  fun op escOutput2num_11 x = x
    val op escOutput2num_11 =
    ThmBind.DT(((("OMNIType",89),
                [("OMNIType",[85]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%123%30%123%37%167%172%253$1@2%253$0@3%170$1@$0@2|@|@"])
  fun op num2escOutput_ONTO x = x
    val op num2escOutput_ONTO =
    ThmBind.DT(((("OMNIType",90),
                [("OMNIType",[85]),("bool",[25,62])]),["DISK_THM"]),
               [ThmBind.read"%123%30%202%85%159%170$1@%260$0@3%161$0@%226%210%209%245@5|@|@"])
  fun op escOutput2num_ONTO x = x
    val op escOutput2num_ONTO =
    ThmBind.DT(((("OMNIType",91),
                [("OMNIType",[85]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%147%85%167%161$0@%226%210%209%245@5%186%30%172$1@%253$0@2|@2|@"])
  fun op num2escOutput_thm x = x
    val op num2escOutput_thm =
    ThmBind.DT(((("OMNIType",96),[("OMNIType",[92,93,94,95])]),[]),
               [ThmBind.read"%159%170%260%160@2%232@2%159%170%260%226%209%245@4%221@2%159%170%260%226%210%245@4%231@2%170%260%226%209%209%245@5%230@4"])
  fun op escOutput2num_thm x = x
    val op escOutput2num_thm =
    ThmBind.DT(((("OMNIType",97),
                [("OMNIType",[87,92,93,94,95]),("bool",[25,53]),
                 ("numeral",[3,7])]),["DISK_THM"]),
               [ThmBind.read"%159%172%253%232@2%160@2%159%172%253%221@2%226%209%245@4%159%172%253%231@2%226%210%245@4%172%253%230@2%226%209%209%245@7"])
  fun op escOutput_EQ_escOutput x = x
    val op escOutput_EQ_escOutput =
    ThmBind.DT(((("OMNIType",98),
                [("OMNIType",[89]),("bool",[57])]),["DISK_THM"]),
               [ThmBind.read"%123%30%123%37%167%170$1@$0@2%172%253$1@2%253$0@3|@|@"])
  fun op escOutput_case_def x = x
    val op escOutput_case_def =
    ThmBind.DT(((("OMNIType",101),
                [("OMNIType",[97,100]),("bool",[53,55,63]),
                 ("numeral",[3,6,7])]),["DISK_THM"]),
               [ThmBind.read"%159%116%101%116%103%116%105%116%107%162%254%232@$3@$2@$1@$0@2$3@|@|@|@|@2%159%116%101%116%103%116%105%116%107%162%254%221@$3@$2@$1@$0@2$2@|@|@|@|@2%159%116%101%116%103%116%105%116%107%162%254%231@$3@$2@$1@$0@2$1@|@|@|@|@2%116%101%116%103%116%105%116%107%162%254%230@$3@$2@$1@$0@2$0@|@|@|@|@4"])
  fun op datatype_escOutput x = x
    val op datatype_escOutput =
    ThmBind.DT(((("OMNIType",102),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%222%50%232@%221@%231@%230@2"])
  fun op escOutput_distinct x = x
    val op escOutput_distinct =
    ThmBind.DT(((("OMNIType",103),
                [("OMNIType",[97,98]),("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%159%271%170%232@%221@3%159%271%170%232@%231@3%159%271%170%232@%230@3%159%271%170%221@%231@3%159%271%170%221@%230@3%271%170%231@%230@7"])
  fun op escOutput_case_cong x = x
    val op escOutput_case_cong =
    ThmBind.DT(((("OMNIType",104),
                [("OMNIType",[90,92,93,94,95,101]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,178,179,183,186,275]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%123%6%123%13%116%101%116%103%116%105%116%107%180%159%170$5@$4@2%159%180%170$4@%232@2%162$3@%102@3%159%180%170$4@%221@2%162$2@%104@3%159%180%170$4@%231@2%162$1@%106@3%180%170$4@%230@2%162$0@%108@7%162%254$5@$3@$2@$1@$0@2%254$4@%102@%104@%106@%108@3|@|@|@|@|@|@"])
  fun op escOutput_nchotomy x = x
    val op escOutput_nchotomy =
    ThmBind.DT(((("OMNIType",105),
                [("OMNIType",[90,92,93,94,95]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,178,179,183,186,275]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%123%30%246%170$0@%232@2%246%170$0@%221@2%246%170$0@%231@2%170$0@%230@4|@"])
  fun op escOutput_Axiom x = x
    val op escOutput_Axiom =
    ThmBind.DT(((("OMNIType",106),
                [("OMNIType",[97]),("bool",[8,14,25,53,55,63]),
                 ("numeral",[3,8])]),["DISK_THM"]),
               [ThmBind.read"%116%112%116%113%116%114%116%115%192%58%159%162$0%232@2$4@2%159%162$0%221@2$3@2%159%162$0%231@2$2@2%162$0%230@2$1@4|@|@|@|@|@"])
  fun op escOutput_induction x = x
    val op escOutput_induction =
    ThmBind.DT(((("OMNIType",107),
                [("OMNIType",[90,92,93,94,95]),
                 ("arithmetic",
                 [24,25,27,41,46,59,73,95,178,179,183,186,275]),
                 ("bool",
                 [8,14,25,31,35,42,50,51,53,57,62,63,92,95,100,103,104,
                  106]),("numeral",[3,5,6,7,8,15,16,17]),
                 ("sat",[1,3,5,6,7,11,12,13,15])]),["DISK_THM"]),
               [ThmBind.read"%137%20%180%159$0%221@2%159$0%230@2%159$0%231@2$0%232@5%123%30$1$0@|@2|@"])
  fun op escOutput_distinct_clauses x = x
    val op escOutput_distinct_clauses =
    ThmBind.DT(((("OMNIType",108),
                [("OMNIType",[97,98]),("numeral",[3,6])]),["DISK_THM"]),
               [ThmBind.read"%159%271%170%232@%221@3%159%271%170%232@%231@3%159%271%170%232@%230@3%159%271%170%221@%231@3%159%271%170%221@%230@3%271%170%231@%230@7"])
  fun op datatype_output x = x
    val op datatype_output =
    ThmBind.DT(((("OMNIType",117),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%222%81%224@%234@2"])
  fun op output_11 x = x
    val op output_11 =
    ThmBind.DT(((("OMNIType",118),
                [("OMNIType",[110,111,112,113,114]),
                 ("bool",[26,55,62,180]),("ind_type",[33,34]),
                 ("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%159%123%30%123%37%167%173%224$1@2%224$0@3%170$1@$0@2|@|@2%118%26%118%33%167%173%234$1@2%234$0@3%164$1@$0@2|@|@2"])
  fun op output_distinct x = x
    val op output_distinct =
    ThmBind.DT(((("OMNIType",119),
                [("OMNIType",[110,111,112,113,114]),
                 ("bool",[25,26,46,53,62,180]),("ind_type",[33,34]),
                 ("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%118%33%123%30%271%173%224$0@2%234$1@3|@|@"])
  fun op output_case_cong x = x
    val op output_case_cong =
    ThmBind.DT(((("OMNIType",120),
                [("OMNIType",[110,111,112,113,114,115]),
                 ("bool",[26,180])]),["DISK_THM"]),
               [ThmBind.read"%148%8%148%15%136%58%127%68%180%159%173$3@$2@2%159%123%30%180%173$3@%224$0@3%162$2$0@2%62$0@3|@2%118%26%180%173$3@%234$0@3%162$1$0@2%71$0@3|@4%162%262$3@$1@$0@2%262$2@%62@%71@3|@|@|@|@"])
  fun op output_nchotomy x = x
    val op output_nchotomy =
    ThmBind.DT(((("OMNIType",121),
                [("OMNIType",[110,111,112,113,114]),
                 ("bool",[26,180])]),["DISK_THM"]),
               [ThmBind.read"%148%80%246%186%47%173$1@%224$0@2|@2%182%95%173$1@%234$0@2|@2|@"])
  fun op output_Axiom x = x
    val op output_Axiom =
    ThmBind.DT(((("OMNIType",122),
                [("OMNIType",[110,111,112,113,114]),("bool",[26,180]),
                 ("ind_type",[33,34]),("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%136%65%127%68%196%74%159%123%30%162$1%224$0@3$3$0@2|@2%118%26%162$1%234$0@3$2$0@2|@2|@|@|@"])
  fun op output_induction x = x
    val op output_induction =
    ThmBind.DT(((("OMNIType",123),
                [("OMNIType",[110,111,112,113,114]),
                 ("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%140%22%180%159%123%47$1%224$0@2|@2%118%95$1%234$0@2|@3%148%79$1$0@|@2|@"])
  fun op output_distinct_clauses x = x
    val op output_distinct_clauses =
    ThmBind.DT(((("OMNIType",124),
                [("OMNIType",[110,111,112,113,114]),
                 ("bool",[25,26,46,53,62,180]),("ind_type",[33,34]),
                 ("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%118%33%123%30%271%173%224$0@2%234$1@3|@|@"])
  fun op output_one_one x = x
    val op output_one_one =
    ThmBind.DT(((("OMNIType",125),
                [("OMNIType",[110,111,112,113,114]),
                 ("bool",[26,55,62,180]),("ind_type",[33,34]),
                 ("pair",[8,9])]),["DISK_THM"]),
               [ThmBind.read"%159%123%30%123%37%167%173%224$1@2%224$0@3%170$1@$0@2|@|@2%118%26%118%33%167%173%234$1@2%234$0@3%164$1@$0@2|@|@2"])
  fun op datatype_principal x = x
    val op datatype_principal =
    ThmBind.DT(((("OMNIType",132),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%222%84%236@2"])
  fun op principal_11 x = x
    val op principal_11 =
    ThmBind.DT(((("OMNIType",133),
                [("OMNIType",[127,128,129]),("bool",[26,55,62,180]),
                 ("ind_type",[33,34])]),["DISK_THM"]),
               [ThmBind.read"%120%28%120%35%167%174%236$1@2%236$0@3%166$1@$0@2|@|@"])
  fun op principal_case_cong x = x
    val op principal_case_cong =
    ThmBind.DT(((("OMNIType",134),
                [("OMNIType",[127,128,129,130]),
                 ("bool",[26,180])]),["DISK_THM"]),
               [ThmBind.read"%149%9%149%16%131%55%180%159%174$2@$1@2%120%28%180%174$2@%236$0@3%162$1$0@2%60$0@3|@3%162%264$2@$0@2%264$1@%60@3|@|@|@"])
  fun op principal_nchotomy x = x
    val op principal_nchotomy =
    ThmBind.DT(((("OMNIType",135),
                [("OMNIType",[127,128,129]),
                 ("bool",[26,180])]),["DISK_THM"]),
               [ThmBind.read"%149%83%184%97%174$1@%236$0@2|@|@"])
  fun op principal_Axiom x = x
    val op principal_Axiom =
    ThmBind.DT(((("OMNIType",136),
                [("OMNIType",[127,128,129]),("bool",[26,180]),
                 ("ind_type",[33,34])]),["DISK_THM"]),
               [ThmBind.read"%131%55%198%75%120%28%162$1%236$0@3$2$0@2|@|@|@"])
  fun op principal_induction x = x
    val op principal_induction =
    ThmBind.DT(((("OMNIType",137),
                [("OMNIType",[127,128,129]),("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%141%23%180%120%97$1%236$0@2|@2%149%82$1$0@|@2|@"])
  fun op principal_one_one x = x
    val op principal_one_one =
    ThmBind.DT(((("OMNIType",138),
                [("OMNIType",[127,128,129]),("bool",[26,55,62,180]),
                 ("ind_type",[33,34])]),["DISK_THM"]),
               [ThmBind.read"%120%28%120%35%167%174%236$1@2%236$0@3%166$1@$0@2|@|@"])

  val _ = DB.bindl "OMNIType"
  [("escCommand_TY_DEF",escCommand_TY_DEF,DB.Def),
   ("escCommand_BIJ",escCommand_BIJ,DB.Def),
   ("escCommand_size_def",escCommand_size_def,DB.Def),
   ("escCommand_CASE",escCommand_CASE,DB.Def),
   ("command_TY_DEF",command_TY_DEF,DB.Def),
   ("command_case_def",command_case_def,DB.Def),
   ("command_size_def",command_size_def,DB.Def),
   ("escState_TY_DEF",escState_TY_DEF,DB.Def),
   ("escState_BIJ",escState_BIJ,DB.Def),
   ("escState_size_def",escState_size_def,DB.Def),
   ("escState_CASE",escState_CASE,DB.Def),
   ("state_TY_DEF",state_TY_DEF,DB.Def),
   ("state_case_def",state_case_def,DB.Def),
   ("state_size_def",state_size_def,DB.Def),
   ("escOutput_TY_DEF",escOutput_TY_DEF,DB.Def),
   ("escOutput_BIJ",escOutput_BIJ,DB.Def),
   ("escOutput_size_def",escOutput_size_def,DB.Def),
   ("escOutput_CASE",escOutput_CASE,DB.Def),
   ("output_TY_DEF",output_TY_DEF,DB.Def),
   ("output_case_def",output_case_def,DB.Def),
   ("output_size_def",output_size_def,DB.Def),
   ("principal_TY_DEF",principal_TY_DEF,DB.Def),
   ("principal_case_def",principal_case_def,DB.Def),
   ("principal_size_def",principal_size_def,DB.Def),
   ("num2escCommand_escCommand2num",num2escCommand_escCommand2num,DB.Thm),
   ("escCommand2num_num2escCommand",escCommand2num_num2escCommand,DB.Thm),
   ("num2escCommand_11",num2escCommand_11,DB.Thm),
   ("escCommand2num_11",escCommand2num_11,DB.Thm),
   ("num2escCommand_ONTO",num2escCommand_ONTO,DB.Thm),
   ("escCommand2num_ONTO",escCommand2num_ONTO,DB.Thm),
   ("num2escCommand_thm",num2escCommand_thm,DB.Thm),
   ("escCommand2num_thm",escCommand2num_thm,DB.Thm),
   ("escCommand_EQ_escCommand",escCommand_EQ_escCommand,DB.Thm),
   ("escCommand_case_def",escCommand_case_def,DB.Thm),
   ("datatype_escCommand",datatype_escCommand,DB.Thm),
   ("escCommand_distinct",escCommand_distinct,DB.Thm),
   ("escCommand_case_cong",escCommand_case_cong,DB.Thm),
   ("escCommand_nchotomy",escCommand_nchotomy,DB.Thm),
   ("escCommand_Axiom",escCommand_Axiom,DB.Thm),
   ("escCommand_induction",escCommand_induction,DB.Thm),
   ("datatype_command",datatype_command,DB.Thm),
   ("command_11",command_11,DB.Thm),
   ("command_distinct",command_distinct,DB.Thm),
   ("command_case_cong",command_case_cong,DB.Thm),
   ("command_nchotomy",command_nchotomy,DB.Thm),
   ("command_Axiom",command_Axiom,DB.Thm),
   ("command_induction",command_induction,DB.Thm),
   ("escCommand_distinct_clauses",escCommand_distinct_clauses,DB.Thm),
   ("command_distinct_clauses",command_distinct_clauses,DB.Thm),
   ("command_one_one",command_one_one,DB.Thm),
   ("num2escState_escState2num",num2escState_escState2num,DB.Thm),
   ("escState2num_num2escState",escState2num_num2escState,DB.Thm),
   ("num2escState_11",num2escState_11,DB.Thm),
   ("escState2num_11",escState2num_11,DB.Thm),
   ("num2escState_ONTO",num2escState_ONTO,DB.Thm),
   ("escState2num_ONTO",escState2num_ONTO,DB.Thm),
   ("num2escState_thm",num2escState_thm,DB.Thm),
   ("escState2num_thm",escState2num_thm,DB.Thm),
   ("escState_EQ_escState",escState_EQ_escState,DB.Thm),
   ("escState_case_def",escState_case_def,DB.Thm),
   ("datatype_escState",datatype_escState,DB.Thm),
   ("escState_distinct",escState_distinct,DB.Thm),
   ("escState_case_cong",escState_case_cong,DB.Thm),
   ("escState_nchotomy",escState_nchotomy,DB.Thm),
   ("escState_Axiom",escState_Axiom,DB.Thm),
   ("escState_induction",escState_induction,DB.Thm),
   ("escState_distinct_clauses",escState_distinct_clauses,DB.Thm),
   ("datatype_state",datatype_state,DB.Thm), ("state_11",state_11,DB.Thm),
   ("state_distinct",state_distinct,DB.Thm),
   ("state_case_cong",state_case_cong,DB.Thm),
   ("state_nchotomy",state_nchotomy,DB.Thm),
   ("state_Axiom",state_Axiom,DB.Thm),
   ("state_induction",state_induction,DB.Thm),
   ("state_distinct_clauses",state_distinct_clauses,DB.Thm),
   ("state_one_one",state_one_one,DB.Thm),
   ("num2escOutput_escOutput2num",num2escOutput_escOutput2num,DB.Thm),
   ("escOutput2num_num2escOutput",escOutput2num_num2escOutput,DB.Thm),
   ("num2escOutput_11",num2escOutput_11,DB.Thm),
   ("escOutput2num_11",escOutput2num_11,DB.Thm),
   ("num2escOutput_ONTO",num2escOutput_ONTO,DB.Thm),
   ("escOutput2num_ONTO",escOutput2num_ONTO,DB.Thm),
   ("num2escOutput_thm",num2escOutput_thm,DB.Thm),
   ("escOutput2num_thm",escOutput2num_thm,DB.Thm),
   ("escOutput_EQ_escOutput",escOutput_EQ_escOutput,DB.Thm),
   ("escOutput_case_def",escOutput_case_def,DB.Thm),
   ("datatype_escOutput",datatype_escOutput,DB.Thm),
   ("escOutput_distinct",escOutput_distinct,DB.Thm),
   ("escOutput_case_cong",escOutput_case_cong,DB.Thm),
   ("escOutput_nchotomy",escOutput_nchotomy,DB.Thm),
   ("escOutput_Axiom",escOutput_Axiom,DB.Thm),
   ("escOutput_induction",escOutput_induction,DB.Thm),
   ("escOutput_distinct_clauses",escOutput_distinct_clauses,DB.Thm),
   ("datatype_output",datatype_output,DB.Thm),
   ("output_11",output_11,DB.Thm),
   ("output_distinct",output_distinct,DB.Thm),
   ("output_case_cong",output_case_cong,DB.Thm),
   ("output_nchotomy",output_nchotomy,DB.Thm),
   ("output_Axiom",output_Axiom,DB.Thm),
   ("output_induction",output_induction,DB.Thm),
   ("output_distinct_clauses",output_distinct_clauses,DB.Thm),
   ("output_one_one",output_one_one,DB.Thm),
   ("datatype_principal",datatype_principal,DB.Thm),
   ("principal_11",principal_11,DB.Thm),
   ("principal_case_cong",principal_case_cong,DB.Thm),
   ("principal_nchotomy",principal_nchotomy,DB.Thm),
   ("principal_Axiom",principal_Axiom,DB.Thm),
   ("principal_induction",principal_induction,DB.Thm),
   ("principal_one_one",principal_one_one,DB.Thm)]

  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "OMNIType",
    thydataty = "TypeGrammarDeltas",
    read = ThmBind.read,
    data =
        "NTY8.OMNIType,10.escCommandNTY8.OMNIType,7.commandNTY8.OMNIType,8.escStateNTY8.OMNIType,5.stateNTY8.OMNIType,9.escOutputNTY8.OMNIType,6.outputNTY8.OMNIType,9.principal"
  }
  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "OMNIType",
    thydataty = "TermGrammarDeltas",
    read = ThmBind.read,
    data =
        "OO14.escCommand2num4.%250OO14.num2escCommand4.%259OO12.returnToBase4.%268OO13.changeMission4.%247OO8.resupply4.%267OO14.reactToContact4.%266OO15.escCommand_size4.%252OO15.escCommand_CASE4.%251OO4.case4.%251OO4.ESCc4.%223OO3.SLc4.%233OO12.command_CASE4.%248OO12.command_size4.%249OO4.case4.%248OO12.escState2num4.%256OO12.num2escState4.%261OO3.RTB4.%228OO2.CM4.%215OO8.RESUPPLY4.%227OO3.RTC4.%229OO13.escState_size4.%258OO13.escState_CASE4.%257OO4.case4.%257OO4.ESCs4.%225OO3.SLs4.%235OO10.state_CASE4.%269OO10.state_size4.%270OO4.case4.%269OO13.escOutput2num4.%253OO13.num2escOutput4.%260OO12.ReturnToBase4.%232OO13.ChangeMission4.%221OO8.Resupply4.%231OO14.ReactToContact4.%230OO14.escOutput_size4.%255OO14.escOutput_CASE4.%254OO4.case4.%254OO4.ESCo4.%224OO3.SLo4.%234OO11.output_CASE4.%262OO11.output_size4.%263OO4.case4.%262OO2.SR4.%236OO14.principal_CASE4.%264OO14.principal_size4.%265OO4.case4.%264"
  }
  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val OMNIType_grammars = merge_grammars ["indexedLists", "patternMatches"]
  local
  val (tyUDs, tmUDs) = GrammarDeltas.thy_deltas{thyname="OMNIType"}
  val addtmUDs = term_grammar.add_deltas tmUDs
  val addtyUDs = type_grammar.apply_deltas tyUDs
  in
  val OMNIType_grammars = 
    Portable.## (addtyUDs,addtmUDs) OMNIType_grammars
  val _ = Parse.grammarDB_insert("OMNIType",OMNIType_grammars)
  val _ = Parse.temp_set_grammars (addtyUDs (Parse.type_grammar()), addtmUDs (Parse.term_grammar()))
  end (* addUDs local *)
  end


  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG escCommand_Axiom,
           case_def=escCommand_case_def,
           case_cong=escCommand_case_cong,
           induction=ORIG escCommand_induction,
           nchotomy=escCommand_nchotomy,
           size=SOME(Parse.Term`(OMNIType$escCommand_size) :OMNIType$escCommand -> num$num`,
                     ORIG escCommand_size_def),
           encode = NONE,
           lift=NONE,
           one_one=NONE,
           distinct=SOME escCommand_distinct,
           fields=let fun T t s A = mk_thy_type{Thy=t,Tyop=s,Args=A}
    val U = mk_vartype
in
[] end,
           accessors=[],
           updates=[],
           recognizers=[],
           destructors=[]}
        val tyinfo0 = EnumType.update_tyinfo num2escCommand_thm escCommand2num_thm NONE tyinfo0
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
          {ax=ORIG command_Axiom,
           case_def=command_case_def,
           case_cong=command_case_cong,
           induction=ORIG command_induction,
           nchotomy=command_nchotomy,
           size=SOME(Parse.Term`(OMNIType$command_size) :('slCommand -> num$num) -> 'slCommand OMNIType$command -> num$num`,
                     ORIG command_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME command_11,
           distinct=SOME command_distinct,
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
          {ax=ORIG escState_Axiom,
           case_def=escState_case_def,
           case_cong=escState_case_cong,
           induction=ORIG escState_induction,
           nchotomy=escState_nchotomy,
           size=SOME(Parse.Term`(OMNIType$escState_size) :OMNIType$escState -> num$num`,
                     ORIG escState_size_def),
           encode = NONE,
           lift=NONE,
           one_one=NONE,
           distinct=SOME escState_distinct,
           fields=let fun T t s A = mk_thy_type{Thy=t,Tyop=s,Args=A}
    val U = mk_vartype
in
[] end,
           accessors=[],
           updates=[],
           recognizers=[],
           destructors=[]}
        val tyinfo0 = EnumType.update_tyinfo num2escState_thm escState2num_thm NONE tyinfo0
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
          {ax=ORIG state_Axiom,
           case_def=state_case_def,
           case_cong=state_case_cong,
           induction=ORIG state_induction,
           nchotomy=state_nchotomy,
           size=SOME(Parse.Term`(OMNIType$state_size) :('slState -> num$num) -> 'slState OMNIType$state -> num$num`,
                     ORIG state_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME state_11,
           distinct=SOME state_distinct,
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
          {ax=ORIG escOutput_Axiom,
           case_def=escOutput_case_def,
           case_cong=escOutput_case_cong,
           induction=ORIG escOutput_induction,
           nchotomy=escOutput_nchotomy,
           size=SOME(Parse.Term`(OMNIType$escOutput_size) :OMNIType$escOutput -> num$num`,
                     ORIG escOutput_size_def),
           encode = NONE,
           lift=NONE,
           one_one=NONE,
           distinct=SOME escOutput_distinct,
           fields=let fun T t s A = mk_thy_type{Thy=t,Tyop=s,Args=A}
    val U = mk_vartype
in
[] end,
           accessors=[],
           updates=[],
           recognizers=[],
           destructors=[]}
        val tyinfo0 = EnumType.update_tyinfo num2escOutput_thm escOutput2num_thm NONE tyinfo0
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
          {ax=ORIG output_Axiom,
           case_def=output_case_def,
           case_cong=output_case_cong,
           induction=ORIG output_induction,
           nchotomy=output_nchotomy,
           size=SOME(Parse.Term`(OMNIType$output_size) :('slOutput -> num$num) -> 'slOutput OMNIType$output -> num$num`,
                     ORIG output_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME output_11,
           distinct=SOME output_distinct,
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
          {ax=ORIG principal_Axiom,
           case_def=principal_case_def,
           case_cong=principal_case_cong,
           induction=ORIG principal_induction,
           nchotomy=principal_nchotomy,
           size=SOME(Parse.Term`(OMNIType$principal_size) :('stateRole -> num$num) -> 'stateRole OMNIType$principal -> num$num`,
                     ORIG principal_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME principal_11,
           distinct=NONE,
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

val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "OMNIType"
end
