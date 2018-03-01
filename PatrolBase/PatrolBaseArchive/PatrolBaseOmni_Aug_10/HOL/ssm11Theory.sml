structure ssm11Theory :> ssm11Theory =
struct
  val _ = if !Globals.print_thy_loads then TextIO.print "Loading ssm11Theory ... " else ()
  open Type Term Thm
  infixr -->

  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  (* Parents and ML dependencies *)
  local open satListTheory
  in end;
  val _ = Theory.link_parents
          ("ssm11",
          Arbnum.fromString "1503359460",
          Arbnum.fromString "177264")
          [("satList",
           Arbnum.fromString "1503359458",
           Arbnum.fromString "860497")];
  val _ = Theory.incorporate_types "ssm11"
       [("trType", 1), ("order", 1), ("configuration", 6)];

  val idvector = 
    let fun ID(thy,oth) = {Thy = thy, Other = oth}
    in Vector.fromList
  [ID("min", "fun"), ID("ssm11", "trType"), ID("num", "num"),
   ID("ssm11", "order"), ID("ssm11", "configuration"), ID("list", "list"),
   ID("aclfoundation", "Form"), ID("min", "bool"), ID("pair", "prod"),
   ID("aclfoundation", "po"), ID("aclfoundation", "Kripke"),
   ID("ind_type", "recspace"), ID("aclfoundation", "Princ"),
   ID("bool", "!"), ID("arithmetic", "+"), ID("pair", ","),
   ID("bool", "/\\"), ID("num", "0"), ID("min", "="), ID("min", "==>"),
   ID("bool", "?"), ID("bool", "ARB"), ID("arithmetic", "BIT1"),
   ID("ind_type", "BOTTOM"), ID("ssm11", "CFG"),
   ID("ssm11", "CFGInterpret"), ID("list", "CONS"),
   ID("ind_type", "CONSTR"), ID("bool", "DATATYPE"),
   ID("aclfoundation", "Form_size"), ID("list", "NIL"),
   ID("ssm11", "NONE"), ID("arithmetic", "NUMERAL"), ID("ssm11", "SOME"),
   ID("num", "SUC"), ID("ssm11", "TR"), ID("bool", "TYPE_DEFINITION"),
   ID("arithmetic", "ZERO"), ID("bool", "\\/"),
   ID("ssm11", "configuration_CASE"), ID("ssm11", "configuration_size"),
   ID("ssm11", "discard"), ID("ssm11", "exec"), ID("list", "list_size"),
   ID("ssm11", "order_CASE"), ID("ssm11", "order_size"),
   ID("aclfoundation", "prop"), ID("aclrules", "sat"),
   ID("satList", "satList"), ID("aclfoundation", "says"),
   ID("ssm11", "trType_CASE"), ID("ssm11", "trType_size"),
   ID("ssm11", "trap"), ID("bool", "~")]
  end;
  local open SharingTables
  in
  val tyvector = build_type_vector idvector
  [TYV "'command", TYOP [1, 0], TYOP [0, 0, 1], TYOP [2], TYOP [0, 1, 3],
   TYOP [0, 0, 3], TYOP [0, 5, 4], TYV "'a", TYOP [0, 0, 7],
   TYOP [0, 8, 7], TYOP [0, 8, 9], TYOP [0, 8, 10], TYOP [0, 1, 11],
   TYOP [3, 0], TYOP [0, 13, 3], TYOP [0, 5, 14], TYOP [0, 7, 7],
   TYOP [0, 8, 16], TYOP [0, 13, 17], TYV "'state", TYV "'principal",
   TYV "'output", TYV "'e", TYV "'d", TYOP [4, 0, 23, 22, 21, 20, 19],
   TYOP [0, 24, 3], TYOP [0, 19, 3], TYOP [0, 26, 25], TYOP [0, 20, 3],
   TYOP [0, 28, 27], TYOP [0, 21, 3], TYOP [0, 30, 29], TYOP [0, 22, 3],
   TYOP [0, 32, 31], TYOP [0, 23, 3], TYOP [0, 34, 33], TYOP [0, 5, 35],
   TYOP [5, 21], TYOP [0, 37, 7], TYOP [0, 19, 38],
   TYOP [6, 13, 20, 23, 22], TYOP [5, 40], TYOP [0, 41, 39],
   TYOP [0, 41, 42], TYOP [0, 19, 40], TYOP [0, 44, 43], TYOP [7],
   TYOP [0, 40, 46], TYOP [0, 47, 45], TYOP [0, 48, 7], TYOP [0, 24, 49],
   TYOP [0, 24, 46], TYOP [0, 24, 51], TYOP [0, 1, 52], TYOP [9, 22],
   TYOP [9, 23], TYOP [8, 55, 54], TYV "'b", TYOP [10, 13, 57, 20, 23, 22],
   TYOP [8, 58, 56], TYOP [0, 59, 53], TYOP [0, 0, 13], TYOP [0, 59, 51],
   TYOP [0, 37, 24], TYOP [0, 19, 63], TYOP [0, 41, 64], TYOP [0, 41, 65],
   TYOP [0, 44, 66], TYOP [0, 47, 67], TYOP [8, 19, 37], TYOP [8, 41, 69],
   TYOP [8, 41, 70], TYOP [8, 44, 71], TYOP [8, 47, 72], TYOP [11, 73],
   TYOP [0, 74, 46], TYOP [11, 0], TYOP [0, 76, 46], TYOP [0, 1, 19],
   TYOP [0, 19, 78], TYOP [0, 1, 21], TYOP [0, 19, 80], TYOP [12, 20],
   TYOP [0, 13, 46], TYOP [0, 1, 46], TYOP [0, 68, 46], TYOP [0, 24, 7],
   TYOP [0, 13, 7], TYOP [0, 1, 7], TYOP [0, 61, 83], TYOP [0, 24, 74],
   TYOP [0, 13, 76], TYOP [0, 1, 76], TYOP [0, 2, 46], TYOP [0, 2, 93],
   TYOP [0, 2, 94], TYOP [0, 7, 46], TYOP [0, 96, 46], TYOP [0, 0, 46],
   TYOP [0, 98, 46], TYOP [0, 19, 46], TYOP [0, 100, 46], TYOP [0, 47, 46],
   TYOP [0, 58, 46], TYOP [0, 103, 46], TYOP [0, 82, 46],
   TYOP [0, 105, 46], TYOP [0, 51, 46], TYOP [0, 8, 46], TYOP [0, 108, 46],
   TYOP [0, 5, 46], TYOP [0, 110, 46], TYOP [0, 34, 46], TYOP [0, 112, 46],
   TYOP [0, 32, 46], TYOP [0, 114, 46], TYOP [0, 30, 46],
   TYOP [0, 116, 46], TYOP [0, 28, 46], TYOP [0, 118, 46],
   TYOP [0, 44, 46], TYOP [0, 120, 46], TYOP [0, 81, 46],
   TYOP [0, 122, 46], TYOP [0, 79, 46], TYOP [0, 124, 46],
   TYOP [0, 26, 46], TYOP [0, 126, 46], TYOP [0, 102, 46],
   TYOP [0, 107, 46], TYOP [0, 48, 46], TYOP [0, 130, 46],
   TYOP [0, 83, 46], TYOP [0, 132, 46], TYOP [0, 62, 46],
   TYOP [0, 134, 46], TYOP [0, 60, 46], TYOP [0, 136, 46],
   TYOP [0, 77, 46], TYOP [0, 138, 46], TYOP [0, 75, 46],
   TYOP [0, 140, 46], TYOP [0, 84, 46], TYOP [0, 142, 46],
   TYOP [0, 37, 46], TYOP [0, 144, 46], TYOP [0, 41, 46],
   TYOP [0, 146, 46], TYOP [0, 55, 46], TYOP [0, 148, 46],
   TYOP [0, 54, 46], TYOP [0, 150, 46], TYOP [0, 59, 46],
   TYOP [0, 152, 46], TYOP [0, 3, 3], TYOP [0, 3, 154], TYOP [0, 37, 69],
   TYOP [0, 19, 156], TYOP [0, 56, 59], TYOP [0, 58, 158],
   TYOP [0, 71, 72], TYOP [0, 44, 160], TYOP [0, 72, 73],
   TYOP [0, 47, 162], TYOP [0, 69, 70], TYOP [0, 41, 164],
   TYOP [0, 70, 71], TYOP [0, 41, 166], TYOP [0, 54, 56],
   TYOP [0, 55, 168], TYOP [0, 46, 46], TYOP [0, 46, 170], TYOP [0, 7, 96],
   TYOP [0, 0, 98], TYOP [0, 19, 100], TYOP [0, 44, 120],
   TYOP [0, 47, 102], TYOP [0, 60, 136], TYOP [0, 37, 144],
   TYOP [0, 41, 146], TYOP [0, 3, 46], TYOP [0, 3, 180], TYOP [0, 13, 83],
   TYOP [0, 59, 152], TYOP [0, 76, 77], TYOP [0, 74, 75], TYOP [0, 1, 84],
   TYOP [0, 86, 46], TYOP [0, 187, 46], TYOP [0, 90, 46],
   TYOP [0, 189, 46], TYOP [0, 87, 46], TYOP [0, 191, 46],
   TYOP [0, 91, 46], TYOP [0, 193, 46], TYOP [0, 88, 46],
   TYOP [0, 195, 46], TYOP [0, 92, 46], TYOP [0, 197, 46],
   TYOP [0, 37, 37], TYOP [0, 21, 199], TYOP [0, 41, 41],
   TYOP [0, 40, 201], TYOP [0, 3, 76], TYOP [0, 203, 76], TYOP [0, 0, 204],
   TYOP [0, 3, 205], TYOP [0, 3, 74], TYOP [0, 207, 74], TYOP [0, 73, 208],
   TYOP [0, 3, 209], TYOP [0, 40, 3], TYOP [0, 32, 211], TYOP [0, 34, 212],
   TYOP [0, 28, 213], TYOP [0, 14, 214], TYOP [0, 77, 193],
   TYOP [0, 77, 197], TYOP [0, 75, 189], TYOP [0, 37, 3],
   TYOP [0, 30, 219], TYOP [0, 41, 3], TYOP [0, 211, 221],
   TYOP [0, 13, 40], TYOP [0, 59, 47], TYOP [0, 59, 146], TYOP [0, 40, 40],
   TYOP [0, 82, 226]]
  end
  val _ = Theory.incorporate_consts "ssm11" tyvector
     [("trap", 2), ("trType_size", 6), ("trType_CASE", 12),
      ("order_size", 15), ("order_CASE", 18), ("exec", 2), ("discard", 2),
      ("configuration_size", 36), ("configuration_CASE", 50), ("TR", 60),
      ("SOME", 61), ("NONE", 13), ("CFGInterpret", 62), ("CFG", 68)];

  local open SharingTables
  in
  val tmvector = build_term_vector idvector tyvector
  [TMV("'configuration'", 75), TMV("'order'", 77), TMV("'trType'", 77),
   TMV("M", 58), TMV("M", 24), TMV("M", 13), TMV("M", 1), TMV("M'", 24),
   TMV("M'", 13), TMV("M'", 1), TMV("NS", 79), TMV("Oi", 55),
   TMV("Os", 54), TMV("Out", 81), TMV("P", 82), TMV("P", 51), TMV("P", 83),
   TMV("P", 62), TMV("P", 84), TMV("TR'", 60), TMV("a", 0), TMV("a'", 0),
   TMV("a0", 47), TMV("a0", 59), TMV("a0", 76), TMV("a0'", 47),
   TMV("a0'", 74), TMV("a1", 44), TMV("a1", 1), TMV("a1'", 44),
   TMV("a2", 24), TMV("a2", 41), TMV("a2'", 41), TMV("a3", 24),
   TMV("a3", 41), TMV("a3'", 41), TMV("a4", 19), TMV("a4'", 19),
   TMV("a5", 37), TMV("a5'", 37), TMV("authenticationTest", 47),
   TMV("c", 0), TMV("c", 24), TMV("cc", 24), TMV("cmd", 0),
   TMV("configuration", 85), TMV("f", 8), TMV("f", 5), TMV("f", 47),
   TMV("f", 48), TMV("f'", 8), TMV("f'", 48), TMV("f0", 8), TMV("f0", 44),
   TMV("f1", 7), TMV("f1", 8), TMV("f1", 34), TMV("f1'", 8), TMV("f2", 8),
   TMV("f2", 32), TMV("f2'", 8), TMV("f3", 30), TMV("f4", 28),
   TMV("f5", 26), TMV("fn", 86), TMV("fn", 87), TMV("fn", 88),
   TMV("input", 40), TMV("ins", 41), TMV("l", 41), TMV("l0", 41),
   TMV("l1", 37), TMV("n", 3), TMV("o", 13), TMV("oo", 13),
   TMV("order", 89), TMV("outputStream", 37), TMV("outs", 37),
   TMV("rep", 90), TMV("rep", 91), TMV("rep", 92), TMV("s", 19),
   TMV("securityContext", 41), TMV("state", 19), TMV("stateInterp", 44),
   TMV("t", 1), TMV("trType", 95), TMV("tt", 1), TMV("v", 7), TMV("v", 58),
   TMV("v'", 7), TMV("v1", 55), TMV("v10", 47), TMV("v11", 44),
   TMV("v12", 41), TMV("v13", 19), TMV("v14", 37), TMV("v15", 59),
   TMV("v2", 54), TMV("v3", 24), TMV("x", 40), TMC(13, 97), TMC(13, 99),
   TMC(13, 101), TMC(13, 102), TMC(13, 104), TMC(13, 106), TMC(13, 107),
   TMC(13, 109), TMC(13, 111), TMC(13, 113), TMC(13, 115), TMC(13, 117),
   TMC(13, 119), TMC(13, 121), TMC(13, 123), TMC(13, 125), TMC(13, 127),
   TMC(13, 128), TMC(13, 129), TMC(13, 131), TMC(13, 133), TMC(13, 135),
   TMC(13, 137), TMC(13, 139), TMC(13, 141), TMC(13, 143), TMC(13, 145),
   TMC(13, 147), TMC(13, 132), TMC(13, 149), TMC(13, 151), TMC(13, 153),
   TMC(13, 138), TMC(13, 140), TMC(13, 142), TMC(14, 155), TMC(15, 157),
   TMC(15, 159), TMC(15, 161), TMC(15, 163), TMC(15, 165), TMC(15, 167),
   TMC(15, 169), TMC(16, 171), TMC(17, 3), TMC(18, 172), TMC(18, 173),
   TMC(18, 174), TMC(18, 171), TMC(18, 52), TMC(18, 175), TMC(18, 176),
   TMC(18, 177), TMC(18, 178), TMC(18, 179), TMC(18, 181), TMC(18, 182),
   TMC(18, 183), TMC(18, 184), TMC(18, 185), TMC(18, 186), TMC(19, 171),
   TMC(20, 99), TMC(20, 101), TMC(20, 102), TMC(20, 104), TMC(20, 106),
   TMC(20, 121), TMC(20, 123), TMC(20, 125), TMC(20, 128), TMC(20, 188),
   TMC(20, 190), TMC(20, 192), TMC(20, 194), TMC(20, 196), TMC(20, 198),
   TMC(20, 145), TMC(20, 147), TMC(20, 149), TMC(20, 151), TMC(21, 0),
   TMC(22, 154), TMC(23, 76), TMC(23, 74), TMC(24, 68), TMC(25, 62),
   TMC(26, 200), TMC(26, 202), TMC(27, 206), TMC(27, 210), TMC(28, 170),
   TMC(29, 215), TMC(30, 41), TMC(31, 13), TMC(32, 154), TMC(33, 61),
   TMC(34, 154), TMC(35, 60), TMC(36, 216), TMC(36, 217), TMC(36, 218),
   TMC(37, 3), TMC(38, 171), TMC(39, 50), TMC(40, 36), TMC(41, 2),
   TMC(42, 2), TMC(43, 220), TMC(43, 222), TMC(44, 18), TMC(45, 15),
   TMC(46, 223), TMC(47, 224), TMC(48, 225), TMC(49, 227), TMC(50, 12),
   TMC(51, 6), TMC(52, 2), TMC(53, 170)]
  end
  structure ThmBind = struct
    val DT = Thm.disk_thm
    val read = Term.read_raw tmvector
  end
  fun op order_TY_DEF x = x
    val op order_TY_DEF =
    ThmBind.DT(((("ssm11",0),[("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%175%79%200%24%124%1%162%133%24%162%204%163%20%159$1@%20%190%145@$0@%72%184|@|$0@2|@2%159$0@%190%198%145@2%182@%72%184|@4$1$0@2|@2$0$1@2|@|@$0@|@"])
  fun op order_case_def x = x
    val op order_case_def =
    ThmBind.DT(((("ssm11",6),
                [("bool",[26,180]),("ind_type",[33,34]),
                 ("ssm11",[1,2,3,4,5])]),["DISK_THM"]),
               [ThmBind.read"%144%102%20%108%46%101%88%146%211%197$2@2$1@$0@2$1$2@2|@|@|@2%108%46%101%88%146%211%195@$1@$0@2$0@|@|@2"])
  fun op order_size_def x = x
    val op order_size_def =
    ThmBind.DT(((("ssm11",7),
                [("bool",[26,180]),("ind_type",[33,34]),
                 ("ssm11",[1,2,3,4,5])]),["DISK_THM"]),
               [ThmBind.read"%144%109%47%102%20%156%212$1@%197$0@3%136%196%183%203@3$1$0@3|@|@2%109%47%156%212$0@%195@2%145@|@2"])
  fun op trType_TY_DEF x = x
    val op trType_TY_DEF =
    ThmBind.DT(((("ssm11",17),[("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%177%80%201%24%124%2%162%133%24%162%204%163%20%159$1@%20%190%145@$0@%72%184|@|$0@2|@2%204%163%20%159$1@%20%190%198%145@2$0@%72%184|@|$0@2|@2%163%20%159$1@%20%190%198%198%145@3$0@%72%184|@|$0@2|@4$1$0@2|@2$0$1@2|@|@$0@|@"])
  fun op trType_case_def x = x
    val op trType_case_def =
    ThmBind.DT(((("ssm11",25),
                [("bool",[26,180]),("ind_type",[33,34]),
                 ("ssm11",[18,19,20,21,22,23,24])]),["DISK_THM"]),
               [ThmBind.read"%144%102%20%108%46%108%55%108%58%146%217%207$3@2$2@$1@$0@2$2$3@2|@|@|@|@2%144%102%20%108%46%108%55%108%58%146%217%219$3@2$2@$1@$0@2$1$3@2|@|@|@|@2%102%20%108%46%108%55%108%58%146%217%208$3@2$2@$1@$0@2$0$3@2|@|@|@|@3"])
  fun op trType_size_def x = x
    val op trType_size_def =
    ThmBind.DT(((("ssm11",26),
                [("bool",[26,180]),("ind_type",[33,34]),
                 ("ssm11",[18,19,20,21,22,23,24])]),["DISK_THM"]),
               [ThmBind.read"%144%109%47%102%20%156%218$1@%207$0@3%136%196%183%203@3$1$0@3|@|@2%144%109%47%102%20%156%218$1@%219$0@3%136%196%183%203@3$1$0@3|@|@2%109%47%102%20%156%218$1@%208$0@3%136%196%183%203@3$1$0@3|@|@3"])
  fun op configuration_TY_DEF x = x
    val op configuration_TY_DEF =
    ThmBind.DT(((("ssm11",36),[("bool",[26])]),["DISK_THM"]),
               [ThmBind.read"%173%78%202%26%125%0%162%134%26%162%171%22%168%27%179%31%179%34%164%36%178%38%160$6@%22%27%31%34%36%38%191%145@%140$5@%139$4@%142$3@%141$2@%137$1@$0@6%72%185|@||||||$5@$4@$3@$2@$1@$0@2|@|@|@|@|@|@2$1$0@2|@2$0$1@2|@|@$0@|@"])
  fun op configuration_case_def x = x
    val op configuration_case_def =
    ThmBind.DT(((("ssm11",40),
                [("bool",[26,180]),("ind_type",[33,34]),("pair",[8,9]),
                 ("ssm11",[37,38,39])]),["DISK_THM"]),
               [ThmBind.read"%118%22%114%27%128%31%128%34%103%36%127%38%120%49%146%205%186$6@$5@$4@$3@$2@$1@2$0@2$0$6@$5@$4@$3@$2@$1@2|@|@|@|@|@|@|@"])
  fun op configuration_size_def x = x
    val op configuration_size_def =
    ThmBind.DT(((("ssm11",41),
                [("bool",[26,180]),("ind_type",[33,34]),("pair",[8,9]),
                 ("ssm11",[37,38,39])]),["DISK_THM"]),
               [ThmBind.read"%109%47%110%56%111%59%112%61%113%62%117%63%118%22%114%27%128%31%128%34%103%36%127%38%156%206$11@$10@$9@$8@$7@$6@%186$5@$4@$3@$2@$1@$0@3%136%196%183%203@3%136%210%193%212$11@2$7@$10@$9@2$3@2%136%210%193%212$11@2$7@$10@$9@2$2@2%136$6$1@2%209$8@$0@6|@|@|@|@|@|@|@|@|@|@|@|@"])
  fun op TR_def x = x
    val op TR_def =
    ThmBind.DT(((("ssm11",53),[]),[]),
               [ThmBind.read"%153%199@%23%28%30%33%123%19%162%132%23%135%28%107%30%107%33%162%204%171%40%167%14%170%10%166%3%180%11%181%12%169%13%164%81%179%82%168%84%163%44%179%68%178%77%144%158$16@%138$9@%143$8@$7@4%144%161$15@%208$2@3%144%150$14@%186$12@$3@$4@%189%216$11@%213%197$2@4$1@2$5@$0@3%144%150$13@%186$12@$3@$4@$1@$10$5@%208$2@3%188$6$5@%208$2@3$0@4%144$12%216$11@%213%197$2@5%187%138$9@%143$8@$7@3%186$12@$3@$4@%189%216$11@%213%197$2@4$1@2$5@$0@7|@|@|@|@|@|@|@|@|@|@|@|@|@2%204%171%40%167%14%170%10%166%3%180%11%181%12%169%13%164%81%179%82%168%84%163%44%179%68%178%77%144%158$16@%138$9@%143$8@$7@4%144%161$15@%219$2@3%144%150$14@%186$12@$3@$4@%189%216$11@%213%197$2@4$1@2$5@$0@3%144%150$13@%186$12@$3@$4@$1@$10$5@%219$2@3%188$6$5@%219$2@3$0@4%144$12%216$11@%213%197$2@5%187%138$9@%143$8@$7@3%186$12@$3@$4@%189%216$11@%213%197$2@4$1@2$5@$0@7|@|@|@|@|@|@|@|@|@|@|@|@|@2%171%40%170%10%166%3%180%11%181%12%169%13%164%81%179%82%168%84%163%44%165%100%179%68%178%77%144%158$16@%138$10@%143$9@$8@4%144%161$15@%207$3@3%144%150$14@%186$12@$4@$5@%189$2@$1@2$6@$0@3%144%150$13@%186$12@$4@$5@$1@$11$6@%207$3@3%188$7$6@%207$3@3$0@4%220$12$2@6|@|@|@|@|@|@|@|@|@|@|@|@|@4$4$3@$2@$1@$0@2|@|@|@|@2$0$4@$3@$2@$1@2|@||||@"])
  fun op datatype_order x = x
    val op datatype_order =
    ThmBind.DT(((("ssm11",8),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%192%75%197@%195@2"])
  fun op order_11 x = x
    val op order_11 =
    ThmBind.DT(((("ssm11",9),
                [("bool",[26,55,62,180]),("ind_type",[33,34]),
                 ("ssm11",[1,2,3,4,5])]),["DISK_THM"]),
               [ThmBind.read"%102%20%102%21%149%157%197$1@2%197$0@3%147$1@$0@2|@|@"])
  fun op order_distinct x = x
    val op order_distinct =
    ThmBind.DT(((("ssm11",10),
                [("bool",[25,26,46,53,62,180]),("ind_type",[33,34]),
                 ("ssm11",[1,2,3,4,5])]),["DISK_THM"]),
               [ThmBind.read"%102%20%220%157%197$0@2%195@2|@"])
  fun op order_case_cong x = x
    val op order_case_cong =
    ThmBind.DT(((("ssm11",11),
                [("bool",[26,180]),("ssm11",[1,2,3,4,5,6])]),["DISK_THM"]),
               [ThmBind.read"%129%5%129%8%108%46%101%88%162%144%157$3@$2@2%144%102%20%162%157$3@%197$0@3%146$2$0@2%50$0@3|@2%162%157$2@%195@2%146$0@%90@5%146%211$3@$1@$0@2%211$2@%50@%90@3|@|@|@|@"])
  fun op order_nchotomy x = x
    val op order_nchotomy =
    ThmBind.DT(((("ssm11",12),
                [("bool",[26,180]),("ssm11",[1,2,3,4,5])]),["DISK_THM"]),
               [ThmBind.read"%129%74%204%163%41%157$1@%197$0@2|@2%157$0@%195@2|@"])
  fun op order_Axiom x = x
    val op order_Axiom =
    ThmBind.DT(((("ssm11",13),
                [("bool",[26,180]),("ind_type",[33,34]),
                 ("ssm11",[1,2,3,4,5])]),["DISK_THM"]),
               [ThmBind.read"%108%52%101%54%174%65%144%102%20%146$1%197$0@3$3$0@2|@2%146$0%195@2$1@2|@|@|@"])
  fun op order_induction x = x
    val op order_induction =
    ThmBind.DT(((("ssm11",14),
                [("bool",[26]),("ssm11",[1,2,3,4,5])]),["DISK_THM"]),
               [ThmBind.read"%121%16%162%144%102%41$1%197$0@2|@2$0%195@3%129%73$1$0@|@2|@"])
  fun op order_distinct_clauses x = x
    val op order_distinct_clauses =
    ThmBind.DT(((("ssm11",15),
                [("bool",[25,26,46,53,62,180]),("ind_type",[33,34]),
                 ("ssm11",[1,2,3,4,5])]),["DISK_THM"]),
               [ThmBind.read"%102%20%220%157%197$0@2%195@2|@"])
  fun op order_one_one x = x
    val op order_one_one =
    ThmBind.DT(((("ssm11",16),
                [("bool",[26,55,62,180]),("ind_type",[33,34]),
                 ("ssm11",[1,2,3,4,5])]),["DISK_THM"]),
               [ThmBind.read"%102%20%102%21%149%157%197$1@2%197$0@3%147$1@$0@2|@|@"])
  fun op datatype_trType x = x
    val op datatype_trType =
    ThmBind.DT(((("ssm11",27),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%192%86%207@%219@%208@2"])
  fun op trType_11 x = x
    val op trType_11 =
    ThmBind.DT(((("ssm11",28),
                [("bool",[26,55,62,180]),("ind_type",[33,34]),
                 ("ssm11",[18,19,20,21,22,23,24])]),["DISK_THM"]),
               [ThmBind.read"%144%102%20%102%21%149%161%207$1@2%207$0@3%147$1@$0@2|@|@2%144%102%20%102%21%149%161%219$1@2%219$0@3%147$1@$0@2|@|@2%102%20%102%21%149%161%208$1@2%208$0@3%147$1@$0@2|@|@3"])
  fun op trType_distinct x = x
    val op trType_distinct =
    ThmBind.DT(((("ssm11",29),
                [("bool",[25,26,35,46,50,53,55,62,180]),
                 ("ind_type",[33,34]),
                 ("ssm11",[18,19,20,21,22,23,24])]),["DISK_THM"]),
               [ThmBind.read"%144%102%21%102%20%220%161%207$0@2%219$1@3|@|@2%144%102%21%102%20%220%161%207$0@2%208$1@3|@|@2%102%21%102%20%220%161%219$0@2%208$1@3|@|@3"])
  fun op trType_case_cong x = x
    val op trType_case_cong =
    ThmBind.DT(((("ssm11",30),
                [("bool",[26,180]),
                 ("ssm11",[18,19,20,21,22,23,24,25])]),["DISK_THM"]),
               [ThmBind.read"%135%6%135%9%108%46%108%55%108%58%162%144%161$4@$3@2%144%102%20%162%161$4@%207$0@3%146$3$0@2%50$0@3|@2%144%102%20%162%161$4@%219$0@3%146$2$0@2%57$0@3|@2%102%20%162%161$4@%208$0@3%146$1$0@2%60$0@3|@5%146%217$4@$2@$1@$0@2%217$3@%50@%57@%60@3|@|@|@|@|@"])
  fun op trType_nchotomy x = x
    val op trType_nchotomy =
    ThmBind.DT(((("ssm11",31),
                [("bool",[26,180]),
                 ("ssm11",[18,19,20,21,22,23,24])]),["DISK_THM"]),
               [ThmBind.read"%135%87%204%163%41%161$1@%207$0@2|@2%204%163%41%161$1@%219$0@2|@2%163%41%161$1@%208$0@2|@3|@"])
  fun op trType_Axiom x = x
    val op trType_Axiom =
    ThmBind.DT(((("ssm11",32),
                [("bool",[26,180]),("ind_type",[33,34]),
                 ("ssm11",[18,19,20,21,22,23,24])]),["DISK_THM"]),
               [ThmBind.read"%108%52%108%55%108%58%176%66%144%102%20%146$1%207$0@3$4$0@2|@2%144%102%20%146$1%219$0@3$3$0@2|@2%102%20%146$1%208$0@3$2$0@2|@3|@|@|@|@"])
  fun op trType_induction x = x
    val op trType_induction =
    ThmBind.DT(((("ssm11",33),
                [("bool",[26]),
                 ("ssm11",[18,19,20,21,22,23,24])]),["DISK_THM"]),
               [ThmBind.read"%126%18%162%144%102%41$1%207$0@2|@2%144%102%41$1%219$0@2|@2%102%41$1%208$0@2|@4%135%85$1$0@|@2|@"])
  fun op trType_distinct_clauses x = x
    val op trType_distinct_clauses =
    ThmBind.DT(((("ssm11",34),
                [("bool",[25,26,35,46,50,53,55,62,180]),
                 ("ind_type",[33,34]),
                 ("ssm11",[18,19,20,21,22,23,24])]),["DISK_THM"]),
               [ThmBind.read"%144%102%21%102%20%220%161%207$0@2%219$1@3|@|@2%144%102%21%102%20%220%161%207$0@2%208$1@3|@|@2%102%21%102%20%220%161%219$0@2%208$1@3|@|@3"])
  fun op trType_one_one x = x
    val op trType_one_one =
    ThmBind.DT(((("ssm11",35),
                [("bool",[26,55,62,180]),("ind_type",[33,34]),
                 ("ssm11",[18,19,20,21,22,23,24])]),["DISK_THM"]),
               [ThmBind.read"%144%102%20%102%21%149%161%207$1@2%207$0@3%147$1@$0@2|@|@2%144%102%20%102%21%149%161%219$1@2%219$0@3%147$1@$0@2|@|@2%102%20%102%21%149%161%208$1@2%208$0@3%147$1@$0@2|@|@3"])
  fun op datatype_configuration x = x
    val op datatype_configuration =
    ThmBind.DT(((("ssm11",42),[("bool",[25,170])]),["DISK_THM"]),
               [ThmBind.read"%192%45%186@2"])
  fun op configuration_11 x = x
    val op configuration_11 =
    ThmBind.DT(((("ssm11",43),
                [("bool",[26,50,55,62,180]),("ind_type",[33,34]),
                 ("pair",[8,9]),("ssm11",[37,38,39])]),["DISK_THM"]),
               [ThmBind.read"%118%22%114%27%128%31%128%34%103%36%127%38%118%25%114%29%128%32%128%35%103%37%127%39%149%150%186$11@$10@$9@$8@$7@$6@2%186$5@$4@$3@$2@$1@$0@3%144%152$11@$5@2%144%151$10@$4@2%144%155$9@$3@2%144%155$8@$2@2%144%148$7@$1@2%154$6@$0@7|@|@|@|@|@|@|@|@|@|@|@|@"])
  fun op configuration_case_cong x = x
    val op configuration_case_cong =
    ThmBind.DT(((("ssm11",44),
                [("bool",[26,180]),("ssm11",[37,38,39,40])]),["DISK_THM"]),
               [ThmBind.read"%107%4%107%7%120%49%162%144%150$2@$1@2%118%22%114%27%128%31%128%34%103%36%127%38%162%150$7@%186$5@$4@$3@$2@$1@$0@3%146$6$5@$4@$3@$2@$1@$0@2%51$5@$4@$3@$2@$1@$0@3|@|@|@|@|@|@3%146%205$2@$0@2%205$1@%51@3|@|@|@"])
  fun op configuration_nchotomy x = x
    val op configuration_nchotomy =
    ThmBind.DT(((("ssm11",45),
                [("bool",[26,180]),("ssm11",[37,38,39])]),["DISK_THM"]),
               [ThmBind.read"%107%43%171%48%168%53%179%69%179%70%164%81%178%71%150$6@%186$5@$4@$3@$2@$1@$0@2|@|@|@|@|@|@|@"])
  fun op configuration_Axiom x = x
    val op configuration_Axiom =
    ThmBind.DT(((("ssm11",46),
                [("bool",[26,180]),("ind_type",[33,34]),("pair",[8,9]),
                 ("ssm11",[37,38,39])]),["DISK_THM"]),
               [ThmBind.read"%120%49%172%64%118%22%114%27%128%31%128%34%103%36%127%38%146$6%186$5@$4@$3@$2@$1@$0@3$7$5@$4@$3@$2@$1@$0@2|@|@|@|@|@|@|@|@"])
  fun op configuration_induction x = x
    val op configuration_induction =
    ThmBind.DT(((("ssm11",47),
                [("bool",[26]),("ssm11",[37,38,39])]),["DISK_THM"]),
               [ThmBind.read"%119%15%162%118%48%114%53%128%69%128%70%103%81%127%71$6%186$5@$4@$3@$2@$1@$0@2|@|@|@|@|@|@2%107%42$1$0@|@2|@"])
  fun op configuration_one_one x = x
    val op configuration_one_one =
    ThmBind.DT(((("ssm11",48),
                [("bool",[26,50,55,62,180]),("ind_type",[33,34]),
                 ("pair",[8,9]),("ssm11",[37,38,39])]),["DISK_THM"]),
               [ThmBind.read"%118%22%114%27%128%31%128%34%103%36%127%38%118%25%114%29%128%32%128%35%103%37%127%39%149%150%186$11@$10@$9@$8@$7@$6@2%186$5@$4@$3@$2@$1@$0@3%144%152$11@$5@2%144%151$10@$4@2%144%155$9@$3@2%144%155$8@$2@2%144%148$7@$1@2%154$6@$0@7|@|@|@|@|@|@|@|@|@|@|@|@"])
  fun op CFGInterpret_ind x = x
    val op CFGInterpret_ind =
    ThmBind.DT(((("ssm11",51),
                [("bool",[25,26,46,47,52,53,57,62,71,75,76,77,79,180]),
                 ("list",[46]),("pair",[5,16]),("relation",[107,113]),
                 ("sat",[1,3,5,6,7,11,12,13,14,15]),
                 ("ssm11",[37,38,39])]),["DISK_THM"]),
               [ThmBind.read"%122%17%162%144%105%3%130%11%131%12%118%40%114%84%128%82%104%67%128%68%103%83%127%76$10%138$9@%143$8@$7@3%186$6@$5@$4@%189$3@$2@2$1@$0@2|@|@|@|@|@|@|@|@|@|@2%132%97%118%92%114%93%128%94%103%95%127%96$6$5@%186$4@$3@$2@%194@$1@$0@2|@|@|@|@|@|@3%105%89%130%91%131%98%107%99$4%138$3@%143$2@$1@3$0@|@|@|@|@2|@"])
  fun op CFGInterpret_def x = x
    val op CFGInterpret_def =
    ThmBind.DT(((("ssm11",52),
                [("bool",[15,57]),("combin",[19]),("list",[6]),
                 ("pair",[49]),("relation",[113,132]),
                 ("ssm11",[40,49,50])]),["DISK_THM"]),
               [ThmBind.read"%149%187%138%3@%143%11@%12@3%186%40@%84@%82@%189%67@%68@2%83@%76@3%144%215%138%3@%143%11@%12@3%82@2%144%214%138%3@%143%11@%12@3%67@2%214%138%3@%143%11@%12@3%84%83@5"])
  fun op TR_rules x = x
    val op TR_rules =
    ThmBind.DT(((("ssm11",54),
                [("bool",[26]),("ssm11",[53])]),["DISK_THM"]),
               [ThmBind.read"%144%118%40%106%14%116%10%105%3%130%11%131%12%115%13%103%81%128%82%114%84%102%44%128%68%127%77%162%144$12%216$11@%213%197$2@5%187%138$9@%143$8@$7@3%186$12@$3@$4@%189%216$11@%213%197$2@4$1@2$5@$0@4%199%138$9@%143$8@$7@3%208$2@2%186$12@$3@$4@%189%216$11@%213%197$2@4$1@2$5@$0@2%186$12@$3@$4@$1@$10$5@%208$2@3%188$6$5@%208$2@3$0@4|@|@|@|@|@|@|@|@|@|@|@|@|@2%144%118%40%106%14%116%10%105%3%130%11%131%12%115%13%103%81%128%82%114%84%102%44%128%68%127%77%162%144$12%216$11@%213%197$2@5%187%138$9@%143$8@$7@3%186$12@$3@$4@%189%216$11@%213%197$2@4$1@2$5@$0@4%199%138$9@%143$8@$7@3%219$2@2%186$12@$3@$4@%189%216$11@%213%197$2@4$1@2$5@$0@2%186$12@$3@$4@$1@$10$5@%219$2@3%188$6$5@%219$2@3$0@4|@|@|@|@|@|@|@|@|@|@|@|@|@2%118%40%116%10%105%3%130%11%131%12%115%13%103%81%128%82%114%84%102%44%104%100%128%68%127%77%162%220$12$2@3%199%138$10@%143$9@$8@3%207$3@2%186$12@$4@$5@%189$2@$1@2$6@$0@2%186$12@$4@$5@$1@$11$6@%207$3@3%188$7$6@%207$3@3$0@4|@|@|@|@|@|@|@|@|@|@|@|@|@3"])
  fun op TR_ind x = x
    val op TR_ind =
    ThmBind.DT(((("ssm11",55),
                [("bool",[26]),("ssm11",[53])]),["DISK_THM"]),
               [ThmBind.read"%123%19%162%144%118%40%106%14%116%10%105%3%130%11%131%12%115%13%103%81%128%82%114%84%102%44%128%68%127%77%162%144$12%216$11@%213%197$2@5%187%138$9@%143$8@$7@3%186$12@$3@$4@%189%216$11@%213%197$2@4$1@2$5@$0@4$13%138$9@%143$8@$7@3%208$2@2%186$12@$3@$4@%189%216$11@%213%197$2@4$1@2$5@$0@2%186$12@$3@$4@$1@$10$5@%208$2@3%188$6$5@%208$2@3$0@4|@|@|@|@|@|@|@|@|@|@|@|@|@2%144%118%40%106%14%116%10%105%3%130%11%131%12%115%13%103%81%128%82%114%84%102%44%128%68%127%77%162%144$12%216$11@%213%197$2@5%187%138$9@%143$8@$7@3%186$12@$3@$4@%189%216$11@%213%197$2@4$1@2$5@$0@4$13%138$9@%143$8@$7@3%219$2@2%186$12@$3@$4@%189%216$11@%213%197$2@4$1@2$5@$0@2%186$12@$3@$4@$1@$10$5@%219$2@3%188$6$5@%219$2@3$0@4|@|@|@|@|@|@|@|@|@|@|@|@|@2%118%40%116%10%105%3%130%11%131%12%115%13%103%81%128%82%114%84%102%44%104%100%128%68%127%77%162%220$12$2@3$13%138$10@%143$9@$8@3%207$3@2%186$12@$4@$5@%189$2@$1@2$6@$0@2%186$12@$4@$5@$1@$11$6@%207$3@3%188$7$6@%207$3@3$0@4|@|@|@|@|@|@|@|@|@|@|@|@|@4%132%23%135%28%107%30%107%33%162%199$3@$2@$1@$0@2$4$3@$2@$1@$0@2|@|@|@|@2|@"])
  fun op TR_strongind x = x
    val op TR_strongind =
    ThmBind.DT(((("ssm11",56),
                [("bool",[26]),("ssm11",[53])]),["DISK_THM"]),
               [ThmBind.read"%123%19%162%144%118%40%106%14%116%10%105%3%130%11%131%12%115%13%103%81%128%82%114%84%102%44%128%68%127%77%162%144$12%216$11@%213%197$2@5%187%138$9@%143$8@$7@3%186$12@$3@$4@%189%216$11@%213%197$2@4$1@2$5@$0@4$13%138$9@%143$8@$7@3%208$2@2%186$12@$3@$4@%189%216$11@%213%197$2@4$1@2$5@$0@2%186$12@$3@$4@$1@$10$5@%208$2@3%188$6$5@%208$2@3$0@4|@|@|@|@|@|@|@|@|@|@|@|@|@2%144%118%40%106%14%116%10%105%3%130%11%131%12%115%13%103%81%128%82%114%84%102%44%128%68%127%77%162%144$12%216$11@%213%197$2@5%187%138$9@%143$8@$7@3%186$12@$3@$4@%189%216$11@%213%197$2@4$1@2$5@$0@4$13%138$9@%143$8@$7@3%219$2@2%186$12@$3@$4@%189%216$11@%213%197$2@4$1@2$5@$0@2%186$12@$3@$4@$1@$10$5@%219$2@3%188$6$5@%219$2@3$0@4|@|@|@|@|@|@|@|@|@|@|@|@|@2%118%40%116%10%105%3%130%11%131%12%115%13%103%81%128%82%114%84%102%44%104%100%128%68%127%77%162%220$12$2@3$13%138$10@%143$9@$8@3%207$3@2%186$12@$4@$5@%189$2@$1@2$6@$0@2%186$12@$4@$5@$1@$11$6@%207$3@3%188$7$6@%207$3@3$0@4|@|@|@|@|@|@|@|@|@|@|@|@|@4%132%23%135%28%107%30%107%33%162%199$3@$2@$1@$0@2$4$3@$2@$1@$0@2|@|@|@|@2|@"])
  fun op TR_cases x = x
    val op TR_cases =
    ThmBind.DT(((("ssm11",57),
                [("bool",[26]),("ssm11",[53])]),["DISK_THM"]),
               [ThmBind.read"%132%23%135%28%107%30%107%33%149%199$3@$2@$1@$0@2%204%171%40%167%14%170%10%166%3%180%11%181%12%169%13%164%81%179%82%168%84%163%44%179%68%178%77%144%158$16@%138$9@%143$8@$7@4%144%161$15@%208$2@3%144%150$14@%186$12@$3@$4@%189%216$11@%213%197$2@4$1@2$5@$0@3%144%150$13@%186$12@$3@$4@$1@$10$5@%208$2@3%188$6$5@%208$2@3$0@4%144$12%216$11@%213%197$2@5%187%138$9@%143$8@$7@3%186$12@$3@$4@%189%216$11@%213%197$2@4$1@2$5@$0@7|@|@|@|@|@|@|@|@|@|@|@|@|@2%204%171%40%167%14%170%10%166%3%180%11%181%12%169%13%164%81%179%82%168%84%163%44%179%68%178%77%144%158$16@%138$9@%143$8@$7@4%144%161$15@%219$2@3%144%150$14@%186$12@$3@$4@%189%216$11@%213%197$2@4$1@2$5@$0@3%144%150$13@%186$12@$3@$4@$1@$10$5@%219$2@3%188$6$5@%219$2@3$0@4%144$12%216$11@%213%197$2@5%187%138$9@%143$8@$7@3%186$12@$3@$4@%189%216$11@%213%197$2@4$1@2$5@$0@7|@|@|@|@|@|@|@|@|@|@|@|@|@2%171%40%170%10%166%3%180%11%181%12%169%13%164%81%179%82%168%84%163%44%165%100%179%68%178%77%144%158$16@%138$10@%143$9@$8@4%144%161$15@%207$3@3%144%150$14@%186$12@$4@$5@%189$2@$1@2$6@$0@3%144%150$13@%186$12@$4@$5@$1@$11$6@%207$3@3%188$7$6@%207$3@3$0@4%220$12$2@6|@|@|@|@|@|@|@|@|@|@|@|@|@4|@|@|@|@"])
  fun op TR_EQ_rules_thm x = x
    val op TR_EQ_rules_thm =
    ThmBind.DT(((("ssm11",58),
                [("bool",
                 [13,25,26,27,29,35,46,47,50,51,52,53,55,62,92,93,95,180]),
                 ("combin",[19]),("ind_type",[33,34]),("list",[9]),
                 ("pair",[8,9]),
                 ("sat",[1,3,5,6,7,11,12,13,14,15,17,18,19,20,23]),
                 ("ssm11",
                 [18,19,20,21,22,23,24,37,38,39,53])]),["DISK_THM"]),
               [ThmBind.read"%144%149%199%138%3@%143%11@%12@3%208%44@2%186%40@%84@%82@%189%216%14@%213%197%44@4%68@2%81@%77@2%186%40@%84@%82@%68@%10%81@%208%44@3%188%13%81@%208%44@3%77@4%144%40%216%14@%213%197%44@5%187%138%3@%143%11@%12@3%186%40@%84@%82@%189%216%14@%213%197%44@4%68@2%81@%77@5%144%149%199%138%3@%143%11@%12@3%219%44@2%186%40@%84@%82@%189%216%14@%213%197%44@4%68@2%81@%77@2%186%40@%84@%82@%68@%10%81@%219%44@3%188%13%81@%219%44@3%77@4%144%40%216%14@%213%197%44@5%187%138%3@%143%11@%12@3%186%40@%84@%82@%189%216%14@%213%197%44@4%68@2%81@%77@5%149%199%138%3@%143%11@%12@3%207%44@2%186%40@%84@%82@%189%100@%68@2%81@%77@2%186%40@%84@%82@%68@%10%81@%207%44@3%188%13%81@%207%44@3%77@4%220%40%100@5"])
  fun op TRrule0 x = x
    val op TRrule0 =
    ThmBind.DT(((("ssm11",59),
                [("bool",
                 [13,25,26,27,29,35,46,47,50,51,52,53,55,62,92,93,95,180]),
                 ("combin",[19]),("ind_type",[33,34]),("list",[9]),
                 ("pair",[8,9]),
                 ("sat",[1,3,5,6,7,11,12,13,14,15,17,18,19,20,23]),
                 ("ssm11",
                 [18,19,20,21,22,23,24,37,38,39,53])]),["DISK_THM"]),
               [ThmBind.read"%149%199%138%3@%143%11@%12@3%208%44@2%186%40@%84@%82@%189%216%14@%213%197%44@4%68@2%81@%77@2%186%40@%84@%82@%68@%10%81@%208%44@3%188%13%81@%208%44@3%77@4%144%40%216%14@%213%197%44@5%187%138%3@%143%11@%12@3%186%40@%84@%82@%189%216%14@%213%197%44@4%68@2%81@%77@4"])
  fun op TRrule1 x = x
    val op TRrule1 =
    ThmBind.DT(((("ssm11",60),
                [("bool",
                 [13,25,26,27,29,35,46,47,50,51,52,53,55,62,92,93,95,180]),
                 ("combin",[19]),("ind_type",[33,34]),("list",[9]),
                 ("pair",[8,9]),
                 ("sat",[1,3,5,6,7,11,12,13,14,15,17,18,19,20,23]),
                 ("ssm11",
                 [18,19,20,21,22,23,24,37,38,39,53])]),["DISK_THM"]),
               [ThmBind.read"%149%199%138%3@%143%11@%12@3%219%44@2%186%40@%84@%82@%189%216%14@%213%197%44@4%68@2%81@%77@2%186%40@%84@%82@%68@%10%81@%219%44@3%188%13%81@%219%44@3%77@4%144%40%216%14@%213%197%44@5%187%138%3@%143%11@%12@3%186%40@%84@%82@%189%216%14@%213%197%44@4%68@2%81@%77@4"])
  fun op TR_discard_cmd_rule x = x
    val op TR_discard_cmd_rule =
    ThmBind.DT(((("ssm11",61),
                [("bool",
                 [13,25,26,27,29,35,46,47,50,51,52,53,55,62,92,93,95,180]),
                 ("combin",[19]),("ind_type",[33,34]),("list",[9]),
                 ("pair",[8,9]),
                 ("sat",[1,3,5,6,7,11,12,13,14,15,17,18,19,20,23]),
                 ("ssm11",
                 [18,19,20,21,22,23,24,37,38,39,53])]),["DISK_THM"]),
               [ThmBind.read"%149%199%138%3@%143%11@%12@3%207%44@2%186%40@%84@%82@%189%100@%68@2%81@%77@2%186%40@%84@%82@%68@%10%81@%207%44@3%188%13%81@%207%44@3%77@4%220%40%100@3"])
  fun op TR_exec_cmd_rule x = x
    val op TR_exec_cmd_rule =
    ThmBind.DT(((("ssm11",62),
                [("bool",
                 [13,25,26,27,29,35,46,47,50,51,52,53,55,62,92,93,95,180]),
                 ("combin",[19]),("ind_type",[33,34]),("list",[9]),
                 ("pair",[8,9]),
                 ("sat",[1,3,5,6,7,11,12,13,14,15,17,18,19,20,23]),
                 ("ssm11",
                 [18,19,20,21,22,23,24,37,38,39,53])]),["DISK_THM"]),
               [ThmBind.read"%118%40%128%82%114%84%106%14%102%44%128%68%103%81%127%77%162%105%3%130%11%131%12%162%187%138$2@%143$1@$0@3%186$10@$8@$9@%189%216$7@%213%197$6@4$5@2$4@$3@3%214%138$2@%143$1@$0@3%213%197$6@4|@|@|@2%116%10%115%13%105%3%130%11%131%12%149%199%138$2@%143$1@$0@3%208$8@2%186$12@$10@$11@%189%216$9@%213%197$8@4$7@2$6@$5@2%186$12@$10@$11@$7@$4$6@%208$8@3%188$3$6@%208$8@3$5@4%144$12%216$9@%213%197$8@5%144%187%138$2@%143$1@$0@3%186$12@$10@$11@%189%216$9@%213%197$8@4$7@2$6@$5@3%214%138$2@%143$1@$0@3%213%197$8@6|@|@|@|@|@2|@|@|@|@|@|@|@|@"])

  val _ = DB.bindl "ssm11"
  [("order_TY_DEF",order_TY_DEF,DB.Def),
   ("order_case_def",order_case_def,DB.Def),
   ("order_size_def",order_size_def,DB.Def),
   ("trType_TY_DEF",trType_TY_DEF,DB.Def),
   ("trType_case_def",trType_case_def,DB.Def),
   ("trType_size_def",trType_size_def,DB.Def),
   ("configuration_TY_DEF",configuration_TY_DEF,DB.Def),
   ("configuration_case_def",configuration_case_def,DB.Def),
   ("configuration_size_def",configuration_size_def,DB.Def),
   ("TR_def",TR_def,DB.Def), ("datatype_order",datatype_order,DB.Thm),
   ("order_11",order_11,DB.Thm), ("order_distinct",order_distinct,DB.Thm),
   ("order_case_cong",order_case_cong,DB.Thm),
   ("order_nchotomy",order_nchotomy,DB.Thm),
   ("order_Axiom",order_Axiom,DB.Thm),
   ("order_induction",order_induction,DB.Thm),
   ("order_distinct_clauses",order_distinct_clauses,DB.Thm),
   ("order_one_one",order_one_one,DB.Thm),
   ("datatype_trType",datatype_trType,DB.Thm),
   ("trType_11",trType_11,DB.Thm),
   ("trType_distinct",trType_distinct,DB.Thm),
   ("trType_case_cong",trType_case_cong,DB.Thm),
   ("trType_nchotomy",trType_nchotomy,DB.Thm),
   ("trType_Axiom",trType_Axiom,DB.Thm),
   ("trType_induction",trType_induction,DB.Thm),
   ("trType_distinct_clauses",trType_distinct_clauses,DB.Thm),
   ("trType_one_one",trType_one_one,DB.Thm),
   ("datatype_configuration",datatype_configuration,DB.Thm),
   ("configuration_11",configuration_11,DB.Thm),
   ("configuration_case_cong",configuration_case_cong,DB.Thm),
   ("configuration_nchotomy",configuration_nchotomy,DB.Thm),
   ("configuration_Axiom",configuration_Axiom,DB.Thm),
   ("configuration_induction",configuration_induction,DB.Thm),
   ("configuration_one_one",configuration_one_one,DB.Thm),
   ("CFGInterpret_ind",CFGInterpret_ind,DB.Thm),
   ("CFGInterpret_def",CFGInterpret_def,DB.Thm),
   ("TR_rules",TR_rules,DB.Thm), ("TR_ind",TR_ind,DB.Thm),
   ("TR_strongind",TR_strongind,DB.Thm), ("TR_cases",TR_cases,DB.Thm),
   ("TR_EQ_rules_thm",TR_EQ_rules_thm,DB.Thm), ("TRrule0",TRrule0,DB.Thm),
   ("TRrule1",TRrule1,DB.Thm),
   ("TR_discard_cmd_rule",TR_discard_cmd_rule,DB.Thm),
   ("TR_exec_cmd_rule",TR_exec_cmd_rule,DB.Thm)]

  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "ssm11",
    thydataty = "rule_induction",
    read = ThmBind.read,
    data = "ssm11.TR_strongind"
  }
  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "ssm11",
    thydataty = "compute",
    read = ThmBind.read,
    data = "ssm11.CFGInterpret_def"
  }
  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "ssm11",
    thydataty = "TypeGrammarDeltas",
    read = ThmBind.read,
    data =
        "NTY5.ssm11,5.orderNTY5.ssm11,6.trTypeNTY5.ssm11,13.configuration"
  }
  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "ssm11",
    thydataty = "TermGrammarDeltas",
    read = ThmBind.read,
    data =
        "OO4.SOME4.%197OO4.NONE4.%195OO10.order_CASE4.%211OO10.order_size4.%212OO4.case4.%211OO7.discard4.%207OO4.trap4.%219OO4.exec4.%208OO11.trType_CASE4.%217OO11.trType_size4.%218OO4.case4.%217OO3.CFG4.%186OO18.configuration_CASE4.%205OO18.configuration_size4.%206OO4.case4.%205OO12.CFGInterpret4.%187OO2.TR4.%199"
  }
  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val ssm11_grammars = merge_grammars ["satList"]
  local
  val (tyUDs, tmUDs) = GrammarDeltas.thy_deltas{thyname="ssm11"}
  val addtmUDs = term_grammar.add_deltas tmUDs
  val addtyUDs = type_grammar.apply_deltas tyUDs
  in
  val ssm11_grammars = 
    Portable.## (addtyUDs,addtmUDs) ssm11_grammars
  val _ = Parse.grammarDB_insert("ssm11",ssm11_grammars)
  val _ = Parse.temp_set_grammars (addtyUDs (Parse.type_grammar()), addtmUDs (Parse.term_grammar()))
  end (* addUDs local *)
  end


  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG order_Axiom,
           case_def=order_case_def,
           case_cong=order_case_cong,
           induction=ORIG order_induction,
           nchotomy=order_nchotomy,
           size=SOME(Parse.Term`(ssm11$order_size) :('command -> num$num) -> 'command ssm11$order -> num$num`,
                     ORIG order_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME order_11,
           distinct=SOME order_distinct,
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
          {ax=ORIG trType_Axiom,
           case_def=trType_case_def,
           case_cong=trType_case_cong,
           induction=ORIG trType_induction,
           nchotomy=trType_nchotomy,
           size=SOME(Parse.Term`(ssm11$trType_size) :('command -> num$num) -> 'command ssm11$trType -> num$num`,
                     ORIG trType_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME trType_11,
           distinct=SOME trType_distinct,
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
          {ax=ORIG configuration_Axiom,
           case_def=configuration_case_def,
           case_cong=configuration_case_cong,
           induction=ORIG configuration_induction,
           nchotomy=configuration_nchotomy,
           size=SOME(Parse.Term`(ssm11$configuration_size) :('command -> num$num) ->
('d -> num$num) ->
('e -> num$num) ->
('output -> num$num) ->
('principal -> num$num) ->
('state -> num$num) ->
('command, 'd, 'e, 'output, 'principal, 'state) ssm11$configuration ->
num$num`,
                     ORIG configuration_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME configuration_11,
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
val _ = Theory.load_complete "ssm11"
end
