structure example1Theory :> example1Theory =
struct
  val _ = if !Globals.print_thy_loads then TextIO.print "Loading example1Theory ... " else ()
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
          ("example1",
          Arbnum.fromString "1500586888",
          Arbnum.fromString "183482")
          [("indexedLists",
           Arbnum.fromString "1497837441",
           Arbnum.fromString "85466"),
           ("patternMatches",
           Arbnum.fromString "1497837479",
           Arbnum.fromString "270614")];
  val _ = Theory.incorporate_types "example1" [];

  val idvector = 
    let fun ID(thy,oth) = {Thy = thy, Other = oth}
    in Vector.fromList
  [ID("min", "bool"), ID("bool", "!"), ID("min", "fun"), ID("min", "==>")]
  end;
  local open SharingTables
  in
  val tyvector = build_type_vector idvector
  [TYOP [0], TYOP [2, 0, 0], TYOP [2, 1, 0], TYOP [2, 0, 1]]
  end
  val _ = Theory.incorporate_consts "example1" tyvector [];

  local open SharingTables
  in
  val tmvector = build_term_vector idvector tyvector
  [TMV("p", 0), TMV("q", 0), TMC(1, 2), TMC(3, 3)]
  end
  structure ThmBind = struct
    val DT = Thm.disk_thm
    val read = Term.read_raw tmvector
  end
  fun op prob1Theorem x = x
    val op prob1Theorem =
    ThmBind.DT(((("example1",0),[]),[]),
               [ThmBind.read"%2%0%2%1%3$1@%3%3$1@$0@2$0@2|@|@"])
  fun op demoTheorem x = x
    val op demoTheorem =
    ThmBind.DT(((("example1",1),
                [("bool",[25,26,46,47,52,53,62,70]),
                 ("sat",[1,3,5,6,7,11,12,13,14,15])]),["DISK_THM"]),
               [ThmBind.read"%2%0%2%1%3$1@%3%3$1@$0@2$0@2|@|@"])

  val _ = DB.bindl "example1"
  [("prob1Theorem",prob1Theorem,DB.Thm),
   ("demoTheorem",demoTheorem,DB.Thm)]

  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val example1_grammars = merge_grammars ["indexedLists", "patternMatches"]
  local
  val (tyUDs, tmUDs) = GrammarDeltas.thy_deltas{thyname="example1"}
  val addtmUDs = term_grammar.add_deltas tmUDs
  val addtyUDs = type_grammar.apply_deltas tyUDs
  in
  val example1_grammars = 
    Portable.## (addtyUDs,addtmUDs) example1_grammars
  val _ = Parse.grammarDB_insert("example1",example1_grammars)
  val _ = Parse.temp_set_grammars (addtyUDs (Parse.type_grammar()), addtmUDs (Parse.term_grammar()))
  end (* addUDs local *)
  end

val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "example1"
end
