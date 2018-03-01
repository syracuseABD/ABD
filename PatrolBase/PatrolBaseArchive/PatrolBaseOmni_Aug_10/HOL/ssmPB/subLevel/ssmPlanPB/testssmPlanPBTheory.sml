structure testssmPlanPBTheory :> testssmPlanPBTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading testssmPlanPBTheory ... " else ()
  open Type Term Thm
  infixr -->

  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  (*  Parents *)
  local open OMNITypeTheory PlanPBTypeTheory ssm11Theory
  in end;
  val _ = Theory.link_parents
          ("testssmPlanPB",
          Arbnum.fromString "1500860947",
          Arbnum.fromString "679869")
          [("PlanPBType",
           Arbnum.fromString "1500860943",
           Arbnum.fromString "711843"),
           ("ssm11",
           Arbnum.fromString "1499652452",
           Arbnum.fromString "890464"),
           ("OMNIType",
           Arbnum.fromString "1499574745",
           Arbnum.fromString "168021")];
  val _ = Theory.incorporate_types "testssmPlanPB" [];

  val idvector = 
    let fun ID(thy,oth) = {Thy = thy, Other = oth}
    in Vector.fromList
  []
  end;
  local open SharingTables
  in
  val tyvector = build_type_vector idvector
  []
  end
  val _ = Theory.incorporate_consts "testssmPlanPB" tyvector [];

  local open SharingTables
  in
  val tmvector = build_term_vector idvector tyvector
  []
  end
  structure ThmBind = struct
    val DT = Thm.disk_thm
    val read = Term.read_raw tmvector
  end


  val _ = DB.bindl "testssmPlanPB" []

  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val testssmPlanPB_grammars = merge_grammars ["PlanPBType", "ssm11",
                                               "OMNIType"]
  local
  val (tyUDs, tmUDs) = GrammarDeltas.thy_deltas{thyname="testssmPlanPB"}
  val addtmUDs = term_grammar.add_deltas tmUDs
  val addtyUDs = type_grammar.apply_deltas tyUDs
  in
  val testssmPlanPB_grammars = 
    Portable.## (addtyUDs,addtmUDs) testssmPlanPB_grammars
  val _ = Parse.grammarDB_insert("testssmPlanPB",testssmPlanPB_grammars)
  val _ = Parse.temp_set_grammars (addtyUDs (Parse.type_grammar()), addtmUDs (Parse.term_grammar()))
  end (* addUDs local *)
  end

val _ = if !Globals.print_thy_loads then print "done\n" else ()
val _ = Theory.load_complete "testssmPlanPB"
end
