app load [ "PlanPBTypeTheory", "ssmPlanPBTheory",
          "EmitTeX"];

open EmitTeX;

print_theories_as_tex_doc
["PlanPBType", "ssmPlanPB"] "Report";
