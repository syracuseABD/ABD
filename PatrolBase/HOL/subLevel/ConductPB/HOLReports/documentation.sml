app load [ "ConductPBTypeTheory", "ssmConductPBTheory",
          "EmitTeX"];

open EmitTeX;

print_theories_as_tex_doc
["ConductPBType", "ssmConductPB"] "Report";
