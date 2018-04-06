app load [ "ConductORPTypeTheory", "ssmConductORPTheory",
          "EmitTeX"];

open EmitTeX;

print_theories_as_tex_doc
["ConductORPType", "ssmConductORP"] "Report";
