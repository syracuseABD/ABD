app load [ "MoveToORPTypeTheory", "ssmMoveToORPTheory",
          "EmitTeX"];

open EmitTeX;

print_theories_as_tex_doc
["MoveToORPType", "ssmMoveToORP"] "Report";
