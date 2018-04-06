app load [ "MoveToPBTypeTheory", "ssmMoveToPBTheory",
          "EmitTeX"];

open EmitTeX;

print_theories_as_tex_doc
["MoveToPBType", "ssmMoveToPB"] "Report";
