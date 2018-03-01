app load ["PBTypeTheory",
          "ssmPBTheory",
          "EmitTeX"];

open EmitTeX;

print_theories_as_tex_doc
["PBType","ssmPB"] "ssmPBReport";
