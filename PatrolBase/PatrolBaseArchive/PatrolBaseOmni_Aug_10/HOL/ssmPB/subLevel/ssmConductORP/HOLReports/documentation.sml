app load ["conductORPTypeTheory",
          "ssmConductPBTheory",
          "EmitTeX"];

open EmitTeX;

print_theories_as_tex_doc
["conductORPType","ssmConductORP"] "conductORPReport";
