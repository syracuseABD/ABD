app load ["OMNITypeTheory","ssmPBTheory","PBTypeTheory","EmitTeX"];

open EmitTeX;

print_theories_as_tex_doc
["OMNIType","ssmPB","PBType"] "OMNIReport";
