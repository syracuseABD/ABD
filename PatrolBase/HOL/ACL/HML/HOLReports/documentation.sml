app load ["mmFoundationTheory","substitutionTheory","EmitTeX"];

open mmFoundationTheory EmitTeX;

print_theories_as_tex_doc
["mmFoundation","substitution"] "mmFoundationReport";
