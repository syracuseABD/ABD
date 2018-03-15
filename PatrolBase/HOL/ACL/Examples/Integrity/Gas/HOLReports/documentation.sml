(************ Builds documentation **********)
app load ["IntegrityLevelsTheory", "gasTheory", "EmitTeX"];
open IntegrityLevelsTheory gasTheory EmitTeX;
print_theories_as_tex_doc ["IntegrityLevels", "gas"] "gasReport";