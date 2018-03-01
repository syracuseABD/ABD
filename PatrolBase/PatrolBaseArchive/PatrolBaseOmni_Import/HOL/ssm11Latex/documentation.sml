app load ["ssm11Theory","satListTheory","ssminfRules","EmitTeX"];

open EmitTeX;

print_theories_as_tex_doc
["ssm11","satList","ssminf"] "ssm11Report";
