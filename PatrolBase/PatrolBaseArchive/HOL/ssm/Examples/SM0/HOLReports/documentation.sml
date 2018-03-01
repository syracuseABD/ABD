app load ["ssmTheory","SM0Theory","SM0SolutionsTheory",
          "EmitTeX"];

open EmitTeX;

print_theories_as_tex_doc
["ssm","SM0","SM0Solutions"] "SM0Report";
