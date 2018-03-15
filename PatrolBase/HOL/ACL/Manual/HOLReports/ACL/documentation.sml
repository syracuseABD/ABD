app load ["aclfoundationTheory","aclsemanticsTheory",
          "aclrulesTheory","aclDrulesTheory","EmitTeX"];
open EmitTeX;


print_theories_as_tex_doc
["aclfoundation","aclsemantics","aclrules","aclDrules"] "aclReport";
