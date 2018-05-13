app load [ "PBTypeIntegratedTheory", "ssmPBTheory",
    	   "PBIntegratedDefTheory",
          "EmitTeX"];

open EmitTeX;

print_theories_as_tex_doc
["PBTypeIntegrated", "ssmPB","PBIntegratedDef"] "Report";
