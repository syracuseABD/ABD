app load ["OMNITypeTheory", "ssm11Theory", "ssmTheory",
    	  "satListTheory","ssminfRules",
    	  "ssmPBTheory",
	  "PBTypeIntegratedTheory","PBIntegratedDefTheory",
          "ssmConductORPTheory", "ConductORPTypeTheory",
	  "ssmConductPBTheory","ConductPBTypeTheory",
	  "ssmMoveToORPTheory","MoveToORPTypeTheory",
	  "ssmMoveToPBTheory","MoveToPBTypeTheory",
	  "ssmPlanPBTheory","PlanPBTypeTheory",
          "EmitTeX"];

open EmitTeX;

print_theories_as_tex_doc
["OMNIType","ssm11", "ssm",
 "satList","ssminfRules",
 "ssmPB",
 "PBTypeIntegrated","PBIntegratedDef",
 "ssmConductORP","ConductORPType",
 "ssmConductPB","ConductPBType","ssmMoveToORP","MoveToORPType",
 "ssmMoveToPB","MoveToPBType","ssmPlanPB","PlanPBType" ] "OMNIReport";
