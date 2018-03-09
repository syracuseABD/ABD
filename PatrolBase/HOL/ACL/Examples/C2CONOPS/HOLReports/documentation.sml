app load ["commandTheory","missionRolesTheory","missionStaffTheory",
   "missionKeysTheory","missionCONOPS1Theory","missionCONOPS2Theory","EmitTeX"];

open commandTheory missionRolesTheory missionStaffTheory
   missionKeysTheory missionCONOPS1Theory missionCONOPS2Theory EmitTeX;

print_theories_as_tex_doc
["command","missionRoles","missionCONOPS1","missionStaff","missionCONOPS2",
 "missionKeys"]
"MissionReport";
