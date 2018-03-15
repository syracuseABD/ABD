app load ["cipherTheory","commandTheory","missionRolesTheory","missionStaffTheory",
          "revisedMissionKeysTheory","messageCertificateTheory","BFOConopsTheory","EmitTeX"];

open cipherTheory commandTheory missionRolesTheory missionStaffTheory revisedMissionKeysTheory 
     messageCertificateTheory BFOConopsTheory EmitTeX;

print_theories_as_tex_doc
["cipher","missionStaff","revisedMissionKeys","messageCertificate","BFOConops"]
"SecureMessageReport";
