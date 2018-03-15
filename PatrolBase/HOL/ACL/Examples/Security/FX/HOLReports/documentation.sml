(************************************************************)
(* documentation.sml: 10 March 2013                         *)
(* Author: Shiu-Kai Chin                                    *)
(* File used to generate documentation for reports in LaTeX *)
(************************************************************)

(* We need to load the HOL theories we want to print out *)
(* as well as the EmitTeX library in HOL, which          *)
(* generates the LaTeX macros for us.                    *)

app 
 load 
 ["SecurityLevelsTheory","MilitarySecurityTheory","EmitTeX"];
open SecurityLevelsTheory MilitarySecurityTheory EmitTeX;


print_theories_as_tex_doc
["SecurityLevels","MilitarySecurity"] "FXReport";
