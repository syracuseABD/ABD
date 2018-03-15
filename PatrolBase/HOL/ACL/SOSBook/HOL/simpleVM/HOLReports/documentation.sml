(************************************************************)
(* documentation.sml: 9 October 2012                        *)
(* Author: Shiu-Kai Chin                                    *)
(* File used to generate documentation for reports in LaTeX *)
(************************************************************)

(* We need to load the HOL theories we want to print out *)
(* as well as the EmitTeX library in HOL, which          *)
(* generates the LaTeX macros for us.                    *)

app load ["rm1Theory","EmitTeX"];
open EmitTeX;


print_theories_as_tex_doc
["rm1"] "rm1Report";
