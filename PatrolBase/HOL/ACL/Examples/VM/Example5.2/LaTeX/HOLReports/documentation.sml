(************************************************************)
(* documentation.sml: 9 October 2012                        *)
(* Author: Shiu-Kai Chin                                    *)
(* File used to generate documentation for reports in LaTeX *)
(************************************************************)

(* We need to load the HOL theories we want to print out *)
(* as well as the EmitTeX library in HOL, which          *)
(* generates the LaTeX macros for us.                    *)

app load ["accessTheory","EmitTeX"];
open EmitTeX;

(* In what follows, we use print_theories_as_tex_doc *)
(* to generate a report in LaTeX that pretty prints  *)
(* aclfoundationTheory and c2DrulesTheory. We call   *)
(* this report c2rulesReport.                        *)
(* NOTE: existing copies of c2rulesReport.tex must   *)
(* be DELETED or else print_theories_as_tex_doc will *)
(* fail.                                             *)
print_theories_as_tex_doc
["access"] "vmReport";