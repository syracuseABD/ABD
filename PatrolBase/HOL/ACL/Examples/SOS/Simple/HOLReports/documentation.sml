app load ["foundationTheory","sos0Theory","sos1Theory","EmitTeX"];
open foundationTheory sos0Theory sos1Theory EmitTeX;

print_theories_as_tex_doc
["foundation","sos0","sos1"] "SimpleSOSReport";
