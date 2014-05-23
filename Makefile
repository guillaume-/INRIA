SOURCES = ms_fundamental_interfaces.ml ms_identifier.ml ms_printable_objects.ml ms_idhtbl.ml ms_syntax_tree.ml ter_toString.ml ms_parser.ml ms_scanner.ml ter_exception.ml ter_util.ml ter_iterateurs.ml ter_identite.ml ter_identite_p.ml ter_arith_to_call.ml ter_no_submod.ml ter_chk_spec.ml ter_schemas_latex.ml ter_schemas_dot.ml ter_transfos.ml main.ml
RESULT  = main

all: byte-code
-include OCamlMakefile
