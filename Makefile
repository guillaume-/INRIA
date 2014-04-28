SOURCES = ms_fundamental_interfaces.ml ms_identifier.ml ms_printable_objects.ml ms_idhtbl.ml ter_parser_checks.ml ms_syntax_tree.ml ter_toString.ml ms_parser.ml ms_scanner.ml ter_exception.ml ter_util.ml ter_plouf.ml ter_convert.ml main.ml
RESULT  = main

all: byte-code
-include OCamlMakefile
