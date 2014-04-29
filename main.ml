let main () =
  try
    let lexbuf = Lexing.from_channel stdin in
      Ms_parser.g_specification Ms_scanner.lexer lexbuf
  with End_of_file -> exit 0

let t0 = Ter_parser_checks.chk_spec (main());;

let t1 = Ter_convert.cvrt_spec t0;;

(*
let t2 = Ter_iterateurs.do_transfo t1;;
*)

let t3 = Ter_toString.str_specification t1;;

print_string t3
