open Ter_transfos

let main () =
  try
    let lexbuf = Lexing.from_channel stdin in
      Ms_parser.g_specification Ms_scanner.lexer lexbuf
  with End_of_file -> exit 0

let spec_0 = print_string "----------------------- Lecture ficher -----------------------\n";
			let s = main() 
			in print_string "------------------ Verification syntaxique -------------------\n";
				check (s);;



(*let spec_1 = print_string "-- Remplacement symboles arithmétiques -> appels procedures --\n";
			addCall spec_0;;*)
			
let spec_2 = print_string "----------------- Suppression des submodules -----------------\n";
			noSub spec_0;;
			
(*let spec_3 = check spec_2;;*)
			
let str = Ter_toString.str_specification spec_2;;
print_string str;
