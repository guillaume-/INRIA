{
(* Copyright 2013 Dumitru Potop Butucaru ( email: dumitru.potop_butucaru@inria.fr ).

   This program is free software: you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation, either version 3 of the
   License, or (at your option) any later version.
   
   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
   
   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>
*)
open Ms_syntax_tree ;;
open Ms_parser ;;

let scanner_debug_mode = true ;;
let scanner_debug_print text =
  if scanner_debug_mode 
  then (Printf.printf "Scanner debug: %s\n" text ; flush stdout)
  else ()
;;


let keyword_list =
  [("process", Lprocess);
   ("procedure", Lprocedure);
   ("enum", Lenum);
   ("type", Ltype);
   ("in", Lin);
   ("out", Lout);
   ("local", Llocal);
   ("when", Lwhen);
   ("default", Ldefault);
   ("call", Lcall);
   ("end", Lend);
   ("where", Lwhere);
   ("submodule", Lsubmodule);
   ("constant", Lconstant);
   ("not", Lnot);
   ("and", Land);
   ("or", Lor);
 ] ;;

let rec is_keyword str lst =
  if lst = [] then false
  else if str=(fst (List.hd lst)) then true 
  else is_keyword str (List.tl lst) ;;

let rec get_keyword_code str lst =
  if str=(fst (List.hd lst)) then (snd (List.hd lst))
  else get_keyword_code str (List.tl lst) ;;

let rec get_keyword_name id lst =
  if lst = [] then failwith "Ms_scanner::get_keyword_name - unexpected id"
  else if id=(snd (List.hd lst)) then (fst (List.hd lst))
  else get_keyword_name id (List.tl lst) ;;

}

rule lexer = parse
    [' ' '\n' '\t' '\r']  { lexer lexbuf }
|		['0'-'9']+ 
		{ 
			(*let symb_start = Lexing.lexeme_start lexbuf in scanner_debug_print("Scanner:Constante:"^(int_of_string symb_start)) ; *)
			LINT (int_of_string(Lexing.lexeme lexbuf)) }
|   '%'['\n'-'\r' ' '-'$' '&'-'~']*'%' { lexer lexbuf }
|   eof { scanner_debug_print "Scanner:Eof" ; Leof }
|   ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '_' '0'-'9']* 
    {
     
     let str= Lexing.lexeme lexbuf in 
     if is_keyword str keyword_list then 
       (
	scanner_debug_print ("Scanner:Keyword:"^str) ;
	get_keyword_code str keyword_list
       )
     else 
       (
	scanner_debug_print ("Scanner:Identifier:"^str) ;
	Lidentifier str
       )
   }
|   "$1 init" {  scanner_debug_print "Scanner:Ldelay" ; Ldelay }
|   "^+"  {  scanner_debug_print "Scanner:Lclockplus" ; Lclockplus }
|   "^-"  {  scanner_debug_print "Scanner:Lclockminus" ; Lclockminus }
|   "^*"  {  scanner_debug_print "Scanner:Lclocktimes" ; Lclocktimes }
|   '(' {  scanner_debug_print "Scanner:Lopen" ; Lopen }
|   ')' {  scanner_debug_print "Scanner:Lclose" ; Lclose }
|   '[' {  scanner_debug_print "Scanner:Lsqopen" ; Lsqopen }
|   ']' {  scanner_debug_print "Scanner:Lsqclose" ; Lsqclose }
|   ":=" {  scanner_debug_print "Scanner:Lassign" ; Lassign }
|   '^' {  scanner_debug_print "Scanner:Lclock" ; Lclock }
|   '=' {  scanner_debug_print "Scanner:Lequal" ; Lequal }
|   "<=" {  scanner_debug_print "Scanner:Lleq" ; Lleq }
|   '<' {  scanner_debug_print "Scanner:Lless" ; Lless }
|   '+' {  scanner_debug_print "Scanner:Lplus" ; Lplus }
|   '-' {  scanner_debug_print "Scanner:Lminus" ; Lminus }
|   '*' {  scanner_debug_print "Scanner:Ltimes" ; Ltimes }
|   "->" { scanner_debug_print "Scanner:Larrow" ; Larrow }
|   ';' {  scanner_debug_print "Scanner:Lsemicolon" ; Lsemicolon }
|   ':' {  scanner_debug_print "Scanner:Lcolon" ; Lcolon }
|   '?' {  scanner_debug_print "Scanner:Linput" ; Linput }
|   '!' {  scanner_debug_print "Scanner:Loutput" ; Loutput }
|   "where" {  scanner_debug_print "Scanner:Lwhere" ; Lwhere }
|   ',' {  scanner_debug_print "Scanner:Lcomma" ; Lcomma }
|   '|' {  scanner_debug_print "Scanner:Lbar" ; Lbar }
|   '#' {  scanner_debug_print "Scanner:Lexclusive" ; Lexclusive }
{
}

