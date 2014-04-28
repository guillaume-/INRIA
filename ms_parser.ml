type token =
  | Lidentifier of (string)
  | Leof
  | Larrow
  | Lopen
  | Lclose
  | Lsqopen
  | Lsqclose
  | Lassign
  | Lclock
  | Lequal
  | Lleq
  | Lless
  | Lplus
  | Lminus
  | Ltimes
  | Lsemicolon
  | Lcolon
  | Linput
  | Loutput
  | Lcomma
  | Lbar
  | Lclockplus
  | Lclockminus
  | Lclocktimes
  | Ldelay
  | Lnot
  | Lexclusive
  | Lprocess
  | Lprocedure
  | Lwhen
  | Ldefault
  | Lcall
  | Land
  | Lor
  | Lend
  | Llocal
  | Lsubmodule
  | Ltype
  | Lenum
  | Lin
  | Lout
  | Lwhere
  | Lconstant
  | LINT of (int)

open Parsing;;
let _ = parse_error;;
# 2 "ms_parser.mly"
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

  open Ms_identifier ;;
  open Ms_syntax_tree ;;
  open Ms_idhtbl ;;
  open Ter_parser_checks ;;
  open SyntaxTree ;;

  let parser_debug_mode = true ;;
  let parser_debug_print text =
	if parser_debug_mode 
	then (Printf.printf "Parser debug: %s\n" text ; flush stdout)
	else ()
  ;;
  
  let no_signal_declarations =
	(* Constant to use in the following code 
	   (facilitates factoring). 
	*)
	{
	  input_signal_list = [] ;
	  output_signal_list = [] ;
	  local_signal_list = [] ;
	} 
  ;;

  let build_signal_declarations
	  signal_direction
	  typed_signal_list_list
	  =
	let signal_declaration_list =
	  List.map
	(
	  fun (y,z) ->
		let signal_declaration =
		  {
			signal_name = y ;
			signal_type = z ;
			signal_direction = signal_direction ;
		  } 
		in
		let _ = gih_get_type z 
		and _ = gih_set_signal y signal_declaration 
		in
		  signal_declaration
	)
	typed_signal_list_list
	in
	  match signal_direction with
	| Input -> { no_signal_declarations with 
			   input_signal_list = signal_declaration_list }
	| Output -> { no_signal_declarations with 
			output_signal_list = signal_declaration_list }
	| Local -> { no_signal_declarations with 
			   local_signal_list = signal_declaration_list }
  ;;
# 121 "ms_parser.ml"
let yytransl_const = [|
  258 (* Leof *);
  259 (* Larrow *);
  260 (* Lopen *);
  261 (* Lclose *);
  262 (* Lsqopen *);
  263 (* Lsqclose *);
  264 (* Lassign *);
  265 (* Lclock *);
  266 (* Lequal *);
  267 (* Lleq *);
  268 (* Lless *);
  269 (* Lplus *);
  270 (* Lminus *);
  271 (* Ltimes *);
  272 (* Lsemicolon *);
  273 (* Lcolon *);
  274 (* Linput *);
  275 (* Loutput *);
  276 (* Lcomma *);
  277 (* Lbar *);
  278 (* Lclockplus *);
  279 (* Lclockminus *);
  280 (* Lclocktimes *);
  281 (* Ldelay *);
  282 (* Lnot *);
  283 (* Lexclusive *);
  284 (* Lprocess *);
  285 (* Lprocedure *);
  286 (* Lwhen *);
  287 (* Ldefault *);
  288 (* Lcall *);
  289 (* Land *);
  290 (* Lor *);
  291 (* Lend *);
  292 (* Llocal *);
  293 (* Lsubmodule *);
  294 (* Ltype *);
  295 (* Lenum *);
  296 (* Lin *);
  297 (* Lout *);
  298 (* Lwhere *);
  299 (* Lconstant *);
    0|]

let yytransl_block = [|
  257 (* Lidentifier *);
  300 (* LINT *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\001\000\001\000\002\000\002\000\003\000\004\000\
\008\000\007\000\007\000\009\000\009\000\012\000\013\000\013\000\
\014\000\014\000\015\000\010\000\016\000\016\000\017\000\017\000\
\017\000\018\000\021\000\021\000\021\000\021\000\021\000\021\000\
\021\000\021\000\021\000\021\000\021\000\021\000\021\000\021\000\
\021\000\021\000\021\000\021\000\021\000\022\000\022\000\023\000\
\023\000\019\000\024\000\024\000\024\000\024\000\024\000\024\000\
\020\000\006\000\006\000\005\000\005\000\011\000\011\000\025\000\
\025\000\025\000\000\000"

let yylen = "\002\000\
\001\000\002\000\002\000\002\000\003\000\008\000\008\000\003\000\
\002\000\007\000\009\000\001\000\002\000\002\000\001\000\001\000\
\002\000\003\000\002\000\004\000\002\000\003\000\001\000\001\000\
\001\000\003\000\003\000\003\000\003\000\001\000\001\000\003\000\
\003\000\003\000\003\000\003\000\003\000\002\000\005\000\002\000\
\003\000\003\000\003\000\003\000\005\000\000\000\001\000\001\000\
\003\000\003\000\002\000\002\000\002\000\003\000\004\000\002\000\
\008\000\000\000\001\000\001\000\003\000\002\000\003\000\001\000\
\001\000\005\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\001\000\000\000\000\000\000\000\067\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\002\000\003\000\
\004\000\000\000\000\000\000\000\000\000\005\000\008\000\000\000\
\000\000\059\000\000\000\000\000\015\000\016\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\013\000\000\000\014\000\
\000\000\061\000\000\000\000\000\000\000\000\000\019\000\000\000\
\000\000\000\000\000\000\000\000\018\000\007\000\006\000\000\000\
\000\000\000\000\000\000\023\000\024\000\025\000\000\000\000\000\
\064\000\011\000\065\000\000\000\000\000\000\000\000\000\000\000\
\020\000\000\000\000\000\009\000\000\000\031\000\000\000\000\000\
\000\000\000\000\030\000\000\000\000\000\052\000\053\000\056\000\
\050\000\000\000\022\000\000\000\063\000\000\000\040\000\038\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\044\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\055\000\000\000\066\000\000\000\000\000\000\000\047\000\000\000\
\039\000\000\000\045\000\000\000\049\000\057\000"

let yydgoto = "\002\000\
\007\000\008\000\009\000\010\000\026\000\027\000\011\000\065\000\
\031\000\046\000\066\000\032\000\033\000\040\000\041\000\058\000\
\059\000\060\000\061\000\062\000\133\000\134\000\135\000\071\000\
\068\000"

let yysindex = "\023\000\
\006\255\000\000\000\000\025\255\032\255\044\255\000\000\006\255\
\006\255\006\255\031\255\077\255\038\255\250\254\000\000\000\000\
\000\000\096\255\117\255\127\255\090\255\000\000\000\000\045\255\
\110\255\000\000\126\255\129\255\000\000\000\000\135\255\045\255\
\138\255\127\255\147\255\127\255\137\255\000\000\127\255\000\000\
\136\255\000\000\160\255\146\255\142\255\124\255\000\000\138\255\
\153\255\156\255\000\255\004\255\000\000\000\000\000\000\066\255\
\172\255\169\255\158\255\000\000\000\000\000\000\179\255\148\255\
\000\000\000\000\000\000\165\255\255\254\003\255\181\255\180\255\
\000\000\000\255\184\255\000\000\004\255\000\000\255\254\185\255\
\015\255\186\255\000\000\134\255\159\255\000\000\000\000\000\000\
\000\000\127\255\000\000\178\255\000\000\055\255\000\000\000\000\
\164\255\187\255\255\254\255\254\255\254\255\254\255\254\255\254\
\255\254\255\254\255\254\255\254\255\254\255\254\166\255\188\255\
\193\255\000\000\194\255\255\254\007\255\134\255\134\255\134\255\
\007\255\007\255\007\255\007\255\007\255\007\255\058\255\058\255\
\000\000\192\255\000\000\195\255\112\255\196\255\000\000\255\254\
\000\000\255\254\000\000\197\255\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\198\255\000\000\000\000\000\000\000\000\
\001\255\000\000\000\000\000\000\000\000\000\000\000\000\199\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\162\255\000\000\092\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\200\255\000\000\000\000\163\255\000\000\000\000\000\000\
\000\000\000\000\000\000\189\255\207\255\000\000\000\000\000\000\
\000\000\198\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\208\255\000\000\
\000\000\000\000\000\000\201\255\018\255\041\255\062\255\079\255\
\085\255\099\255\133\255\150\255\155\255\157\255\071\255\093\255\
\000\000\000\000\000\000\000\000\202\255\000\000\000\000\201\255\
\000\000\000\000\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\099\000\000\000\000\000\000\000\229\255\109\000\206\255\000\000\
\179\000\000\000\135\000\000\000\000\000\165\000\215\255\140\000\
\000\000\000\000\000\000\000\000\205\255\079\000\078\000\000\000\
\000\000"

let yytablesize = 216
let yytable = "\078\000\
\056\000\064\000\079\000\021\000\039\000\060\000\042\000\003\000\
\044\000\022\000\067\000\047\000\085\000\086\000\087\000\096\000\
\060\000\084\000\097\000\100\000\101\000\102\000\036\000\001\000\
\080\000\012\000\064\000\094\000\081\000\088\000\082\000\004\000\
\013\000\004\000\005\000\067\000\057\000\036\000\036\000\109\000\
\110\000\020\000\083\000\006\000\014\000\027\000\063\000\117\000\
\118\000\119\000\120\000\121\000\122\000\123\000\124\000\125\000\
\126\000\127\000\128\000\114\000\027\000\027\000\029\000\030\000\
\099\000\018\000\028\000\100\000\101\000\102\000\100\000\101\000\
\102\000\069\000\070\000\041\000\103\000\104\000\105\000\106\000\
\041\000\028\000\028\000\029\000\107\000\108\000\019\000\109\000\
\110\000\033\000\041\000\041\000\041\000\041\000\041\000\041\000\
\017\000\042\000\029\000\029\000\041\000\041\000\042\000\034\000\
\033\000\033\000\015\000\016\000\017\000\017\000\017\000\023\000\
\042\000\042\000\042\000\042\000\042\000\042\000\034\000\034\000\
\024\000\099\000\042\000\042\000\100\000\101\000\102\000\025\000\
\028\000\034\000\035\000\138\000\036\000\103\000\104\000\105\000\
\106\000\035\000\039\000\037\000\045\000\107\000\108\000\099\000\
\109\000\110\000\100\000\101\000\102\000\043\000\050\000\048\000\
\035\000\035\000\032\000\103\000\104\000\105\000\106\000\037\000\
\049\000\043\000\051\000\107\000\108\000\052\000\109\000\110\000\
\054\000\032\000\032\000\055\000\072\000\073\000\037\000\037\000\
\043\000\043\000\074\000\075\000\077\000\089\000\076\000\090\000\
\092\000\095\000\098\000\113\000\111\000\115\000\116\000\129\000\
\130\000\131\000\132\000\136\000\010\000\062\000\112\000\137\000\
\139\000\142\000\058\000\012\000\021\000\046\000\048\000\051\000\
\054\000\026\000\038\000\093\000\053\000\091\000\140\000\141\000"

let yycheck = "\001\001\
\001\001\052\000\004\001\010\001\001\001\005\001\034\000\002\001\
\036\000\016\001\052\000\039\000\010\001\011\001\012\001\001\001\
\016\001\069\000\004\001\013\001\014\001\015\001\005\001\001\000\
\026\001\001\001\077\000\079\000\030\001\027\001\032\001\028\001\
\001\001\028\001\029\001\077\000\037\001\020\001\021\001\033\001\
\034\001\004\001\044\001\038\001\001\001\005\001\043\001\099\000\
\100\000\101\000\102\000\103\000\104\000\105\000\106\000\107\000\
\108\000\109\000\110\000\005\001\020\001\021\001\018\001\019\001\
\010\001\035\001\005\001\013\001\014\001\015\001\013\001\014\001\
\015\001\008\001\009\001\005\001\022\001\023\001\024\001\025\001\
\010\001\020\001\021\001\005\001\030\001\031\001\010\001\033\001\
\034\001\005\001\020\001\021\001\022\001\023\001\024\001\025\001\
\005\001\005\001\020\001\021\001\030\001\031\001\010\001\005\001\
\020\001\021\001\008\000\009\000\010\000\018\001\019\001\016\001\
\020\001\021\001\022\001\023\001\024\001\025\001\020\001\021\001\
\004\001\010\001\030\001\031\001\013\001\014\001\015\001\001\001\
\039\001\020\001\005\001\020\001\004\001\022\001\023\001\024\001\
\025\001\005\001\001\001\005\001\004\001\030\001\031\001\010\001\
\033\001\034\001\013\001\014\001\015\001\003\001\005\001\016\001\
\020\001\021\001\005\001\022\001\023\001\024\001\025\001\005\001\
\001\001\005\001\021\001\030\001\031\001\042\001\033\001\034\001\
\016\001\020\001\021\001\016\001\001\001\005\001\020\001\021\001\
\020\001\021\001\021\001\001\001\016\001\001\001\035\001\004\001\
\001\001\001\001\001\001\010\001\030\001\026\001\004\001\026\001\
\005\001\001\001\001\001\004\001\035\001\035\001\090\000\005\001\
\005\001\005\001\005\001\005\001\005\001\005\001\005\001\001\001\
\001\001\021\001\032\000\077\000\048\000\074\000\136\000\138\000"

let yynames_const = "\
  Leof\000\
  Larrow\000\
  Lopen\000\
  Lclose\000\
  Lsqopen\000\
  Lsqclose\000\
  Lassign\000\
  Lclock\000\
  Lequal\000\
  Lleq\000\
  Lless\000\
  Lplus\000\
  Lminus\000\
  Ltimes\000\
  Lsemicolon\000\
  Lcolon\000\
  Linput\000\
  Loutput\000\
  Lcomma\000\
  Lbar\000\
  Lclockplus\000\
  Lclockminus\000\
  Lclocktimes\000\
  Ldelay\000\
  Lnot\000\
  Lexclusive\000\
  Lprocess\000\
  Lprocedure\000\
  Lwhen\000\
  Ldefault\000\
  Lcall\000\
  Land\000\
  Lor\000\
  Lend\000\
  Llocal\000\
  Lsubmodule\000\
  Ltype\000\
  Lenum\000\
  Lin\000\
  Lout\000\
  Lwhere\000\
  Lconstant\000\
  "

let yynames_block = "\
  Lidentifier\000\
  LINT\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    Obj.repr(
# 103 "ms_parser.mly"
  (
	{
	 process_list = [] ;
	 type_declaration_list = [] ;
	 procedure_declaration_list = [] ;
	}
  )
# 387 "ms_parser.ml"
               : Ms_syntax_tree.SyntaxTree.specification))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'g_type_definition) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ms_syntax_tree.SyntaxTree.specification) in
    Obj.repr(
# 111 "ms_parser.mly"
  ( 
	parser_debug_print "Parser:g_specification: complete type definition" ; 
	{ _2 with 
	type_declaration_list = _1::(_2.type_declaration_list)
	}
  )
# 400 "ms_parser.ml"
               : Ms_syntax_tree.SyntaxTree.specification))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'g_procedure_definition) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ms_syntax_tree.SyntaxTree.specification) in
    Obj.repr(
# 118 "ms_parser.mly"
  ( 
	parser_debug_print "Parser:g_specification: complete procedure definition" ; 
	{ _2 with 
	procedure_declaration_list = _1::(_2.procedure_declaration_list)
	}
  )
# 413 "ms_parser.ml"
               : Ms_syntax_tree.SyntaxTree.specification))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'g_process) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ms_syntax_tree.SyntaxTree.specification) in
    Obj.repr(
# 125 "ms_parser.mly"
  ( 
	parser_debug_print "Parser:g_specification: complete process definition"; 
	{
		_2 with process_list = (gih_chk_process _1)::(_2.process_list)
	}
  )
# 426 "ms_parser.ml"
               : Ms_syntax_tree.SyntaxTree.specification))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 135 "ms_parser.mly"
 (
	let type_declaration = {
		tv_type_name = Identifier.of_string _2 ;
		variant_set = IdentifierSet.empty ;
	} in (
		gih_set_type type_declaration.tv_type_name type_declaration ;
		type_declaration
	)
  )
# 441 "ms_parser.ml"
               : 'g_type_definition))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'g_nv_identifier_list) in
    Obj.repr(
# 145 "ms_parser.mly"
  (
	let type_declaration =
	{
		tv_type_name = Identifier.of_string _2 ;
		variant_set = IdentifierSet.from_list _6 ;
	} in
	gih_set_type type_declaration.tv_type_name type_declaration;
	List.iter ( fun enum_variant -> gih_set_enum_variant enum_variant type_declaration) _6;
	type_declaration
  )
# 458 "ms_parser.ml"
               : 'g_type_definition))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'g_identifier_list) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 161 "ms_parser.mly"
  (
	let procedure_definition =
	  {
			procedure_name = Identifier.of_string _2 ;
			procedure_input_list = _4 ;
			procedure_output = Identifier.of_string _7 ;
	  }
	in
	  (* Check that the types of the input and output are already defined. *)
	  let _ =  gih_get_type (Identifier.of_string _7)
	  and _ =
	List.map
	  ( fun type_name -> gih_get_type type_name )
	  _4 
	  in
	(* Add the new procedure name *)
	gih_set_procedure (Identifier.of_string _2) procedure_definition ;
	(* Produce the result *)
	procedure_definition
  )
# 486 "ms_parser.ml"
               : 'g_procedure_definition))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'g_header) in
    Obj.repr(
# 185 "ms_parser.mly"
 ( 
		parser_debug_print "Parser: ProcessV1 completed" ; 
		let process =
		{
			header = (fst _1);
			body = (snd _1);
		}
		in
		gih_set_process process.header.process_name process;
		process
	)
# 503 "ms_parser.ml"
               : 'g_process))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'g_header) in
    Obj.repr(
# 200 "ms_parser.mly"
 ( 
		parser_debug_print "Parser: ProcessV1 completed" ; 
		let process =
		{
			header = (fst _1);
			body = (snd _1);
		}
		in
		process
	)
# 519 "ms_parser.ml"
               : 'g_local_process))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'g_interface_signal_declaration_list) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'g_body) in
    Obj.repr(
# 216 "ms_parser.mly"
  ( 
	parser_debug_print "Parser: Header (TER no where's rule) completed" ;
	(
		{
			process_name = Identifier.of_string _2 ;
			signal_declarations = _5 ;
			local_process_list = [] ;
		},
		_7
	)
  )
# 538 "ms_parser.ml"
               : 'g_header))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : 'g_interface_signal_declaration_list) in
    let _7 = (Parsing.peek_val __caml_parser_env 2 : 'g_body) in
    let _9 = (Parsing.peek_val __caml_parser_env 0 : 'g_locals) in
    Obj.repr(
# 230 "ms_parser.mly"
  ( 
	parser_debug_print "Parser: Header (TER where's rule) completed" ;
	match _9 with
	(signal_declarations,local_processes,constant_assignments) ->
	(
		{
			process_name = Identifier.of_string _2 ;
			signal_declarations = {
				_5 with local_signal_list = signal_declarations.local_signal_list
			};
			local_process_list = local_processes ;
		},
		{
			_7 with assignment_list = _7.assignment_list@(constant_assignments);
		}
	)
  )
# 564 "ms_parser.ml"
               : 'g_header))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'g_interface_signal_declaration) in
    Obj.repr(
# 250 "ms_parser.mly"
                                 ( _1 )
# 571 "ms_parser.ml"
               : 'g_interface_signal_declaration_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'g_interface_signal_declaration) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'g_interface_signal_declaration_list) in
    Obj.repr(
# 252 "ms_parser.mly"
 ( 
	  {
		input_signal_list = _1.input_signal_list@_2.input_signal_list ;
		output_signal_list = _1.output_signal_list@_2.output_signal_list ;
		local_signal_list = _1.local_signal_list@_2.local_signal_list ;
	  }
	)
# 585 "ms_parser.ml"
               : 'g_interface_signal_declaration_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'g_signal_direction) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'g_typed_signal_list_list) in
    Obj.repr(
# 263 "ms_parser.mly"
  (  build_signal_declarations _1 _2 )
# 593 "ms_parser.ml"
               : 'g_interface_signal_declaration))
; (fun __caml_parser_env ->
    Obj.repr(
# 267 "ms_parser.mly"
        ( Input )
# 599 "ms_parser.ml"
               : 'g_signal_direction))
; (fun __caml_parser_env ->
    Obj.repr(
# 268 "ms_parser.mly"
           ( Output )
# 605 "ms_parser.ml"
               : 'g_signal_direction))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'g_typed_signal_list) in
    Obj.repr(
# 272 "ms_parser.mly"
                                ( _1 )
# 612 "ms_parser.ml"
               : 'g_typed_signal_list_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'g_typed_signal_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'g_typed_signal_list_list) in
    Obj.repr(
# 273 "ms_parser.mly"
                                                           ( _1@_3 )
# 620 "ms_parser.ml"
               : 'g_typed_signal_list_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'g_nv_identifier_list) in
    Obj.repr(
# 278 "ms_parser.mly"
 (
		let type_id = Identifier.of_string _1
		in
		List.map ( fun signal_id -> (signal_id,type_id) ) _2
	)
# 632 "ms_parser.ml"
               : 'g_typed_signal_list))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'g_statement_list) in
    Obj.repr(
# 287 "ms_parser.mly"
 ( 
		parser_debug_print "Parser: Body completed" ; 
		_3 
	)
# 642 "ms_parser.ml"
               : 'g_body))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'g_statement) in
    Obj.repr(
# 294 "ms_parser.mly"
                  ( _1 )
# 649 "ms_parser.ml"
               : 'g_statement_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'g_statement) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'g_statement_list) in
    Obj.repr(
# 296 "ms_parser.mly"
 ( 
	  {
	assignment_list = 
	  _1.assignment_list@_3.assignment_list ;
	constraint_list = 
	  _1.constraint_list@_3.constraint_list ;
	instantiation_list = 
	  _1.instantiation_list@_3.instantiation_list ;
	  }
	)
# 666 "ms_parser.ml"
               : 'g_statement_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'g_assignment) in
    Obj.repr(
# 310 "ms_parser.mly"
 (
		parser_debug_print "Parser: Assignment completed" ; 
		{
		assignment_list = [_1] ;
		constraint_list = [] ;
		instantiation_list = [] ; 
		}
	)
# 680 "ms_parser.ml"
               : 'g_statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'g_constraint) in
    Obj.repr(
# 319 "ms_parser.mly"
  ( 
	parser_debug_print "Parser: Constraint completed" ;
	{
	  assignment_list = [] ;
	  constraint_list = [_1] ;
	  instantiation_list = [] ; 
	}
  )
# 694 "ms_parser.ml"
               : 'g_statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'g_instantiation) in
    Obj.repr(
# 328 "ms_parser.mly"
  ( 
	parser_debug_print "Parser: Instantiation completed" ;
	{
	  assignment_list = [] ;
	  constraint_list = [] ;
	  instantiation_list = [_1] ; 
	}
  )
# 708 "ms_parser.ml"
               : 'g_statement))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'g_signal_expression) in
    Obj.repr(
# 340 "ms_parser.mly"
 ( 
		{
			assigned_signal_name = Identifier.of_string _1 ;
			signal_expression = _3 ;
		}
	)
# 721 "ms_parser.ml"
               : 'g_assignment))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'g_signal_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'g_signal_expression) in
    Obj.repr(
# 349 "ms_parser.mly"
                                                 ( Plus(_1,_3) )
# 729 "ms_parser.ml"
               : 'g_signal_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'g_signal_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'g_signal_expression) in
    Obj.repr(
# 350 "ms_parser.mly"
                                                  ( Minus(_1,_3) )
# 737 "ms_parser.ml"
               : 'g_signal_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'g_signal_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'g_signal_expression) in
    Obj.repr(
# 351 "ms_parser.mly"
                                                  ( Times(_1,_3) )
# 745 "ms_parser.ml"
               : 'g_signal_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 352 "ms_parser.mly"
         ( IntegerConstant _1 )
# 752 "ms_parser.ml"
               : 'g_signal_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 353 "ms_parser.mly"
               (
		let target = gih_get_target (Identifier.of_string _1) in
			match target with 
				IH_enum_variant(_) ->
					EnumVariantAtom(Identifier.of_string _1)
				| IH_signal(_) ->
					SignalAtom(Identifier.of_string _1)
				| _ ->
					SignalAtom(Identifier.of_string _1)
	)
# 768 "ms_parser.ml"
               : 'g_signal_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'g_signal_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'g_signal_expression) in
    Obj.repr(
# 363 "ms_parser.mly"
                                                  (Delay(_1,_3))
# 776 "ms_parser.ml"
               : 'g_signal_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'g_signal_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'g_signal_expression) in
    Obj.repr(
# 364 "ms_parser.mly"
                                                      (ClockPlus(_1,_3))
# 784 "ms_parser.ml"
               : 'g_signal_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'g_signal_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'g_signal_expression) in
    Obj.repr(
# 365 "ms_parser.mly"
                                                       (ClockMinus(_1,_3))
# 792 "ms_parser.ml"
               : 'g_signal_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'g_signal_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'g_signal_expression) in
    Obj.repr(
# 366 "ms_parser.mly"
                                                       (ClockTimes(_1,_3))
# 800 "ms_parser.ml"
               : 'g_signal_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'g_signal_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'g_signal_expression) in
    Obj.repr(
# 367 "ms_parser.mly"
                                                  ( EqualityAtom(_1,_3) )
# 808 "ms_parser.ml"
               : 'g_signal_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'g_signal_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'g_signal_expression) in
    Obj.repr(
# 369 "ms_parser.mly"
                                                 ( When(_1,_3) )
# 816 "ms_parser.ml"
               : 'g_signal_expression))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 370 "ms_parser.mly"
                     ( WhenAtom(Identifier.of_string _2) )
# 823 "ms_parser.ml"
               : 'g_signal_expression))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 371 "ms_parser.mly"
                                       ( 
		WhenNotAtom(Identifier.of_string _4) 
	)
# 832 "ms_parser.ml"
               : 'g_signal_expression))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 374 "ms_parser.mly"
                    (
		NotAtom(Identifier.of_string _2) 
	)
# 841 "ms_parser.ml"
               : 'g_signal_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'g_signal_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'g_signal_expression) in
    Obj.repr(
# 377 "ms_parser.mly"
                                                ( AndExp(_1,_3) )
# 849 "ms_parser.ml"
               : 'g_signal_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'g_signal_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'g_signal_expression) in
    Obj.repr(
# 378 "ms_parser.mly"
                                               ( OrExp(_1,_3) )
# 857 "ms_parser.ml"
               : 'g_signal_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'g_signal_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'g_signal_expression) in
    Obj.repr(
# 379 "ms_parser.mly"
                                                    ( Default(_1,_3) )
# 865 "ms_parser.ml"
               : 'g_signal_expression))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'g_signal_expression) in
    Obj.repr(
# 380 "ms_parser.mly"
                                    ( _2 )
# 872 "ms_parser.ml"
               : 'g_signal_expression))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'g_signal_expression_list) in
    Obj.repr(
# 381 "ms_parser.mly"
                                                           ( 
		(*	First, I do some sanity checks.
			Here I should check that the types produced by the 
			expressions in the g_signal_expression_list correspond
			to the types specified in the definition of the 
			procedure. 
			I'm actually doing smth simpler, which is to check
			that the number of parameters correspond. :) 
		*)
		let _ = 
			let procedure = gih_get_procedure (Identifier.of_string _2) in
			if ((List.length procedure.procedure_input_list) = (List.length _4))
			then ()
			else 
				failwith ("Ms_parser:g_signal_expression: "
						^ "The numbers of formal and actual parameters are not equal.");
		in
		(* The actual construction of the result. *)
		FunctionCall((Identifier.of_string _2),_4) 
	)
# 899 "ms_parser.ml"
               : 'g_signal_expression))
; (fun __caml_parser_env ->
    Obj.repr(
# 424 "ms_parser.mly"
 ([])
# 905 "ms_parser.ml"
               : 'g_signal_expression_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'g_signal_expression_nv_list) in
    Obj.repr(
# 425 "ms_parser.mly"
                                ( _1 )
# 912 "ms_parser.ml"
               : 'g_signal_expression_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'g_signal_expression) in
    Obj.repr(
# 429 "ms_parser.mly"
                      ( [_1] )
# 919 "ms_parser.ml"
               : 'g_signal_expression_nv_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'g_signal_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'g_signal_expression_nv_list) in
    Obj.repr(
# 430 "ms_parser.mly"
                                                         ( _1::_3 )
# 927 "ms_parser.ml"
               : 'g_signal_expression_nv_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'g_constraint_kind) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 435 "ms_parser.mly"
  ( 
	{
	  constraint_kind = _2 ;
	  left_signal_name = Identifier.of_string _1 ; 
	  right_signal_name = Identifier.of_string _3 ;
	} 
  )
# 942 "ms_parser.ml"
               : 'g_constraint))
; (fun __caml_parser_env ->
    Obj.repr(
# 445 "ms_parser.mly"
                (ClockEquality)
# 948 "ms_parser.ml"
               : 'g_constraint_kind))
; (fun __caml_parser_env ->
    Obj.repr(
# 446 "ms_parser.mly"
              (ClockLeq)
# 954 "ms_parser.ml"
               : 'g_constraint_kind))
; (fun __caml_parser_env ->
    Obj.repr(
# 447 "ms_parser.mly"
               (ClockLess)
# 960 "ms_parser.ml"
               : 'g_constraint_kind))
; (fun __caml_parser_env ->
    Obj.repr(
# 448 "ms_parser.mly"
                      (ClockWhen)
# 966 "ms_parser.ml"
               : 'g_constraint_kind))
; (fun __caml_parser_env ->
    Obj.repr(
# 449 "ms_parser.mly"
                           (ClockWhenNot)
# 972 "ms_parser.ml"
               : 'g_constraint_kind))
; (fun __caml_parser_env ->
    Obj.repr(
# 450 "ms_parser.mly"
                    (ClockExclusive)
# 978 "ms_parser.ml"
               : 'g_constraint_kind))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'g_identifier_list) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'g_signal_expression_list) in
    Obj.repr(
# 455 "ms_parser.mly"
  ( 
	let instantiation =
	  {
	   instance_process_name = Identifier.of_string _2 ;
	   instance_output_signals = _4 ; 
	   instance_input_expressions = _7 ;
	  }
	in

	(************************************************************************************
	/* 	/!\ This check is reported later because it cann't support local processes
	/*	Check that the input list of the called process indeed corresponds 
	/*	to the input list specified when the process is defined.
	/*
	/*let _ =
	/*	let process = gih_get_process (Identifier.of_string $2) in
	/*if((List.length (process.header.signal_declarations.input_signal_list)) = (List.length $7))
	/*then()
	/*else
	/*	failwith(	"Ms_parser:g_instantiation: "
	/*				^"The numbers of formal and actual parameters are not equal.");
	/*in
	/***********************************************************************************)
	instantiation
  )
# 1011 "ms_parser.ml"
               : 'g_instantiation))
; (fun __caml_parser_env ->
    Obj.repr(
# 483 "ms_parser.mly"
([])
# 1017 "ms_parser.ml"
               : 'g_identifier_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'g_nv_identifier_list) in
    Obj.repr(
# 484 "ms_parser.mly"
                       ( _1 )
# 1024 "ms_parser.ml"
               : 'g_identifier_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 488 "ms_parser.mly"
             ( [Identifier.of_string _1] )
# 1031 "ms_parser.ml"
               : 'g_nv_identifier_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'g_nv_identifier_list) in
    Obj.repr(
# 489 "ms_parser.mly"
                                            ( (Identifier.of_string _1)::_3 )
# 1039 "ms_parser.ml"
               : 'g_nv_identifier_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'g_local) in
    Obj.repr(
# 493 "ms_parser.mly"
                    ( _1 )
# 1046 "ms_parser.ml"
               : 'g_locals))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'g_local) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'g_locals) in
    Obj.repr(
# 495 "ms_parser.mly"
   (
	match (_1,_3) with
		((a,b,c),(d,e,f)) -> 
		(
			{
				input_signal_list = a.input_signal_list@d.input_signal_list ;
				output_signal_list = a.output_signal_list@d.output_signal_list ;
				local_signal_list = a.local_signal_list@d.local_signal_list ;
			},
			(b@e),
			(c@f)
		)
	  )
# 1066 "ms_parser.ml"
               : 'g_locals))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'g_local_process) in
    Obj.repr(
# 512 "ms_parser.mly"
(
	(
		no_signal_declarations,
		[_1],
		[]
	)
)
# 1079 "ms_parser.ml"
               : 'g_local))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'g_typed_signal_list) in
    Obj.repr(
# 520 "ms_parser.mly"
(
	(
		( build_signal_declarations Local _1 ),
		[],
		[]
	)
)
# 1092 "ms_parser.ml"
               : 'g_local))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 532 "ms_parser.mly"
(
	(
		(build_signal_declarations 
			Local 
			[(Identifier.of_string _3,Identifier.of_string _2)]
		),
		[],
		[{
			assigned_signal_name = Identifier.of_string _3 ;
			signal_expression = EnumVariantAtom (Identifier.of_string _5) ;
		}]
	)
)
# 1113 "ms_parser.ml"
               : 'g_local))
(* Entry g_specification *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let g_specification (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Ms_syntax_tree.SyntaxTree.specification)
;;
