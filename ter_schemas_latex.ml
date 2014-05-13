open Ms_syntax_tree
open SyntaxTree
open Ms_identifier
open Ter_exception
open Ter_util
open Ter_iterateurs
open Ter_identite

	type point = {x: int; y: int; nom: string;}
	type boite = {x1: int; y1: int; x2 : int ; y2 : int ; nom: string;}
	type extern = { pointIn : point list ; pointOut : point list ; pointLoc : (point*bool) list}
	type intern = {pointIn : point list ; pointOut : point list ; boite: boite;}
	
	type ref = {res: string; util: intern list; gen: extern list; fathers: (string list) list;}

	module SlParam : tRef with type r = ref = struct
		type r = ref
		let creerRef s =
			let init_fathers =
				let rec build_f = 
					let rec listStr fathers = function
						|[] -> []
						|e::l ->	if(List.length e.header.local_process_list) > 0
									then (listStr (e.header.process_name::fathers) (List.rev e.header.local_process_list))
										@(listStr fathers l)
									else fathers::(listStr fathers l)
					in function
					|[] -> []
					|e::l -> if(List.length e.header.local_process_list) > 0
							 then (listStr [e.header.process_name] (List.rev e.header.local_process_list))@(build_f l)
							 else ([]::(build_f l))
				in build_f (List.rev s.process_list)
			in	{res="\\documentclass{article}\n\\usepackage[utf8]{inputenc}\n\\usepackage[T1]{fontenc}\n\\usepackage[french]{babel}\n\\usepackage{tikz}\n\\usetikzlibrary{calc}\n\n\\begin{document}\n\\begin{center}\n\n"
						; util = []
						; gen = []
						; fathers = init_fathers}
	end

	include Identite(SlParam)

	let tfr_spec struc pl tdl pdl = {
		process_list = pl;
		type_declaration_list = tdl;
		procedure_declaration_list = pdl

	}, {
		res = (struc.res ^ "\n\\end{center}\n\\end{document}\n");
		util = []; 
		gen = [] ;
		fathers = [];
	}

	let tfr_process struc ph pb =
		let rec str_fathers = function
			|[] -> ""
			|e::[] -> e
			|e::l -> e^" local de "^(str_fathers l)
		in let str_p =
				ph.process_name
					^(if(
						try(List.length (List.rev (List.hd struc.fathers)) > 0)
						with _ -> false )
					  then " process local de "^(str_fathers (List.hd struc.fathers)) 
					  else "")
					^"\\\\\n\\begin{tikzpicture}[scale=0.5]\n"
(* 					^struc.pro_content *)
					^"\\end{tikzpicture}\n"
		in
	{ body = pb;
	  header = ph;
	}, {
		res = (struc.res ^ str_p);
		util = []; 
		gen = [] ;
		fathers = try List.tl struc.fathers
				with _ -> [];
	}
	
(*	let create_box inl outl name =
		let max_length = max (List.length inl) (List.length outl)
		in let h = max_length * 2 + 1
		in let box = {x1 = ; 
					y1 = ; 
					x2 = ; 
					y2 = ; 
					nom = name;}*)

(*
	let tfr_sig_exp struc = function
		| EnumVariantAtom(i)
		| IntegerConstant(i)
		| SignalAtom(i) ->
			
		| WhenAtom(i)
		| WhenNotAtom(i) ->

		
		| NotAtom(i) ->

		| FunctionCall(i,el) ->

		| InAtom (e, s) ->

		| ClockPlus (e1, e2)
		| ClockMinus (e1, e2)
		| ClockTimes(e1, e2)
		| Delay (e1, e2)
		| EqualityAtom (e1, e2)
		| Default (e1, e2)
		| When (e1, e2)
		| AndExp (e1, e2)
		| OrExp (e1, e2)
		| Plus (e1, e2)
		| Minus (e1, e2)
		| Times (e1, e2) -> 
*)

(*
	val tfr_proced_decla:  t -> Identifier.t -> Identifier.t list -> Identifier.t -> procedure_declaration * t
	val tfr_process: t -> process_header -> process_body -> process * t
	val tfr_proc_hd: t -> Identifier.t -> signal_declarations -> process list -> process_header * t
	val tfr_sig_declas: t -> signal_declaration list -> signal_declaration list -> signal_declaration list -> signal_declarations * t
	val tfr_proc_bd: t -> assignment list -> sconstraint list -> instantiation list -> process_body * t
	val tfr_inst: t -> Identifier.t -> Identifier.t list -> signal_expression list -> instantiation * t
	val tfr_sconstr: t -> sconstraint_kind -> Identifier.t -> Identifier.t -> sconstraint * t
	val tfr_sconstr_k: t -> sconstraint_kind -> sconstraint_kind * t
	val tfr_assign: t -> Identifier.t -> signal_expression -> assignment * t
	val tfr_sig_exp: t -> signal_expression -> signal_expression * t
	val tfr_sig_decla: t -> Identifier.t -> Identifier.t -> direction -> signal_declaration * t
	val tfr_direc: t -> direction -> direction * t
	val tfr_typed_var_set: t -> Identifier.t -> IdentifierSet.t -> typed_variant_set * t
	val tfr_identifier: t -> Identifier.t -> Identifier.t * t
	val tfr_identifier_set:  t -> IdentifierSet.t -> IdentifierSet.t * t
*)
