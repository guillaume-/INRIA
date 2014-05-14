open Ms_syntax_tree
open SyntaxTree
open Ms_identifier
open Ter_exception
open Ter_util
open Ter_iterateurs
open Ter_identite

	type variable = {vname: string; vpos: float}
	type out_point= {ox: float; oy: float; oname: string;}
	type in_point = {ix: float; iy: float; iname: string;}
	type b = {	inL: in_point list;
				(*	outL :
					Si boite != Empty, out_point est une entrée de la boite
					tel que dans boite.inL il existe in_point.iname = out_point.oname
				*)
				outL: (out_point*boite) list;
				nom: string;
				taille: (float*float);
	}
	and boite = |Empty |B of b |Unique of variable
	type ref = {	res: string;
					fathers: (string list) list;
					tmp_expr: (signal_expression*boite)list;
					instances: boite list;
					assigns: boite list;
					v_in: variable list;
					v_out: variable list;
					v_new: variable list;
				}

	module SlParam : tRef with type r = ref = struct
		type r = ref
		let creerRef s =
			let init_fathers =
				let rec build_f fathers = function
					|[] -> []
					|e::l -> if(List.length e.header.local_process_list) > 0
							 then	(build_f (e.header.process_name::fathers) (List.rev e.header.local_process_list))
									@[fathers]
									@(build_f fathers l)
							 else (fathers::(build_f fathers l))
				in build_f [] (List.rev s.process_list)
			in	{res="\\documentclass{article}\n"
					^"\\usepackage[utf8]{inputenc}\n"
					^"\\usepackage[T1]{fontenc}\n"
					^"\\usepackage[french]{babel}\n"
					^"\\usepackage{tikz}\n"
					^"\\usetikzlibrary{calc}\n\n"
					^"\\begin{document}\n"
					^"\\begin{center}\n\n";
				fathers=init_fathers; 
				tmp_expr=[];
				instances=[];
				assigns=[];
				v_in=[];
				v_out=[];
				v_new=[];}
	end

	include Identite(SlParam)

	let tfr_spec struc pl tdl pdl = {
		process_list = pl;
		type_declaration_list = tdl;
		procedure_declaration_list = pdl
	}, {
		res = (struc.res ^ "\n\\end{center}\n\\end{document}\n");
		fathers = [];
		tmp_expr = []; instances = []; assigns = [];
		v_in=[]; v_out=[]; v_new=[];
	}

	let tfr_process struc ph pb =
		let calc_str struc = ""
		in let rec str_fathers = function
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
  					^calc_str struc
					^"\\end{tikzpicture}\n\\\\"
		in
	{ body = pb;
	  header = ph;
	}, {
		res = (struc.res ^ str_p);
		fathers = (try List.tl struc.fathers with _ -> []);
		tmp_expr = []; instances = []; assigns = [];
		v_in=[]; v_out=[]; v_new=[]
	}

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

let tfr_sig_declas struc ins outs locs =
	let fmax = if(List.length ins)>(List.length outs)
			  then float_of_int (List.length ins)
			  else float_of_int (List.length outs)
	in let rec ininit pos = function
		|[] -> []
		|e::l -> {vname=e.signal_name; vpos=pos}::(ininit (pos -. 1.) l)
	in let rec outinit pos = function
		|[] -> []
		|e::l -> {vname=e.signal_name; vpos=pos}::(outinit (pos -. 1.) l)
	in {
	input_signal_list = ins;
	output_signal_list = outs;
	local_signal_list = locs;
}, {res = struc.res;
	fathers = struc.fathers;
	tmp_expr=[];
	instances=[];
	assigns=[];
	v_in = ininit (fmax -. 0.5) ins;
	v_out = outinit (fmax -. 0.5) outs;
	v_new=[];
}

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
