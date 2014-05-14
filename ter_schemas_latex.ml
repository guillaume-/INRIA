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
	type b = { inL: (in_point*boite) list;
				(*	outL :
					Si boite != Empty, out_point est une entrée de la boite
					tel que dans boite.inL il existe in_point.iname = out_point.oname
				*)
				outL: (out_point*boite) list;
				nom: string;
				taille: float;
	}
	and boite = |Empty |B of b(* |Unique of variable*)
	let size = function
		|Empty -> 0.
		|B(b) -> b.taille
	
	let name = function 
		|Empty -> "vide"
		|B(b) -> b.nom
	
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
		in { body = pb;
			header = ph;}, 
			{res = (struc.res ^ str_p);
			fathers = (try List.tl struc.fathers with _ -> []);
			tmp_expr = []; instances = []; assigns = [];
			v_in=[]; v_out=[]; v_new=[]}

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
		in {input_signal_list = ins;
			output_signal_list = outs;
			local_signal_list = locs;}, 
			{res = struc.res;
			fathers = struc.fathers;
			tmp_expr=[];
			instances=[];
			assigns=[];
			v_in = ininit (fmax -. 0.5) ins;
			v_out = outinit (fmax -. 0.5) outs;
			v_new=[];}

	let tfr_assign struc asn ae = 
		let tmp_expr,b = List.hd struc.tmp_expr
		in let n,taille_b = name b, size b
			in let n_assign = B ({inL = [{ix = taille_b -. 1.; iy = 0.; iname = n;},b];
									(* outL existe forcément déjà dans v_out ou v_new et est par conseq déjà positionné quelque part.
									Donc zéro comme position*)
									outL = [{ox = 0.; oy = 0.; oname = asn},Empty];
									nom  = ":=";
									taille = taille_b ;})
				in let n_struc = { res = struc.res;
									fathers = struc.fathers;
									tmp_expr = [];
									instances = struc.instances;
									assigns = n_assign::struc.assigns;
									v_in = struc.v_in;
									v_out = struc.v_out;
									v_new = struc.v_new;} 
					in {assigned_signal_name = asn;signal_expression=ae}, n_struc
	
	let tfr_inst struc ipn ios iie =
		let hauteur = (float (max (List.length ios) (List.length iie))) /. 2.
		and taille_b = List.fold_left (fun r -> fun (e,b) -> let t = size b in if t > r then t else r) 0. struc.tmp_expr
		in let _,outl = List.fold_right (fun e -> fun (h,r) -> 
										(h-.1., ({ox = taille_b +. 2.; oy = h; oname = e},Empty)::r)) 
										ios ((hauteur -. 0.5),[]) 
			and _,inl = List.fold_right (fun (e,b) -> fun (h,r) ->
										(h-.1., ({ix = taille_b +. 1. ; iy = h ; iname = "void" ;},b)::r))
										struc.tmp_expr ((hauteur -. 0.5),[]) 
			in let n_inst = B({inL = inl;
								outL = outl;
								nom  = ipn;
								taille = taille_b +. 2.;})
				in let n_struc = { res = struc.res;
									fathers = struc.fathers;
									tmp_expr = [];
									instances = n_inst::struc.instances;
									assigns = struc.assigns;
									v_in = struc.v_in;
									v_out = struc.v_out;
									v_new = struc.v_new;} 
					in {instance_process_name = ipn ; instance_output_signals = ios ; instance_input_expressions = iie ;},
						n_struc
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
