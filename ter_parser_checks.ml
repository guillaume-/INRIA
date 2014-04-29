open Ms_identifier
open Ms_idhtbl
open Ms_syntax_tree
open SyntaxTree

let rec get_sig_type name = function (*retourne le type d'un signal par recherche de son nom dans une liste de signaux*)
	|[]		-> raise Not_found
	|s::l	-> if(s.signal_name=name)then s.signal_type else (get_sig_type name l)

let rec chk_signals_any_occur = function
	|[]		->	true
	|s::l	->	try(
					let a = get_sig_type s.signal_name l
					in if(a=a)then
						failwith("Multiple define of signal "^s.signal_name^"\n")
					else failwith("a different de a \n")
				)with Not_found -> chk_signals_any_occur l

let chk_signal_declarations s =
	if(chk_signals_any_occur ((s.input_signal_list @ s.output_signal_list)@ s.local_signal_list))
	then s
	else failwith("chk_signal_declarations : TER dead case\n")

let rec chk_process_any_occur name = function
	|[]		->	true
	|p::l	->	if(p.header.process_name = name)
				then false
				else (chk_process_any_occur name l)

let rec chk_local_process_list = function
	|[]		->	[]
	|p::l	->	if(chk_process_any_occur p.header.process_name l)
				then p::(chk_local_process_list l)
				else failwith("Multiple define of local process "^p.header.process_name^"\n")

let chk_header head = {
	process_name = head.process_name; (* name already checked *)
	signal_declarations = chk_signal_declarations head.signal_declarations; (* check that each input/output/local has its name *)
	local_process_list = chk_local_process_list head.local_process_list; (* check that each process has its name *)
}

let chk_left_s name declarations =
	get_sig_type name  (((declarations.input_signal_list)@(declarations.output_signal_list))@(declarations.local_signal_list))

let chk_right_s name declarations =
	get_sig_type name (((declarations.input_signal_list)@(declarations.output_signal_list))@(declarations.local_signal_list))

let rec chk_constraint_list p = function
	|[]		-> []
	|c::l	->	try(let t_ou = chk_left_s c.left_signal_name p.header.signal_declarations
					in 
					try(let t_in = chk_right_s c.right_signal_name p.header.signal_declarations
						in if(t_ou = t_in)
						then c::(chk_constraint_list p l)
						else failwith ("Incompatible types\n")
					)
					with _ -> failwith ("Constraint using as input the undefined signal : "^c.right_signal_name^"\n")
				)
				with Not_found -> failwith ("Constraint using as output the undefined signal : "^c.left_signal_name^"\n")

let rec chk_process_local process_name = function
	|[] -> failwith(process_name^" call but is undefined\n")
	|p::l ->	if(p.header.process_name = process_name)
				then p
				else chk_process_local process_name l

let chk_process_defined process_name local_processes =
	try(
		Hashtbl.find process_table process_name
	)with Not_found -> (chk_process_local process_name local_processes)

let rec chk_list_sig sig_declare = function
	|[] -> []
	|s::l ->	try(
					let a = get_sig_type s
					(sig_declare.input_signal_list
					@sig_declare.output_signal_list
					@sig_declare.local_signal_list)
					in a :: (chk_list_sig sig_declare l)
				)with Not_found ->
					failwith("Signal "^(Identifier.of_string s)^" is not defined\n")

let rec chk_sig sig_declare s =
	try(
		get_sig_type s
		(sig_declare.input_signal_list
		@sig_declare.output_signal_list
		@sig_declare.local_signal_list)
	)with Not_found ->
			failwith("Signal "^(Identifier.of_string s)^" is not defined\n")

let rec chk_exp p = function
	| IntegerConstant(i) ->
		"integer"
	| EnumVariantAtom(e) ->
		chk_var p e
	| SignalAtom(e) ->
		chk_sig p.header.signal_declarations e
	| FunctionCall(f, exp) ->
		chk_procedure p exp f
	| InAtom(e, t) ->
		 if(t.tv_type_name = chk_exp p e)
		 then t.tv_type_name
		 else failwith("InAtom : types do not match")
	| When(e1, e2) ->
		if((chk_exp p e2) = "boolean")
		then (chk_exp p e1)
		else failwith("when hasn't boolean case")
	| AndExp(e1, e2)
	| OrExp(e1, e2) ->
		if(((chk_exp p e1) = (chk_exp p e2))
		&& (chk_exp p e1) = "boolean")
		then "boolean"
		else failwith("Bad type, boolean wanted\n")
	| WhenAtom(e)
	| WhenNotAtom(e)
	| NotAtom(e) ->
		chk_sig p.header.signal_declarations e
	| Plus(e1, e2)
	| Minus(e1, e2)
	| Times(e1, e2) ->
		if(((chk_exp p e1) = (chk_exp p e2))
		&& (chk_exp p e1) = "integer")
		then "integer"
		else failwith("Bad type, integer wanted\n")
	| ClockPlus(e1, e2)
	| ClockMinus(e1, e2)
	| ClockTimes(e1, e2)
	| Delay(e1, e2)
	| Default(e1, e2)
	| EqualityAtom(e1, e2) ->
		if((chk_exp p e1) = (chk_exp p e2))
		then (chk_exp p e1)
		else failwith("Type mismatch\n")
and chk_input_expressions p = function
	|[] -> []
	|exp::l ->	try(let a = chk_exp p exp in
					a::(chk_input_expressions p l)
				)with Not_found -> failwith("chk_input_expressions : TER dead case\n")
and chk_var p e =
	try(
		let a = gih_get_target e in
		match(a)with
			|IH_enum_variant(e) -> e.tv_type_name
			|IH_signal(s) -> s.signal_type
			|_ -> failwith("Enum "^e^" not defined\n")
	)with Not_found -> failwith("Enum "^e^" not defined\n")
and chk_procedure p e f =
	try(
		let a = gih_get_procedure f in
		if(a=a)
		then(	let b= chk_input_expressions p e in
				if(b=b)then
					a.procedure_output
				else failwith("b, b, que de choses différentes")
		)else failwith("a different de a, attention !")
	)with Not_found -> failwith("Procedure "^f^" call but not defined\n")

let chk_arg_numbers p_def inst =
	( (List.length inst.instance_output_signals) = (List.length p_def.header.signal_declarations.output_signal_list))
	&& ( (List.length inst.instance_input_expressions) = (List.length p_def.header.signal_declarations.input_signal_list))

let rec chk_lists l1 l2 = match(l1, l2)with
	|[], [] ->	print_string"\n";
				true
	|e::l, ed::ld ->	print_string ("e1="^e^", e2="^ed^"\n");
						chk_lists l ld
	|[], e::l ->	print_string ("e1 vide, e2="^e^"\n");
					false
	|e::l, [] ->	print_string ("e1="^e^", e2 vide\n");
					false

let chk_each_in_out_type p i p_def si =
	let rec chk_in_types l1 l2 = match(l1, l2)with
		| [], [] -> ()
		| _ , [] -> failwith("Instance "^i.instance_process_name^" hasn't enought input args\n")
		| [], _  -> failwith("Instance "^i.instance_process_name^" has too many input args\n")
		|s::l, ed::ld ->	if( s.signal_type = chk_exp p ed)
							then chk_in_types l ld
							else failwith("Instance "^i.instance_process_name^" has incorrect input types\n")
	in let rec chk_out_types l1 l2 = match(l1, l2)with
		| [], [] -> ()
		| _ , [] -> failwith("Instance "^i.instance_process_name^" hasn't enought output args\n")
		| [], _  -> failwith("Instance "^i.instance_process_name^" has too many output args\n")
		|s::l, ed::ld ->	if( s.signal_type = chk_sig si ed )
							then chk_out_types l ld
							else failwith("Instance "^i.instance_process_name^" has incorrect output types\n")
	in
	chk_out_types p_def.header.signal_declarations.output_signal_list i.instance_output_signals;
	chk_in_types p_def.header.signal_declarations.input_signal_list i.instance_input_expressions

let rec chk_instantiation p = function
	|[]		->	[]
	|e::l	->	let p_def = (chk_process_defined e.instance_process_name p.header.local_process_list) in
				chk_each_in_out_type p e p_def p.header.signal_declarations;
				e::(chk_instantiation p l)

(*
let rec f = function
	|[] -> "\n"
	|e::l -> e^" "^(f l)
						if(chk_lists
							(chk_list_sig p.header.signal_declarations e.instance_output_signals)
							(chk_input_expressions p e.instance_input_expressions))
						then(	print_string (f e.instance_output_signals);
								e::(chk_instantiation p l)
						)else failwith("Invalid type of args in call of "^p_def.header.process_name^"\n")
				)else failwith("Invalid number of args in call of "^p_def.header.process_name^"\n")
*)

let chk_assignment p (a:assignment) =
	let s = p.header.signal_declarations in
	try(let ab = get_sig_type a.assigned_signal_name
					(s.output_signal_list
					@s.local_signal_list)
		in if(ab=ab)then(
			let abc = chk_exp p (a.signal_expression)
			in if(abc=ab)
				then a
				else failwith("Invalid type for assignation "^a.assigned_signal_name)
			)else failwith("ab different de ab\n")
	) with Not_found -> failwith("Invalid assignment : "^a.assigned_signal_name)

let rec chk_body_assignments p = function
	|[]		-> []
	|a::l	-> (chk_assignment p a)::(chk_body_assignments p l)

let chk_body (p:process) = {
	assignment_list = chk_body_assignments p p.body.assignment_list; (* check that the variables used are already defined *)
	constraint_list = chk_constraint_list p p.body.constraint_list; (* check that the variables used are already defined *)
	instantiation_list = chk_instantiation p p.body.instantiation_list; (* check that the variables used are already defined and process used are already defined *)
}

let chk_process (p:process) = 
print_string ("process "^p.header.process_name^"...\n");
{
	header = (chk_header p.header);
	body = (chk_body p);
}

let rec chk_processes = function
	|[] -> []
	|p::l -> (chk_process p)::(chk_processes l)

let chk_spec sp = {
	process_list = chk_processes sp.process_list;
	type_declaration_list = sp.type_declaration_list;
	procedure_declaration_list = sp.procedure_declaration_list;

}
