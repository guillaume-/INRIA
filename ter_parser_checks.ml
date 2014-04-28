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
					then 
					else failwith ("Constraint using as input the undefined signal : "^c.right_signal_name^"\n")
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
	|[] -> true
	|s::l ->	try(
					let a = get_sig_type s
					(sig_declare.input_signal_list
					@sig_declare.output_signal_list
					@sig_declare.local_signal_list)
					in if(a=a)then
						chk_list_sig sig_declare l
					else
						failwith("a different de a \n")
				)with Not_found ->
						failwith("Signal "^(Identifier.of_string s)^" is not defined\n")

let rec chk_exp p = function
	| EnumVariantAtom(e) ->
		t1 p e
	| SignalAtom(e) ->
		chk_list_sig p.header.signal_declarations [e]
	| ClockPlus(e1, e2) ->
		((chk_exp p e1) && (chk_exp p e2))
	| ClockMinus(e1, e2) ->
		((chk_exp p e1) && (chk_exp p e2))
	| ClockTimes(e1, e2) ->
		((chk_exp p e1) && (chk_exp p e2))
	| Delay(e1, e2) ->
		((chk_exp p e1) && (chk_exp p e2))
	| EqualityAtom(e1, e2) ->
		((chk_exp p e1) && (chk_exp p e2))
	| InAtom(e, _) ->
		 chk_exp p e
	| Default(e1, e2) ->
		((chk_exp p e1) && (chk_exp p e2))
	| When(e1, e2) ->
		((chk_exp p e1) && (chk_exp p e2))
	| WhenAtom(e) ->
		chk_list_sig p.header.signal_declarations [e]
	| FunctionCall(f, exp) ->
		t2 p exp f
	| WhenNotAtom(e) ->
		chk_list_sig p.header.signal_declarations [e]
	| NotAtom(e) ->
		chk_list_sig p.header.signal_declarations [e]
	| AndExp(e1, e2) ->
		((chk_exp p e1) && (chk_exp p e2))
	| OrExp(e1, e2) ->
		((chk_exp p e1) && (chk_exp p e2))
	| IntegerConstant(i) ->
		true
	| Plus(e1, e2) ->
		((chk_exp p e1) && (chk_exp p e2))
	| Minus(e1, e2) ->
		((chk_exp p e1) && (chk_exp p e2))
	| Times(e1, e2) ->
		((chk_exp p e1) && (chk_exp p e2))
and chk_input_expressions p = function
	|[] -> true
	|exp::l ->	if(chk_exp p exp)
				then chk_input_expressions p l
				else failwith("chk_input_expressions : TER dead case\n")
and t1 p e =
	try(
		let a = gih_get_target e in
		a=a
	)with Not_found -> failwith("Enum "^e^" not defined\n")
and t2 p e f =
	try(
		let a = gih_get_procedure f in
		if(a=a)
		then chk_input_expressions p e
		else failwith("a different de a, attention !")
	)with Not_found -> failwith("Procedure "^f^" call but not defined\n")

let chk_arg_numbers p_def inst =
	( (List.length inst.instance_output_signals) = (List.length p_def.header.signal_declarations.output_signal_list))
	&& ( (List.length inst.instance_input_expressions) = (List.length p_def.header.signal_declarations.input_signal_list))

let rec chk_instantiation p = function
	|[]		->	[]
	|e::l	->	let p_def = (chk_process_defined e.instance_process_name p.header.local_process_list)
				in if((chk_arg_numbers p_def e)
				&& (chk_list_sig p.header.signal_declarations e.instance_output_signals)
				&& (chk_input_expressions p e.instance_input_expressions)
				)then e::(chk_instantiation p l)
				else failwith("Invalid number of args in call of "^p_def.header.process_name^"\n")

let chk_assignment p (a:assignment) =
	let s = p.header.signal_declarations in
	try(let ab = get_sig_type a.assigned_signal_name
					(s.output_signal_list
					@s.local_signal_list)
		in if(ab=ab)then
			if(chk_exp p (a.signal_expression))
			then a
			else failwith("Invalid assignation for "^a.assigned_signal_name)
		else	failwith("ab different de ab\n")
		
	)
	with Not_found -> failwith("Invalid assignment : "^a.assigned_signal_name)

let rec chk_body_assignments p = function
	|[]		-> []
	|a::l	-> (chk_assignment p a)::(chk_body_assignments p l)

let chk_body (p:process) = {
	assignment_list = chk_body_assignments p p.body.assignment_list; (* check that the variables used are already defined *)
	constraint_list = chk_constraint_list p p.body.constraint_list; (* check that the variables used are already defined *)
	instantiation_list = chk_instantiation p p.body.instantiation_list; (* check that the variables used are already defined and process used are already defined *)
}

let gih_chk_process (p:process) = 
print_string ("process "^p.header.process_name^"...\n");
{
	header = (chk_header p.header);
	body = (chk_body p);
}