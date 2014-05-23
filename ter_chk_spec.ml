open Ms_syntax_tree
open SyntaxTree
open Ms_identifier
open Ter_exception
open Ter_util
open Ter_iterateurs
open Ter_identite_p

module Apl_chk_spec:aParam = struct
	type ref = {spec:specification; proc_cur:process list; exp_types : Identifier.t list; fathers : Identifier.t list}

	module CsParam : tRef with type r = ref = struct
	type r = ref

	let creerRef s =
		let rec locaux pr res = (* res rentre valant [] *)
			let local_pr_list = List.rev pr.header.local_process_list in
			if(List.length local_pr_list > 0)
			then locaux (List.hd local_pr_list) ((local_pr_list)@res)
			else res
		in let loc = locaux (List.hd (List.rev s.process_list)) []
		in let rec buildF (p:process)res =
			if(List.length p.header.local_process_list) > 0
			then buildF (List.hd (List.rev p.header.local_process_list)) (p.header.process_name::res)
			else res
		in	{spec = s; proc_cur = loc@(List.rev s.process_list); exp_types = []; fathers = buildF (List.hd (List.rev s.process_list)) [];}
	end

	include Identite(CsParam)

	let chk_var param p en =
		let s = try List.find (fun e -> (IdentifierSet.exists (fun y -> y = en) e.variant_set)) param.spec.type_declaration_list
				with Not_found -> raise (Undefined(" enum value of "^en))
		in s.tv_type_name

	let chk_sig param decs sA =
		let s = try List.find	(fun e -> e.signal_name = sA)
								(decs.input_signal_list@decs.output_signal_list@decs.local_signal_list)
				with Not_found ->	let p = (List.hd param.proc_cur) 
									in try (ignore (chk_var param p sA);
											raise (Type_mismatch("Signal waited but "^sA^" found as enum")))
										with Undefined(_) -> raise (Undefined("Signal "^sA^"\ndeclarations = "^Ter_toString.str_signal_declarations decs))
		in s.signal_type

	let rec chk_exp param =
		let p = try(List.hd param.proc_cur)
		with Failure(_) -> failwith(" call of a check without process")
		in function
			| IntegerConstant(i) -> "integer"
			| EnumVariantAtom(e) -> chk_var param p e
			| FunctionCall(f, expL) -> chk_procedure param expL f
			| InAtom(e, ty) -> 
				if(ty.tv_type_name = chk_exp param e)
				then ty.tv_type_name
				else raise (Type_mismatch(" with 'in'"))
			| When(e1, e2) ->
				if((chk_exp param e2) = "boolean")
				then (chk_exp param e1)
				else raise (Type_mismatch(" with 'when' : boolean wanted"))
			| EqualityAtom(e1, e2) ->
				let t1 = chk_exp param e1 
				in if(t1 = (chk_exp param e2))
				then "boolean"
				else raise (Type_mismatch("Left and right types must be equals with '='"))
			| AndExp(e1, e2)
			| OrExp(e1, e2) ->
				if ((chk_exp param e1) = "boolean") && (chk_exp param e2) = "boolean"
				then "boolean"
				else raise (Type_mismatch(" with 'and', 'or' : boolean wanted"))
			| Plus(e1, e2)
			| Minus(e1, e2)
			| Times(e1, e2) ->
				if ((chk_exp param e1) = "integer") && (chk_exp param e2) = "integer"
				then "integer"
				else raise (Type_mismatch(" with '+', '-', '*' : integer wanted"))
			| WhenAtom(e)
			| WhenNotAtom(e)
			| NotAtom(e)
			| SignalAtom(e) -> chk_sig param p.header.signal_declarations e
			| ClockPlus(e1, e2)
			| ClockMinus(e1, e2)
			| ClockTimes(e1, e2) -> ignore (chk_exp param e1); (chk_exp param e2)
			| Delay(e1, e2)
			| Default(e1, e2) ->
				let t1 = chk_exp param e1 
				in if(t1 = (chk_exp param e2))
					then t1
					else raise (Type_mismatch("Left and right types must be equals with 'delay', 'default' and '='"))
	and chk_procedure param expL f =
		let fdec = List.find (fun e -> e.procedure_name = f) param.spec.procedure_declaration_list
		in	try if List.for_all2 (fun e1 e2 -> e1 = chk_exp param e2) fdec.procedure_input_list expL
				then fdec.procedure_output
				else raise (Type_mismatch(" in "^fdec.procedure_name))
			with Not_found -> raise (Undefined("Procedure "^f))		

	let apl_proced_decla param name inl out =
		let name_list = List.filter (fun e -> e.procedure_name = name) param.spec.procedure_declaration_list
		in if List.length name_list > 1
			then raise (Multiple_definition ("Procedure declaration: "^ name))
			else if List.exists (fun e -> e.tv_type_name = out) param.spec.type_declaration_list;
					then let tst_in = List.fold_left 
						(fun r -> fun id -> (List.exists (fun e -> e.tv_type_name = id) param.spec.type_declaration_list) && r ) 
						true inl
						in	if tst_in  
							then param
							else raise (Undefined ("Procedure declaration in " ^name^": Input type undefind")) 
					else raise (Undefined ("Procedure declaration: Output type in " ^name^": "^out^" undefind")) 

	let apl_typed_var_set param name vs =
		if(List.length (List.filter (fun e -> e.tv_type_name = name) param.spec.type_declaration_list) > 1)
		then raise (Multiple_definition("Typed variant set: "^name^"\n"))
		else param

	let apl_process param hd bd =
		let rec locals p res addFa =
			let tmp_res = (List.rev p.header.local_process_list)
			in if(List.length p.header.local_process_list)>0
				then if(List.exists (fun e -> e.header.process_name = p.header.process_name ) tmp_res)
						then raise (Multiple_definition(" of process "^p.header.process_name^" into itself"))
						else locals (List.hd tmp_res) (tmp_res@res) (p.header.process_name::addFa)
				else res, addFa
		in let res, fa =	try(locals (List.hd (List.tl param.proc_cur)) [] [])
							with Failure(_) -> [], []
		in let noconcat = try((List.hd param.proc_cur)
							= List.hd ((List.hd (List.tl param.proc_cur)).header.local_process_list)
						)with _ -> true
		in let delMultiples li =
			let rec del res = function
				|[] -> res
				|e::l -> if( try(e = List.hd l)
							 with _ -> false )
						 then del (e::res) (List.tl l)
						 else del (e::res) l
			in del [] (List.rev li)
		in let currents =	if(noconcat)
							then (List.tl param.proc_cur)
							else delMultiples(res@(List.tl param.proc_cur))
		in let fath =	try(if(hd.process_name = (List.hd param.fathers))
							then	if(noconcat)
									then(List.tl param.fathers)
									else delMultiples(fa@(List.tl param.fathers))
							else	if(noconcat)
									then(param.fathers)
									else delMultiples(fa@(param.fathers))
						)with Failure(_) -> fa
	in {spec=param.spec; proc_cur=currents; exp_types=[]; fathers=fath}

	let apl_proc_hd param name sp lpl =
		let name_list n = List.filter (fun e -> e.header.process_name = n)
		in let test_rest =
					if List.length (name_list name  param.proc_cur) > 1
					then raise (Multiple_definition ("Local process "^name))
					else param
		in let lgth_process_list = List.length (name_list name param.spec.process_list) 
		in	if lgth_process_list > 1
			then raise (Multiple_definition ("Process: "^ name))
			else	if lgth_process_list = 1 
					then	if List.find (fun e -> e.header.process_name = name) param.spec.process_list != (List.hd param.proc_cur)
							then raise (Multiple_definition ("Process: "^ name))
							else test_rest
					else test_rest
 
	let apl_sig_declas param isl osl losl =
		if((List.for_all (fun e -> e.signal_direction = Input) isl)
			&& (List.for_all (fun e -> e.signal_direction = Output) osl)
			&& (List.for_all (fun e -> e.signal_direction = Local) losl))
		then param
		else raise (Incompatible_definitions(" in process "^((List.hd param.proc_cur).header.process_name)^", some signals are record in a list that mismatch with the direction"))

	let apl_sig_decla param name stype dir =
		if(List.exists (fun e -> e.tv_type_name = stype) param.spec.type_declaration_list)
		then	let p_cur_sd = (List.hd param.proc_cur).header.signal_declarations
				in	let filtre = List.filter	(fun e -> e.signal_name = name)
												(p_cur_sd.input_signal_list @ p_cur_sd.output_signal_list @ p_cur_sd.local_signal_list)
				in	if List.length filtre > 1
					then raise (Multiple_definition("Signal declaration: "^name))
					else param
		else raise (Undefined("Type "^stype^"at the declaration of"^name))

	let apl_assign param asn ae =
		let decs = (List.hd param.proc_cur).header.signal_declarations
		in let s =	try List.find (fun e -> e.signal_name = asn) (decs.output_signal_list @ decs.local_signal_list)
					with Not_found ->	if(List.exists (fun e -> e.signal_name = asn) decs.input_signal_list)
										then raise (Incompatible_direction(asn^" defined as input, but is used as output"))
										else raise (Undefined(" signal "^asn^" in process "^((List.hd param.proc_cur).header.process_name)))
		in let ty = try(List.hd param.exp_types)
					with Failure(_) -> raise (Bad_construction("Assignation without expression defined"))
		in	if(ty = s.signal_type)
			then {spec=param.spec; proc_cur=param.proc_cur; exp_types=[]; fathers = param.fathers}
			else raise (Type_mismatch("Assignation has Out type "^s.signal_type^", but has for In type "^ty))

	let apl_sconstr param const_kind sLeft sRight =
		let d = try (List.hd param.proc_cur).header.signal_declarations
				with Failure(_) -> raise (Bad_construction("Constraint call but any current process"))
		in	ignore (chk_sig param d sLeft);
			ignore (chk_sig param d sRight);
			param

	let apl_inst param ipn ios iie =
		let okList = (List.filter
						(fun e -> not(List.exists (fun x -> x=e.header.process_name) param.fathers))
						(List.tl param.proc_cur)
					 )
		in if(	not ( List.exists (fun e -> e.header.process_name = ipn) okList
				or	  List.exists (fun e -> e.header.process_name = ipn) (List.hd param.proc_cur).header.local_process_list))
			then raise (Incorrect_call(ipn^" can not be call here"))
			else let chk_lgth p_sd = (List.length ios = List.length p_sd.output_signal_list)
								&& (List.length iie = List.length p_sd.input_signal_list)
				and find_t o = 
						let decs = (List.hd param.proc_cur).header.signal_declarations
						in let sigs = decs.input_signal_list @ decs.output_signal_list @ decs.local_signal_list
						in let f = try List.find (fun e -> e.signal_name = o) sigs 
									with |Not_found -> failwith "TROUVE ??"
									in f.signal_type
									
				in	let chk_out_types p_sd_o = List.fold_left2 (fun r -> fun o -> fun s -> (find_t o = s.signal_type) && r) true ios p_sd_o
					and chk_in_types p_sd_i = List.fold_left2 (fun r -> fun t -> fun s -> (t = s.signal_type) && r) true param.exp_types p_sd_i
					in let chk_in_out p =
							let pr_sd = p.header.signal_declarations
							in	if chk_lgth pr_sd 
								then if chk_out_types pr_sd.output_signal_list 
									then if chk_in_types pr_sd.input_signal_list 
										then {spec = param.spec; proc_cur = param.proc_cur; exp_types = []; fathers = param.fathers}
										else raise (Type_mismatch ("Instance "^ipn^" : input types"))
									else raise (Type_mismatch ("Instance "^ipn^" : output types"))
								else raise (Invalide_argument_numbers ("Instance "^ipn))
								
						in let tst_proc = List.exists (fun e -> e.header.process_name = ipn)  
						in	if (tst_proc param.proc_cur) 
							then	let p_ref = try List.find (fun e -> e.header.process_name = ipn) param.proc_cur
												with | Not_found -> failwith "2"
									in chk_in_out p_ref
							else	if (tst_proc (List.hd param.proc_cur).header.local_process_list)
									then	let p_ref = try List.find (fun e -> e.header.process_name = ipn) (List.hd param.proc_cur).header.local_process_list
														with | Not_found -> failwith "3"
											in chk_in_out p_ref
									else raise (Undefined("Submodule name: "^ipn))

	let apl_sig_exp param exp = {spec = param.spec ; proc_cur = param.proc_cur ; exp_types = (chk_exp param exp)::param.exp_types; fathers = param.fathers}
end
