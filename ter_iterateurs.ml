open Ms_syntax_tree
open SyntaxTree
open Ms_identifier ;;

module type tTransf = sig
    val tfr_spec:  process list -> typed_variant_set list -> procedure_declaration list -> specification
    val tfr_proced_decla:  Identifier.t -> Identifier.t list -> Identifier.t -> procedure_declaration
    val tfr_process: process_header -> process_body -> process
    val tfr_proc_hd: Identifier.t -> signal_declarations -> process list -> process_header
    val tfr_sig_declas: signal_declaration list -> signal_declaration list -> signal_declaration list -> signal_declarations
    val tfr_proc_bd: assignment list -> sconstraint list -> instantiation list -> process_body
    val tfr_inst: Identifier.t -> Identifier.t list -> signal_expression list -> instantiation
    val tfr_sconstr: sconstraint_kind -> Identifier.t -> Identifier.t -> sconstraint
    val tfr_sconstr_k: sconstraint_kind -> sconstraint_kind
    val tfr_assign: Identifier.t -> signal_expression -> assignment
    val tfr_sig_exp: signal_expression -> signal_expression
    val tfr_sig_decla: Identifier.t -> Identifier.t -> direction -> signal_declaration
    val tfr_direc: direction -> direction
    val tfr_typed_var_set: Identifier.t -> IdentifierSet.t -> typed_variant_set
    val tfr_identifier: Identifier.t -> Identifier.t
    val tfr_identifier_set:  IdentifierSet.t -> IdentifierSet.t
end

module Transformation(T: tTransf) = struct 

    let transform_id i = T.tfr_identifier i
    
    let transform_id_set is = T.tfr_identifier_set is
  
    let transform_typed_var_set tvs =  
	let nttn = transform_id tvs.tv_type_name
	and nvs = transform_id_set tvs.variant_set
	in  T.tfr_typed_var_set nttn nvs

    let transform_direc d = T.tfr_direc d
   
    let transform_sig_decla sd = 
	let nsn = transform_id sd.signal_name 
	and nst = transform_id sd.signal_type
	and nd = transform_direc sd.signal_direction
	in T.tfr_sig_decla nsn nst nd
      
   
    let transform_sig_exp e = T.tfr_sig_exp e
    
    let transform_assign a = 
	let nasn = transform_id a.assigned_signal_name
	and nse = transform_sig_exp a.signal_expression
	in T.tfr_assign nasn nse

    let transform_sconstr_k sck = T.tfr_sconstr_k sck
    
    let transform_sconstr sc = 
	let nck = transform_sconstr_k sc.constraint_kind
	and nlsn = transform_id sc.left_signal_name
	and nrsn = transform_id sc.right_signal_name
	in T.tfr_sconstr nck nlsn nrsn
    
    let transform_inst i = 
	let niie = List.fold_right (fun e -> fun r -> let ne = (transform_sig_exp e) in (ne::r)) i.instance_input_expressions []
	and nios = List.fold_right (fun o -> fun r -> let no = (transform_id o) in (no::r)) i.instance_output_signals []
	and nipn = transform_id i.instance_process_name
	    in T.tfr_inst nipn nios niie

      let transform_proc_bd pbd = 
	let nal = List.fold_right (fun a -> fun r -> let na = (transform_assign a) in (na::r)) pbd.assignment_list []
	and ncl = List.fold_right (fun c -> fun r -> let nc = (transform_sconstr c) in (nc::r)) pbd.constraint_list []
	and nil = List.fold_right (fun i -> fun r -> let ni = (transform_inst i) in (ni::r)) pbd.instantiation_list []
	in T.tfr_proc_bd nal ncl nil 
    
      let transform_sig_declas sds = 
	let nisl = List.fold_right (fun i -> fun r -> let ni = (transform_sig_decla i) in (ni::r)) sds.input_signal_list []
	and nosl = List.fold_right (fun o -> fun r -> let no = (transform_sig_decla o) in (no::r)) sds.output_signal_list [] 
	and nlsl = List.fold_right (fun l -> fun r -> let nl = (transform_sig_decla l) in (nl::r)) sds.local_signal_list []  
	in T.tfr_sig_declas nisl nosl nlsl
    
     let rec transform_process p = 
	let nh = transform_proc_hd p.header
	and nb = transform_proc_bd p.body
	in T.tfr_process nh nb
     and transform_proc_hd phd = 
	let nlpl = List.fold_right (fun p -> fun r -> let np = (transform_process p) in (np::r)) phd.local_process_list []
	and npn = transform_id phd.process_name
	and sdn = transform_sig_declas phd.signal_declarations
	in T.tfr_proc_hd npn sdn nlpl

     let transform_proced_decla pd = 
	let nil = List.fold_right (fun i -> fun r -> let ni = (transform_id i) in (ni::r)) pd.procedure_input_list []
	and npn = transform_id pd.procedure_name
	and npo = transform_id pd.procedure_output
	in T.tfr_proced_decla npn nil npo
 
     let transform_spec s= 
	let npl = List.fold_right (fun p -> fun r -> let np = (transform_process p) in (np::r)) s.process_list []
	and ntdl = List.fold_right (fun t -> fun r -> let nt = (transform_typed_var_set t) in (nt::r)) s.type_declaration_list []
	and npdl = List.fold_right (fun p -> fun r -> let np = (transform_proced_decla p) in (np::r)) s.procedure_declaration_list []
	in T.tfr_spec npl ntdl npdl 
end

module Identite:tTransf= struct
    let tfr_spec pl tdl pdl = {
	process_list = pl;
	type_declaration_list = tdl;
	procedure_declaration_list = pdl;
    }

    let tfr_proced_decla pn pi po = {
	procedure_name = pn;
	procedure_input_list = pi;
	procedure_output = po;
    }
    
    let tfr_process ph pb = {
	header = ph;
	body = pb;
    }
    
    let tfr_proc_hd pn sd lpl = {
	process_name = pn;
	signal_declarations = sd;
	local_process_list = lpl;
    }
    
    let tfr_sig_declas isl osl lSl = {
	input_signal_list = isl;
	output_signal_list = osl;
	local_signal_list = lSl;
    } 
    
    let tfr_proc_bd al cl il = {
	assignment_list = al ;
	constraint_list = cl;
	instantiation_list = il;
    }
    
    let tfr_inst ipn ios iie = {
	instance_process_name = ipn;
	instance_output_signals = ios;
	instance_input_expressions = iie;
    } 
    
    let tfr_sconstr ck lsn rsn = {
	constraint_kind = ck;
	left_signal_name = lsn;
	right_signal_name = rsn;
    }

    let tfr_sconstr_k = function
	ClockEquality -> ClockEquality
	| ClockLeq  -> ClockLeq
	| ClockLess -> ClockLess
	| ClockWhen -> ClockWhen
	| ClockWhenNot -> ClockWhenNot
	| ClockExclusive -> ClockExclusive
    
    let tfr_assign asn ae = {
	assigned_signal_name = asn;
	signal_expression = ae;
    }
    
    let tfr_identifier i = i
    
    let tfr_identifier_set is = IdentifierSet.fold (fun e -> fun r -> IdentifierSet.add (tfr_identifier e) r) is IdentifierSet.empty
    
    let tfr_typed_var_set ttn vs = {
	tv_type_name = ttn;
	variant_set = vs;
    }

    let rec tfr_sig_exp = function
	EnumVariantAtom(i) -> let ni = tfr_identifier i
		in EnumVariantAtom(ni)
	| SignalAtom(i) -> let ni = tfr_identifier i
		in SignalAtom(ni)
	| WhenAtom(i) -> let ni = tfr_identifier i
		in WhenAtom(ni)
	| NotAtom(i) -> let ni = tfr_identifier i
		in NotAtom(ni)
	| WhenNotAtom(i) -> let ni = tfr_identifier i
		in WhenNotAtom(ni)

	| IntegerConstant(i) -> IntegerConstant(i)

	| ClockPlus(e1, e2) -> 
		let ne1 = tfr_sig_exp e1
		and ne2 = tfr_sig_exp e2
		in ClockPlus(ne1, ne2)
	| ClockMinus(e1, e2) -> 
		let ne1 = tfr_sig_exp e1
		and ne2 = tfr_sig_exp e2
		in ClockMinus(ne1, ne2)
	| ClockTimes(e1, e2) -> 
		let ne1 = tfr_sig_exp e1
		and ne2 = tfr_sig_exp e2
		in ClockTimes(ne1, ne2)
	| Delay(e1, e2) -> 
		let ne1 = tfr_sig_exp e1
		and ne2 = tfr_sig_exp e2
		in Delay(ne1, ne2)
	| EqualityAtom(e1, e2) -> 
		let ne1 = tfr_sig_exp e1
		and ne2 = tfr_sig_exp e2
		in EqualityAtom(ne1,ne2)
	| Default(e1, e2) -> 
		let ne1 = tfr_sig_exp e1
		and ne2 = tfr_sig_exp e2
		in Default(ne1, ne2)
	| When(e1, e2) -> 
		let ne1 = tfr_sig_exp e1
		and ne2 = tfr_sig_exp e2
		in When(ne1, ne2)
	| AndExp(e1, e2) -> 
		let ne1 = tfr_sig_exp e1
		and ne2 = tfr_sig_exp e2
		in AndExp(ne1, ne2)
	| OrExp(e1, e2) -> 
		let ne1 = tfr_sig_exp e1
		and ne2 = tfr_sig_exp e2
		in OrExp(ne1, ne2)
	| Plus(e1, e2) -> 
		let ne1 = tfr_sig_exp e1
		and ne2 = tfr_sig_exp e2
		in Plus(ne1, ne2)
	| Minus(e1, e2) -> 
		let ne1 = tfr_sig_exp e1
		and ne2 = tfr_sig_exp e2
		in Minus(ne1, ne2)
	| Times(e1, e2) -> 
		let ne1 = tfr_sig_exp e1
		and ne2 = tfr_sig_exp e2
		in Times(ne1, ne2)
	| FunctionCall(i, el) -> 
		let ni = tfr_identifier i
		and nel = List.fold_right (fun e -> fun r -> let ne = (tfr_sig_exp e) in (ne::r)) el []
		in FunctionCall(ni,nel)
	| InAtom(e, tvs) ->
		let ne = tfr_sig_exp e
		and nttn = tfr_identifier tvs.tv_type_name
		and nvs = tfr_identifier_set tvs.variant_set
		in  let ntvs = tfr_typed_var_set nttn nvs
		    in InAtom(ne, ntvs)
    
    let tfr_sig_decla sn st sd = {
	signal_name = sn;
	signal_type = st;
	signal_direction = sd;
    }
    
    let tfr_direc = function
	Input -> Input
	| Output -> Output
	| Local -> Local
end


module Tfr_arith_to_call:tTransf = struct
    include Identite
    
    let tfr_spec pl tdl pdl = {
	process_list = pl;
	type_declaration_list = tdl;
	procedure_declaration_list = 
	    let add = 
		{procedure_name = "add";
		procedure_input_list = ["integer"; "integer"];
		procedure_output = "Integer";}
	    and min =  
		{procedure_name = "min";
		procedure_input_list = ["integer"; "integer"];
		procedure_output = "Integer";}
	    and mul =  
		{procedure_name = "mul";
		procedure_input_list = ["integer"; "integer"];
		procedure_output = "integer";}
	    in add::(min::(mul::pdl));
    }

    let rec tfr_sig_exp =  function
	| Plus(e1, e2) -> let ne1 = tfr_sig_exp e1 
			and ne2 = tfr_sig_exp e2
			in FunctionCall("add", [ne1; ne2])
	| Minus(e1, e2) -> let ne1 = tfr_sig_exp e1 
			and ne2 = tfr_sig_exp e2
			in FunctionCall("sub", [ne1; ne2])
	| Times(e1, e2) -> let ne1 = tfr_sig_exp e1 
			and ne2 = tfr_sig_exp e2
			in FunctionCall("mul", [ne1; ne2])
    
	| EnumVariantAtom(i) -> let ni = tfr_identifier i
		in EnumVariantAtom(ni)
	| SignalAtom(i) -> let ni = tfr_identifier i
		in SignalAtom(ni)
	| WhenAtom(i) -> let ni = tfr_identifier i
		in WhenAtom(ni)
	| NotAtom(i) -> let ni = tfr_identifier i
		in NotAtom(ni)
	| WhenNotAtom(i) -> let ni = tfr_identifier i
		in WhenNotAtom(ni)
	| IntegerConstant(i) -> IntegerConstant(i)

	| ClockPlus(e1, e2) -> 
		let ne1 = tfr_sig_exp e1
		and ne2 = tfr_sig_exp e2
		in ClockPlus(ne1, ne2)
	| ClockMinus(e1, e2) -> 
		let ne1 = tfr_sig_exp e1
		and ne2 = tfr_sig_exp e2
		in ClockMinus(ne1, ne2)
	| ClockTimes(e1, e2) -> 
		let ne1 = tfr_sig_exp e1
		and ne2 = tfr_sig_exp e2
		in ClockTimes(ne1, ne2)
	| Delay(e1, e2) -> 
		let ne1 = tfr_sig_exp e1
		and ne2 = tfr_sig_exp e2
		in Delay(ne1, ne2)
	| EqualityAtom(e1, e2) -> 
		let ne1 = tfr_sig_exp e1
		and ne2 = tfr_sig_exp e2
		in EqualityAtom(ne1,ne2)
	| Default(e1, e2) -> 
		let ne1 = tfr_sig_exp e1
		and ne2 = tfr_sig_exp e2
		in Default(ne1, ne2)
	| When(e1, e2) -> 
		let ne1 = tfr_sig_exp e1
		and ne2 = tfr_sig_exp e2
		in When(ne1, ne2)
	| AndExp(e1, e2) -> 
		let ne1 = tfr_sig_exp e1
		and ne2 = tfr_sig_exp e2
		in AndExp(ne1, ne2)
	| OrExp(e1, e2) -> 
		let ne1 = tfr_sig_exp e1
		and ne2 = tfr_sig_exp e2
		in OrExp(ne1, ne2)

	| FunctionCall(i, el) -> 
		let ni = tfr_identifier i
		and nel = List.fold_right (fun e -> fun r -> let ne = (tfr_sig_exp e) in (ne::r)) el []
		in FunctionCall(ni,nel)
	| InAtom(e, tvs) ->
		let ne = tfr_sig_exp e
		and nttn = tfr_identifier tvs.tv_type_name
		and nvs = tfr_identifier_set tvs.variant_set
		in  let ntvs = tfr_typed_var_set nttn nvs
		    in InAtom(ne, ntvs)

end


let do_transfo prog =
  let module Apply_transfo = Transformation((*Identite*)Tfr_arith_to_call) in
  Apply_transfo.transform_spec prog 
