open Ms_syntax_tree
open SyntaxTree
open Ms_identifier
open Ter_exception
open Ter_util
open Ter_iterateurs

module type tRef = sig
	type r
	val creerRef: specification -> r
end

module IdParam : tRef = struct
	type r = unit
	let creerRef _ = ()
end

module Identite(R : tRef):tParam with type t = R.r = struct
	type t = R.r 
	let creerT = R.creerRef
	
	let tfr_spec s pl tdl pdl = ({
	process_list = pl;
	type_declaration_list = tdl;
	procedure_declaration_list = pdl;
	},s)

	let tfr_proced_decla s pn pi po = ({
	procedure_name = pn;
	procedure_input_list = pi;
	procedure_output = po;
	},s)
	
	let tfr_process s ph pb = ({
	header = ph;
	body = pb;
	},s)
	
	let tfr_proc_hd s pn sd lpl = ({
	process_name = pn;
	signal_declarations = sd;
	local_process_list = lpl;
	},s)

	let tfr_sig_declas s isl osl lSl = ({
	input_signal_list = isl;
	output_signal_list = osl;
	local_signal_list = lSl;
	},s) 

	let tfr_proc_bd s al cl il = ({
	assignment_list = al ;
	constraint_list = cl;
	instantiation_list = il;
	} ,s)

	let tfr_inst s ipn ios iie = ({
	instance_process_name = ipn;
	instance_output_signals = ios;
	instance_input_expressions = iie;
	},s) 

	let tfr_sconstr s ck lsn rsn = ({
	constraint_kind = ck;
	left_signal_name = lsn;
	right_signal_name = rsn;
	},s)

	let tfr_sconstr_k s = function
	ClockEquality -> (ClockEquality,s)
	| ClockLeq  -> (ClockLeq,s)
	| ClockLess -> (ClockLess,s)
	| ClockWhen -> (ClockWhen,s)
	| ClockWhenNot -> (ClockWhenNot,s)
	| ClockExclusive -> (ClockExclusive,s)

	let tfr_assign s asn ae = ({
	assigned_signal_name = asn;
	signal_expression = ae;
	},s)

	let tfr_identifier s i = (i,s)

	let tfr_identifier_set s is = 
	let nis = IdentifierSet.fold (fun e -> fun r -> let ne,_ = (tfr_identifier s e) in (IdentifierSet.add ne r)) is IdentifierSet.empty
	in (nis,s)

	 let tfr_typed_var_set s ttn vs = ({
	tv_type_name = ttn;
	variant_set =vs;
	},s)

	let rec tfr_sig_exp s = function
	EnumVariantAtom(i) -> let ni,_ = tfr_identifier s i
		in (EnumVariantAtom(ni),s)
	| SignalAtom(i) -> let ni,_ = tfr_identifier s i
		in (SignalAtom(ni),s)
	| WhenAtom(i) -> let ni,_ = tfr_identifier s i
		in (WhenAtom(ni),s)
	| NotAtom(i) -> let ni,_ = tfr_identifier s i
		in (NotAtom(ni),s)
	| WhenNotAtom(i) -> let ni,_ = tfr_identifier s i
		in (WhenNotAtom(ni),s)

	| IntegerConstant(i) -> (IntegerConstant(i),s)

	| ClockPlus(e1, e2) -> 
		let ne1, _ = tfr_sig_exp s e1
		and ne2, _ = tfr_sig_exp s e2
		in (ClockPlus(ne1, ne2),s)
	| ClockMinus(e1, e2) -> 
		let ne1, _ = tfr_sig_exp s e1
		and ne2, _ = tfr_sig_exp s e2
		in (ClockMinus(ne1, ne2),s)
	| ClockTimes(e1, e2) -> 
		let ne1, _ = tfr_sig_exp s e1
		and ne2, _ = tfr_sig_exp s e2
		in (ClockTimes(ne1, ne2),s)
	| Delay(e1, e2) -> 
		let ne1, _ = tfr_sig_exp s e1
		and ne2, _ = tfr_sig_exp s e2
		in (Delay(ne1, ne2),s)
	| EqualityAtom(e1, e2) -> 
		let ne1, _ = tfr_sig_exp s e1
		and ne2, _ = tfr_sig_exp s e2
		in (EqualityAtom(ne1,ne2),s)
	| Default(e1, e2) -> 
		let ne1, _ = tfr_sig_exp s e1
		and ne2, _ = tfr_sig_exp s e2
		in (Default(ne1, ne2),s)
	| When(e1, e2) -> 
		let ne1, _ = tfr_sig_exp s e1
		and ne2, _ = tfr_sig_exp s e2
		in (When(ne1, ne2),s)
	| AndExp(e1, e2) -> 
		let ne1, _ = tfr_sig_exp s e1
		and ne2, _ = tfr_sig_exp s e2
		in (AndExp(ne1, ne2),s)
	| OrExp(e1, e2) -> 
		let ne1, _ = tfr_sig_exp s e1
		and ne2, _ = tfr_sig_exp s e2
		in (OrExp(ne1, ne2),s)
	| Plus(e1, e2) -> 
		let ne1, _ = tfr_sig_exp s e1
		and ne2, _ = tfr_sig_exp s e2
		in (Plus(ne1, ne2),s)
	| Minus(e1, e2) -> 
		let ne1, _ = tfr_sig_exp s e1
		and ne2, _ = tfr_sig_exp s e2
		in  (Minus(ne1, ne2),s)
	| Times(e1, e2) -> 
		let ne1, _ = tfr_sig_exp s e1
		and ne2, _ = tfr_sig_exp s e2
		in (Times(ne1, ne2),s)
	| FunctionCall(i, el) -> 
		let ni,_ = tfr_identifier s i
		and nel = List.fold_right (fun e -> fun r -> let (ne,_) = (tfr_sig_exp s e) in (ne::r)) el []
		in (FunctionCall(ni,nel),s) 
	| InAtom(e, tvs) ->  
		let ne,_ = tfr_sig_exp s e
		and nttn,_ = tfr_identifier s tvs.tv_type_name
		and nvs,_ = tfr_identifier_set s tvs.variant_set
		in  let ntvs,_ = tfr_typed_var_set s nttn nvs
			in (InAtom(ne, ntvs),s)

	
	let tfr_sig_decla s sn st sd = ({
	signal_name = sn;
	signal_type = st;
	signal_direction = sd;
	},s)
	
	let tfr_direc s = function
	Input -> (Input,s)
	| Output -> (Output,s)
	| Local -> (Local,s)
	
end
