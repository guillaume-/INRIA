open Ms_syntax_tree;;
open SyntaxTree;;
open Ms_identifier ;;

module type tParam = sig
    type t
    val creerT : t
    val verifT : t -> t list -> t
    
    val tfr_spec:  t -> process list -> typed_variant_set list -> procedure_declaration list -> specification * t
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
end

module Transformation(T: tParam) = struct 
    let transform_id s i = T.tfr_identifier s i
    
    let transform_id_set s is = T.tfr_identifier_set s is

    let transform_typed_var_set s tvs =  
	let nttn, s1 = transform_id s tvs.tv_type_name
	and nvs, s2 = transform_id_set s tvs.variant_set
	in let rs = T.verifT s (s1::[s2])
	    in T.tfr_typed_var_set rs nttn nvs

    let transform_direc s d = T.tfr_direc s d
   
    let transform_sig_decla s sd = 
	let nsn,s1 = transform_id s sd.signal_name 
	and nst,s2 = transform_id s sd.signal_type
	and nd,s3 = transform_direc s sd.signal_direction
	in let rs = T.verifT s (s1::s2::[s3])
	    in T.tfr_sig_decla rs nsn nst nd
      
   
    let transform_sig_exp s e = T.tfr_sig_exp s e
    
    let transform_assign s a = 
	let nasn,s1 = transform_id s a.assigned_signal_name
	and nse,s2 = transform_sig_exp s a.signal_expression
	in let rs = T.verifT s (s1::[s2])
	    in T.tfr_assign rs nasn nse

    let transform_sconstr_k s sck = T.tfr_sconstr_k s sck
    
    let transform_sconstr s sc = 
	let nck,s1 = transform_sconstr_k s sc.constraint_kind
	and nlsn,s2 = transform_id s sc.left_signal_name
	and nrsn,s3 = transform_id s sc.right_signal_name
	in let rs = T.verifT s (s1::s2::[s3])
	    in T.tfr_sconstr rs nck nlsn nrsn
    
    let transform_inst s i = 
	let (niie,ls1) = List.fold_right (fun e -> fun (r,rs) -> let ne,s1 = (transform_sig_exp s e) in ((ne::r),(s1::rs))) i.instance_input_expressions ([],[])
	and (nios,ls2) = List.fold_right (fun o -> fun (r,rs) -> let no,s1 = (transform_id s o) in ((no::r),(s1::rs))) i.instance_output_signals ([],[])
	and nipn,s3 = transform_id s i.instance_process_name
	in let rs = T.verifT s (s3::(ls1@ls2))
	    in T.tfr_inst rs nipn nios niie

      let transform_proc_bd s pbd = 
	let (nal,ls1) = List.fold_right (fun a -> fun (r,rs) -> let na,s1 = (transform_assign s a) in (na::r),(s1::rs)) pbd.assignment_list ([],[])
	and (ncl,ls2) = List.fold_right (fun c -> fun (r,rs) -> let nc,s1 = (transform_sconstr s c) in (nc::r),(s1::rs)) pbd.constraint_list ([],[])
	and (nil,ls3) = List.fold_right (fun i -> fun (r,rs) -> let ni,s1 = (transform_inst s i) in (ni::r),(s1::rs)) pbd.instantiation_list ([],[])
	in let rs = T.verifT s (ls1@ls2@ls3)
	    in T.tfr_proc_bd rs nal ncl nil 
    
      let transform_sig_declas s sds = 
	let (nisl,ls1) = List.fold_right (fun i -> fun (r,rs) -> let ni,s1 = (transform_sig_decla s i) in (ni::r),(s1::rs)) sds.input_signal_list ([],[])
	and (nosl,ls2) = List.fold_right (fun o -> fun (r,rs) -> let no,s1 = (transform_sig_decla s o) in (no::r),(s1::rs)) sds.output_signal_list ([],[]) 
	and (nlsl,ls3) = List.fold_right (fun l -> fun (r,rs) -> let nl,s1 = (transform_sig_decla s l) in (nl::r),(s1::rs)) sds.local_signal_list ([],[])  
	in let rs = T.verifT s (ls1@ls2@ls3)
	    in T.tfr_sig_declas rs nisl nosl nlsl
    
     let rec transform_process s p = 
	let nh,s1 = transform_proc_hd s p.header
	and nb,s2 = transform_proc_bd s p.body
	in let rs1 = T.verifT s (s1::[s2])
	    in T.tfr_process rs1 nh nb
     and transform_proc_hd s phd = 
	let (nlpl,ls1) = List.fold_right (fun p -> fun (r,rs) -> let np,s1 = (transform_process s p) in (np::r),(s1::rs)) phd.local_process_list ([],[])
	and npn,s2 = transform_id s phd.process_name
	and sdn,s3 = transform_sig_declas s phd.signal_declarations
	in let rs2 = T.verifT s (s3::(s2::ls1))
	    in T.tfr_proc_hd rs2 npn sdn nlpl
	
     let transform_proced_decla s pd = 
	let nil,ls1 = List.fold_right (fun i -> fun (r,rs) -> let ni,s1 = (transform_id s i) in (ni::r),(s1::rs)) pd.procedure_input_list ([],[])
	and npn,s2 = transform_id s pd.procedure_name
	and npo,s3 = transform_id s pd.procedure_output
	in let rs = T.verifT s (s3::(s2::ls1))
	    in T.tfr_proced_decla rs npn nil npo
 
     let transform_spec s= 
	let sp = T.creerT
	    in let npl,ls1 = List.fold_right (fun p -> fun (r,rs) -> let np,s1 = (transform_process sp p) in (np::r),(s1::rs)) s.process_list ([],[])
	    and ntdl,ls2 = List.fold_right (fun t -> fun (r,rs) -> let nt,s1 = (transform_typed_var_set sp t) in (nt::r),(s1::rs)) s.type_declaration_list ([],[])
	    and npdl,ls3 = List.fold_right (fun p -> fun (r,rs) -> let np,s1 = (transform_proced_decla sp p) in (np::r),(s1::rs)) s.procedure_declaration_list ([],[])
	    in let rs =  T.verifT sp (ls1@ls2@ls3)
		in let (r,_) = T.tfr_spec rs npl ntdl npdl in r
end

module type tRef = sig
    type r
    type p 
   
    val creerRef: r
    val getRef: r -> r
    val setRef: r -> p -> r 
    val tstRef: r -> p -> bool
    val verifRef: r -> r list -> r
    
    val getPart: string -> p

end

module IdParam : tRef = struct
    type r = unit
    type p = unit
    
    let creerRef = ()
    let getRef _ = ()
    let setRef _ _ = ()
    let tstRef _ _= true
    let verifRef _ _ = ()
    
    let getPart _ = ()

end

module Identite(R : tRef):tParam with type t = R.r = struct
    type t = R.r 
    let creerT = R.creerRef
    let verifT = R.verifRef
    
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


module Tfr_arith_to_call:tParam  = struct
    module AtcParam : tRef with type r = procedure_declaration list = struct
	type r = procedure_declaration list
	type p = procedure_declaration
	
	let creerRef = []
	let getRef r = r
	let setRef r p = p::r
	 let tstRef r p = 
			(List.exists (fun d -> d = p) r)

	let verifRef s =
	      let rec verif = function
	      | [] -> s
	      | e::l ->  let reste = verif l 
			in let rec v = function
			      | [] -> reste
			      | t::q -> let rst = v q
					in if tstRef rst t then rst else setRef rst t
			    in v e
	  in verif
	  
	let getPart s =  {procedure_name = s ;
			  procedure_input_list = ["integer";"integer"] ; 
			  procedure_output = "integer" ;}
	
    end
    include Identite(AtcParam)
    
    let gR = AtcParam.getRef
    let sR = AtcParam.setRef 
    let tR = AtcParam.tstRef
    let vR = AtcParam.verifRef
    
    let tfr_spec s pl tdl pdl = ({
	process_list = pl;
	type_declaration_list = tdl;
	procedure_declaration_list = vR s [pdl];
    },s) 

    let rec tfr_sig_exp (s:t) exp =  
	let trait st e1 e2 = 
		let (ne1, s1) = tfr_sig_exp st e1 
		and (ne2, s2) = tfr_sig_exp st e2
		in let rst = vR st (s1::[s2])
		    in (ne1, ne2, rst)
		    
	and chk p res = if tR res p
			then res
			else sR res p
			
	in match exp with
		| Plus(e1, e2) -> let (ne1, ne2, rs) = trait s e1 e2
				  in ((FunctionCall("add", [ne1; ne2])),
				      (chk (AtcParam.getPart "add") rs))
		| Minus(e1, e2) ->let (ne1, ne2, rs) = trait s e1 e2
				in  ((FunctionCall("sub", [ne1; ne2])) , (chk (AtcParam.getPart "sub") rs))
		| Times(e1, e2) -> let (ne1, ne2, rs) = trait s e1 e2
				in ((FunctionCall("mul", [ne1; ne2])) , (chk (AtcParam.getPart "mul") rs))

		| EnumVariantAtom(i) -> let ni,rs = tfr_identifier s i
			in (EnumVariantAtom(ni),rs)
		| SignalAtom(i) -> let ni,rs = tfr_identifier s i
			in (SignalAtom(ni),rs)
		| WhenAtom(i) -> let ni,rs = tfr_identifier s i
			in (WhenAtom(ni),rs)
		| NotAtom(i) -> let ni,rs = tfr_identifier s i
			in (NotAtom(ni),rs)
		| WhenNotAtom(i) -> let ni,rs = tfr_identifier s i
			in (WhenNotAtom(ni),rs)
		
		| IntegerConstant(i) -> (IntegerConstant(i),s)
		
		| ClockPlus(e1, e2) -> 
			let (ne1, ne2, rs) = trait s e1 e2
			in (ClockPlus(ne1, ne2),rs)
		| ClockMinus(e1, e2) -> 
			let (ne1, ne2, rs) = trait s e1 e2
			in (ClockMinus(ne1, ne2),rs)
		| ClockTimes(e1, e2) -> 
			let (ne1, ne2, rs) = trait s e1 e2
			in (ClockTimes(ne1, ne2),rs)
		| Delay(e1, e2) -> 
			let (ne1, ne2, rs) = trait s e1 e2
			in (Delay(ne1, ne2),rs)
		| EqualityAtom(e1, e2) -> 
			let (ne1, ne2, rs) = trait s e1 e2
			in (EqualityAtom(ne1,ne2),rs)
		| Default(e1, e2) -> 
			let (ne1, ne2, rs) = trait s e1 e2
			in (Default(ne1, ne2),rs)
		| When(e1, e2) -> 
			let (ne1, ne2, rs) = trait s e1 e2
			in (When(ne1, ne2),rs)
		| AndExp(e1, e2) -> 
			let (ne1, ne2, rs) = trait s e1 e2
			in (AndExp(ne1, ne2),rs)
		| OrExp(e1, e2) -> 
			let (ne1, ne2, rs) = trait s e1 e2
			in (OrExp(ne1, ne2),rs)
		| FunctionCall(i, el) -> 
			let ni,s1 = tfr_identifier s i
			and nel,ls1 = List.fold_right (fun e -> fun (r,rs) -> let (ne,ns) = (tfr_sig_exp s e) in (ne::r),(ns::rs)) el ([],[])
			in let rs = vR s (s1::ls1)
			in (FunctionCall(ni,nel),rs) 
		| InAtom(e, tvs) ->  
			let ne,s1 = tfr_sig_exp s e
			and nttn,s2 = tfr_identifier s tvs.tv_type_name
			and nvs,s3 = tfr_identifier_set s tvs.variant_set
			in  let ntvs,s4 = tfr_typed_var_set s nttn nvs
			    in let rs = vR s [s1;s2;s3;s4]
			    in (InAtom(ne, ntvs),rs)
end

module Tfr_no_submodule:tParam = struct

	module NSParam : tRef = struct
	type r = process
	type p = unit
	let creerRef = {
		header = {
			process_name = "";
			signal_declarations = [];
			local_process_list = [];
		};
		body = {
			assignment_list = [];
			constraint_list = [];
			instantiation_list = [];
		};
	}
	let getRef _ = ()
	let setRef _ _ = ()
	let tst _ _= true
	let verifRef _ _ = ()
	end

	include Identite(NSParam)
	let gR = NSParam.getRef
	let sR = NSParam.setRef
	let tR = NSParam.tst

	let rec tfr_process(p:t)=
		let body_without_sub p =
			let get_process name lp =
				let rec local_search name =
					|[] -> failwith(name^" is not defined")
					|p::l ->	if(p.header.process_name = name)
								then p
								else local_search name l
				in try
					gih_get_process name
				with Not_found -> local_search name lp
			and get_signal name declarations =
				let get_s name =
					|[] -> failwith("Signal "^name^" not found\n")
					|d::l ->	if(d.signal_name = name)
								then d
								else get_s name l
				in	get_s name
					((declarations.input_signal_list
					@declarations.output_signal_list)
					@(declarations.local_signal_list))
			and cvrt s i declarations =
					TODO
			and add_sub_list local_processes local_var body = 
				let new_assign lp lv i =
					let p = get_process i.instance_process_name lp
					in
					TODO
				in function
				|[] -> body.assignment_list
				|inst::l ->	(new_assign local_processes local_var inst)
							::(add_sub_list local_processes local_var body l)
			and add_subs_constraints constraints local_processes vars =
				let new_sub_cs lp v i =
					let p = get_process i.instance_process_name lp
					in let new_constraint c c_process_var wanted_var i =
						constraint_kind = c.constraint_kind;
						left_signal_name = cvrt (get_signal c.left_signal_name c_process_var) i c_process_var;
						right_signal_name = cvrt (get_signal c.right_signal_name c_process_var) i c_process_var;
					in match(p.body.constraint_list)with
						|[] -> []
						|c::l -> new_constraint c p.header.signal_declarations v i
				} in function
				|[] -> constraints
				|i::l -> 	(new_sub_cs local_processes vars i)
							::(add_subs_constraints constraints local_processes vars l)
			in {
				assignment_list = 	add_sub_list
										p.header.local_process_list
										p.header.signal_declarations.local_signal_list
										p.body
										p.body.instantiation_list;
				constraint_list =	add_subs_constraints
										p.body.constraint_list
										p.header.local_process_list
										p.header.signal_declarations
										p.body.instantiation_list;
				instantiation_list = [];
		} in {
		header = p.header;
		body = body_without_sub p;
	}
end

let do_transfo prog =
  let module Trans = (*Identite(IdParam)*) Tfr_arith_to_call
  in let module Apply_transfo = Transformation(Trans) 
	in Apply_transfo.transform_spec prog 
