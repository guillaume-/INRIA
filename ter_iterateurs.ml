open Ms_syntax_tree
open SyntaxTree
open Ms_identifier
open Ter_exception

module type tParam = sig
    type t
    val creerT : specification -> t 
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
	in let nvs, s2 = transform_id_set s1 tvs.variant_set
	    in T.tfr_typed_var_set s2 nttn nvs

    let transform_direc s d = T.tfr_direc s d
   
    let transform_sig_decla s sd = 
	let nsn,s1 = transform_id s sd.signal_name 
	in let nst,s2 = transform_id s1 sd.signal_type
	    in let nd,s3 = transform_direc s2 sd.signal_direction
		in T.tfr_sig_decla s3 nsn nst nd
      
   
    let transform_sig_exp s e = T.tfr_sig_exp s e
    
    let transform_assign s a = 
	let nasn,s1 = transform_id s a.assigned_signal_name
	in let nse,s2 = transform_sig_exp s1 a.signal_expression
	    in T.tfr_assign s2 nasn nse

    let transform_sconstr_k s sck = T.tfr_sconstr_k s sck
    
    let transform_sconstr s sc = 
	let nck,s1 = transform_sconstr_k s sc.constraint_kind
	in let nlsn,s2 = transform_id s1 sc.left_signal_name
	    in let nrsn,s3 = transform_id s2 sc.right_signal_name
		in T.tfr_sconstr s3 nck nlsn nrsn
    
    let transform_inst s i = 
	let niie,s1 = List.fold_right (fun e -> fun (r,rs) -> let ne,ns = (transform_sig_exp rs e) in ((ne::r),ns)) i.instance_input_expressions ([],s)
	in let (nios,s2) = List.fold_right (fun o -> fun (r,rs) -> let no,ns = (transform_id rs o) in ((no::r),ns)) i.instance_output_signals ([],s1)
	    in let nipn,s3 = transform_id s2 i.instance_process_name
		    in T.tfr_inst s3 nipn nios niie

      let transform_proc_bd s pbd = 
	let (nal,s1) = List.fold_right (fun a -> fun (r,rs) -> let na,ns = (transform_assign rs a) in (na::r),ns) pbd.assignment_list ([],s)
	in let (ncl,s2) = List.fold_right (fun c -> fun (r,rs) -> let nc,ns = (transform_sconstr rs c) in (nc::r),ns) pbd.constraint_list ([],s1)
	    in let(nil,s3) = List.fold_right (fun i -> fun (r,rs) -> let ni,ns = (transform_inst rs i) in (ni::r),ns) pbd.instantiation_list ([],s2)
		in T.tfr_proc_bd s3 nal ncl nil 
    
      let transform_sig_declas s sds = 
	let (nisl,s1) = List.fold_right (fun i -> fun (r,rs) -> let ni,ns = (transform_sig_decla rs i) in (ni::r),ns) sds.input_signal_list ([],s)
	in let (nosl,s2) = List.fold_right (fun o -> fun (r,rs) -> let no,ns = (transform_sig_decla rs o) in (no::r),ns) sds.output_signal_list ([],s1) 
	    in let (nlsl,s3) = List.fold_right (fun l -> fun (r,rs) -> let nl,ns = (transform_sig_decla rs l) in (nl::r),ns) sds.local_signal_list ([],s2)  
		in T.tfr_sig_declas s3 nisl nosl nlsl
    
      let rec transform_process sa p = 
	let nh,s1 = transform_proc_hd sa p.header
	in let nb,s2 = transform_proc_bd s1 p.body
	    in T.tfr_process s2 nh nb
      and transform_proc_hd sb phd = 
	let (nlpl,s1) = List.fold_right (fun p -> fun (r,rs) -> let np,ns = (transform_process rs p) in (np::r),ns) phd.local_process_list ([],sb)
	in let npn,s2 = transform_id s1 phd.process_name
	    in let sdn,s3 = transform_sig_declas s2 phd.signal_declarations
		in T.tfr_proc_hd s3 npn sdn nlpl

     let transform_proced_decla s pd = 
	let nil,s1 = List.fold_right (fun i -> fun (r,rs) -> let ni,ns = (transform_id rs i) in (ni::r),ns) pd.procedure_input_list ([],s)
	in let npn,s2 = transform_id s1 pd.procedure_name
	    in let npo,s3 = transform_id s2 pd.procedure_output
		in T.tfr_proced_decla s3 npn nil npo
 
     let transform_spec s= 
	let sp = T.creerT s
	    in let npl,s1 = List.fold_right (fun p -> fun (r,rs) -> let np,ns = (transform_process rs p) in (np::r),ns) s.process_list ([],sp)
		in let ntdl,s2 = List.fold_right (fun t -> fun (r,rs) -> let nt,ns = (transform_typed_var_set rs t) in (nt::r),ns) s.type_declaration_list ([],s1)
		    in let npdl,s3 = List.fold_right (fun p -> fun (r,rs) -> let np,ns = (transform_proced_decla rs p) in (np::r),ns) s.procedure_declaration_list ([],s2)
			in let (r,_) = T.tfr_spec s3 npl ntdl npdl in r

end

module type tRef = sig
    type r
    type p 
   
    val creerRef: specification -> r
    val getRef: r -> r
    val setRef: r -> p -> r 
    val tstRef: r -> p -> bool
    val verifRef: r -> r list -> r
    
    val getPart: string -> p

end

module IdParam : tRef = struct
    type r = unit
    type p = unit
    
    let creerRef _ = ()
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

	let creerRef _ = []
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

module Tfr_chk_spec:tParam = struct

type ref = {
	spec : specification ;
	proc_cur : process list;
	exp_types : Identifier.t list;
}

	module CsParam : tRef with type r = ref = struct
		type r = ref
		type p = unit

		let creerRef s = 
			let l = List.rev s.process_list 
			in let loc = List.rev (List.hd l).header.local_process_list 
			in {
				spec = s ;
				proc_cur = loc@l;
				exp_types = [];
		}
		let getRef _ = {
			spec = { 
				process_list = [] ;
				type_declaration_list = [] ;
				procedure_declaration_list = [] ;
			};
			proc_cur = [];
			exp_types = [];
		}
		let setRef _ _ = {
			spec = { 
				process_list = [] ;
				type_declaration_list = [] ;
				procedure_declaration_list = [] ;
			};
			proc_cur = [];
			exp_types = [];
		}
		let tstRef _ _= true
		let verifRef _ _ =  {
			spec = { 
				process_list = [] ;
				type_declaration_list = [] ;
				procedure_declaration_list = [] ;
			};
			proc_cur = [];
			exp_types = [];
		}
		let getPart _ = ()
	end

	include Identite(CsParam)
	let gR = CsParam.getRef
	let sR = CsParam.setRef
	let tR = CsParam.tstRef
	let vR = CsParam.verifRef

	let tfr_proced_decla param name inl out =
	let name_list = List.filter (fun e -> e.procedure_name = name) param.spec.procedure_declaration_list
	in  if List.length name_list > 1
	    then raise (Multiple_definition ("Procedure declaration: "^ name))
	    else if List.exists (fun e -> e.tv_type_name = out) param.spec.type_declaration_list;
		  then let tst_in = List.fold_left 
				    (fun r -> fun id -> (List.exists (fun e -> e.tv_type_name = id) param.spec.type_declaration_list) 
							&& r ) 
				    true inl
			in if tst_in  
			    then ({procedure_name = name; procedure_input_list = inl; procedure_output = out; }, param)
			    else raise (Undefined ("Procedure declaration in " ^name^": Input type undefined")) 
		  else raise (Undefined ("Procedure declaration: Output type in " ^name^": "^out^" undefined")) 
      
    let tfr_typed_var_set param name vs =
	if(List.length (List.filter (fun e -> e.tv_type_name = name) param.spec.type_declaration_list) > 1)
	then raise (Multiple_definition("Typed variant set: "^name))
	else ({tv_type_name = name;variant_set = vs;}, param)

    let tfr_process param hd bd =
	let nproc_cur,loc = if (List.length param.proc_cur) > 1
			then  let n = List.tl param.proc_cur in (n,(List.hd n).header.local_process_list)
			else  let n = param.proc_cur in (n, (List.hd n).header.local_process_list)
	in if List.exists (fun e -> e = List.hd param.proc_cur) loc 
		then ({header = hd; body = bd;}, {spec = param.spec; proc_cur = nproc_cur; exp_types = [];})
		else ({header = hd; body = bd;}, {spec = param.spec; proc_cur = (List.rev loc)@nproc_cur; exp_types = [];})

	let tfr_proc_hd param name sp lpl = 
	let name_list n = List.filter (fun e -> e.header.process_name = n) 
	in let test_rest =
		if List.length (name_list name  param.proc_cur) > 1
		then raise (Multiple_definition ("Local process "^name))
		else  {process_name = name; signal_declarations = sp; local_process_list = lpl;}, param
	in let lgth_process_list = List.length (name_list name param.spec.process_list) 
		in if lgth_process_list > 1
		then raise (Multiple_definition ("Process: "^ name))
		else if lgth_process_list = 1 
				then if List.find (fun e -> e.header.process_name = name) param.spec.process_list != (List.hd param.proc_cur)
					then raise (Multiple_definition ("Process: "^ name))
					else test_rest
				else test_rest

	let tfr_sig_declas t isl osl losl =
	if((List.for_all (fun e -> e.signal_direction = Input) isl)
		&& (List.for_all (fun e -> e.signal_direction = Output) osl)
		&& (List.for_all (fun e -> e.signal_direction = Local) losl))
	then ({input_signal_list = isl;output_signal_list = osl;local_signal_list = losl;}, t)
	else raise (Incompatible_definitions(" in process "^((List.hd t.proc_cur).header.process_name)^", some signals are record in a list that mismatch with the direction"))

	let tfr_sig_decla param sname stype sdir =
	if(List.exists (fun e -> e.tv_type_name = stype) param.spec.type_declaration_list)
	then let p_cur_sd = (List.hd param.proc_cur).header.signal_declarations
		in let filtre = List.filter (fun e -> e.signal_name = sname)
						(p_cur_sd.input_signal_list @ p_cur_sd.output_signal_list @ p_cur_sd.local_signal_list)
		in	if List.length filtre > 1
			then raise (Multiple_definition("Signal declaration: "^sname))
			else ({signal_name = sname; signal_type = stype; signal_direction = sdir;}, param)
	else raise (Undefined("Type "^stype^"at the declaration of"^sname))

	let chk_var t p en =
		let s = try(List.find
					(fun x -> (IdentifierSet.exists (fun y -> y = en) x.variant_set))
					t.spec.type_declaration_list
				)with Not_found -> raise (Undefined(" enum value of "^en))
		in  s.tv_type_name

	let chk_sig t decs sA =
		let s = try( List.find (fun x -> x.signal_name = sA)
						( decs.input_signal_list
						@ decs.output_signal_list
						@ decs.local_signal_list )
				)with Not_found -> (*on adapte l'erreur*)
					let p = (List.hd t.proc_cur) in
					try(ignore (chk_var t p sA);
						raise (Type_mismatch("Signal waited but "^sA^" found as enum"))
					)with Undefined(_) -> raise (Undefined("Signal "^sA))
		in s.signal_type

	let rec chk_exp t =
		let p = try(List.hd t.proc_cur)
				with Failure(_) -> failwith(" call of a check without process")
		in function
		| IntegerConstant(i) ->
			"integer"
		| EnumVariantAtom(e) ->
			chk_var t p e
		| FunctionCall(f, expL) ->
			chk_procedure t expL f
		| InAtom(e, ty) ->
			if(ty.tv_type_name = chk_exp t e)
			then ty.tv_type_name
			else raise (Type_mismatch(" with 'in'"))
		| When(e1, e2) ->
			if((chk_exp t e2) = "boolean")
			then (chk_exp t e1)
			else raise (Type_mismatch(" with 'when' : boolean wanted\n"))
		| AndExp(e1, e2)
		| OrExp(e1, e2) ->
			if(((chk_exp t e1) = "boolean")
			&& (chk_exp t e2) = "boolean")
			then "boolean"
			else raise (Type_mismatch(" with 'and', 'or' : boolean wanted"))
		| Plus(e1, e2)
		| Minus(e1, e2)
		| Times(e1, e2) ->
			if(((chk_exp t e1) = "integer")
			&& (chk_exp t e2) = "integer")
			then "integer"
			else raise (Type_mismatch(" with '+', '-', '*' : integer wanted"))
		| WhenAtom(e)
		| WhenNotAtom(e)
		| NotAtom(e)
		| SignalAtom(e) ->
			chk_sig t p.header.signal_declarations e
		| ClockPlus(e1, e2)
		| ClockMinus(e1, e2)
		| ClockTimes(e1, e2) ->
			ignore (chk_exp t e1);
			(chk_exp t e2)
		| Delay(e1, e2)
		| Default(e1, e2)
		| EqualityAtom(e1, e2) ->
			let t1 = chk_exp t e1 in
			if(t1 = (chk_exp t e2))
			then t1
			else raise (Type_mismatch("Left and right types must be equal in 'delay', 'default' and '='"))
	and chk_procedure t expL f =
		let fdec = List.find (fun x -> x.procedure_name = f) t.spec.procedure_declaration_list
		in	try(if(List.for_all2
						(fun x y -> x = chk_exp t y)
						fdec.procedure_input_list expL
				)then fdec.procedure_output
				else raise (Type_mismatch(" in "^fdec.procedure_name))
			)with Not_found -> raise (Undefined(" procedure "^f))

	let tfr_sig_exp t exp = (exp,{
		spec = t.spec;
		proc_cur = t.proc_cur;
		exp_types = (chk_exp t exp)::t.exp_types;
	})

	let tfr_assign t sNameO sExpI =
		let decs = (List.hd t.proc_cur).header.signal_declarations in
			let s = try List.find
					(fun x -> x.signal_name = sNameO)
					(decs.output_signal_list @ decs.local_signal_list)
					with Not_found -> raise (Undefined(" signal "^sNameO^" in process "^((List.hd t.proc_cur).header.process_name)))
			in let ty = try(List.hd t.exp_types)
						with Failure(_) -> raise (Bad_construction("Assignation without expression defined"))
			in if(ty = s.signal_type)
			then (	{assigned_signal_name=sNameO; signal_expression=sExpI},
					{spec=t.spec; proc_cur=t.proc_cur; exp_types=[];})
			else raise (Type_mismatch("Assignation has Out type "^s.signal_type^", but has for In type "^ty))

	let tfr_sconstr t const_kind sLeft sRight =
		let d = try (List.hd t.proc_cur).header.signal_declarations
				with Failure(_) -> raise (Bad_construction("Constraint call but any current process"))
		in ignore (chk_sig t d sLeft);
		ignore (chk_sig t d sRight);
		({	constraint_kind = const_kind;
			left_signal_name = sLeft;
			right_signal_name = sRight;
		}, t)

	let tfr_inst param ipn ios iie =
		let chk_lgth p_sd = (List.length ios = List.length p_sd.output_signal_list)
							&& (List.length iie = List.length p_sd.input_signal_list)
		and find_t o =	let decs = (List.hd param.proc_cur).header.signal_declarations
		in let sigs = decs.input_signal_list @ decs.output_signal_list @ decs.local_signal_list
		in (List.find (fun e -> e.signal_name = o) sigs ).signal_type
		in let chk_out_types p_sd_o =
			List.fold_left2 (fun r -> fun o -> fun s -> (find_t o = s.signal_type) && r) true ios p_sd_o
		and chk_in_types p_sd_i = List.fold_left2 (fun r -> fun t -> fun s -> (t = s.signal_type) && r) true param.exp_types p_sd_i
		in let chk_in_out p = let pr_sd = p.header.signal_declarations
		in if chk_lgth pr_sd 
			then if chk_out_types pr_sd.output_signal_list 
				then if chk_in_types pr_sd.input_signal_list 
					then ({ instance_process_name = ipn ; instance_output_signals = ios ; instance_input_expressions = iie ;},
							{ spec = param.spec ; proc_cur = param.proc_cur; exp_types = []})
					else raise (Type_mismatch ("Instance "^ipn^" : input types"))
				else raise (Type_mismatch ("Instance "^ipn^" : output types"))
			else raise (Invalide_argument_numbers ("Instance "^ipn))
			in let tst_proc = List.exists (fun e -> e.header.process_name = ipn)  
			in if (tst_proc param.proc_cur) 
			then	let p_ref = List.find (fun e -> e.header.process_name = ipn) param.proc_cur
					in chk_in_out p_ref
			else	if (tst_proc (List.hd param.proc_cur).header.local_process_list)
					then	let p_ref = List.find (fun e -> e.header.process_name = ipn) (List.hd param.proc_cur).header.local_process_list
							in chk_in_out p_ref
					else raise (Undefined("Submodule name: "^ipn))

end

let addCall prog =
	let module Trans = Tfr_arith_to_call
	in let module Apply_transfo = Transformation(Trans) 
	in Apply_transfo.transform_spec prog

let check prog =
	let module Trans = Tfr_chk_spec
	in let module Apply_transfo = Transformation(Trans) 
	in Apply_transfo.transform_spec prog 
