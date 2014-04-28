open Ms_syntax_tree
open SyntaxTree
open Ms_identifier ;;

module type Param = sig
  val tfr_spec:  'a -> process list -> typed_variant_set list -> procedure_declaration list -> specification * 'a
  val tfr_proced_decla:  'a -> Identifier.t -> Identifier.t list -> Identifier.t -> procedure_declaration * 'a
  val tfr_process: 'a -> process_header -> process_body -> process * 'a
  val tfr_proc_hd: 'a -> Identifier.t -> signal_declarations -> process list -> process_header * 'a
  val tfr_sig_declas: 'a -> signal_declaration list -> signal_declaration list -> signal_declaration list -> signal_declarations * 'a
  val tfr_proc_bd: 'a -> assignment list -> sconstraint list -> instantiation list -> process_body * 'a
  val tfr_inst: 'a -> Identifier.t -> Identifier.t list -> signal_expression list -> instantiation * 'a
  val tfr_sconstr: 'a -> sconstraint_kind -> Identifier.t -> Identifier.t -> sconstraint * 'a
  val tfr_sconstr_k: 'a -> sconstraint_kind -> sconstraint_kind * 'a
  val tfr_assign: 'a -> Identifier.t -> signal_expression -> assignment * 'a
  val tfr_sig_exp: 'a -> signal_expression -> signal_expression * 'a
  val tfr_sig_decla: 'a -> Identifier.t -> Identifier.t -> direction -> signal_declaration * 'a
  val tfr_direc: 'a -> direction -> direction * 'a
  val tfr_typed_var_set: 'a -> Identifier.t -> IdentifierSet.t -> typed_variant_set * 'a
  val tfr_identifier: 'a -> Identifier.t -> Identifier.t * 'a
  val tfr_identifier_set:  'a -> IdentifierSet.t -> IdentifierSet.t * 'a
end

module Transformation(P: Param) = struct 
     let verifParam s = 
	let rec vp r = function
	    | [] -> r
	    | e::l -> if r = s 
			then if e != s then vp e l else vp r l
			else if e != r then failwith "maaiiiiis ??" else vp r l
	in vp s

    let transform_id s i = P.tfr_identifier s i
    
    let transform_id_set s is = P.tfr_identifier_set s is (* comment faire pour modifier chaque élément du set ? *)

  
    let transform_typed_var_set s tvs =  
	let nttn, s1 = transform_id s tvs.tv_type_name
	and nvs, s2 = transform_id_set s tvs.variant_set
	in let rs = verifParam s (s1::[s2])
	    in  P.tfr_typed_var_set rs nttn nvs

    let transform_direc s d = P.tfr_direc s d
   
    let transform_sig_decla s sd = 
	let nsn,s1 = transform_id s sd.signal_name 
	and nst,s2 = transform_id s sd.signal_type
	and nd,s3 = transform_direc s sd.signal_direction
	in let rs = verifParam s (s1::s2::[s3])
	    in P.tfr_sig_decla rs nsn nst nd
      
   
    let transform_sig_exp s e = P.tfr_sig_exp s e
    
    let transform_assign s a = 
	let nasn,s1 = transform_id s a.assigned_signal_name
	and nse,s2 = transform_sig_exp s a.signal_expression
	in let rs = verifParam s (s1::[s2])
	    in P.tfr_assign rs nasn nse

    let transform_sconstr_k s sck = P.tfr_sconstr_k s sck
    
    let transform_sconstr s sc = 
	let nck,s1 = transform_sconstr_k s sc.constraint_kind
	and nlsn,s2 = transform_id s sc.left_signal_name
	and nrsn,s3 = transform_id s sc.right_signal_name
	in let rs = verifParam s (s1::s2::[s3])
	    in P.tfr_sconstr rs nck nlsn nrsn
    
    let transform_inst s i = 
	let (niie,ls1) = List.fold_right (fun e -> fun (r,rs) -> let ne,s1 = (transform_sig_exp s e) in ((ne::r),(s1::rs))) i.instance_input_expressions ([],[])
	and (nios,ls2) = List.fold_right (fun o -> fun (r,rs) -> let no,s1 = (transform_id s o) in ((no::r),(s1::rs))) i.instance_output_signals ([],[])
	and nipn,s3 = transform_id s i.instance_process_name
	in let rs = verifParam s (s3::(ls1@ls2))
	    in P.tfr_inst rs nipn nios niie

      let transform_proc_bd s pbd = 
	let (nal,ls1) = List.fold_right (fun a -> fun (r,rs) -> let na,s1 = (transform_assign s a) in (na::r),(s1::rs)) pbd.assignment_list ([],[])
	and (ncl,ls2) = List.fold_right (fun c -> fun (r,rs) -> let nc,s1 = (transform_sconstr s c) in (nc::r),(s1::rs)) pbd.constraint_list ([],[])
	and (nil,ls3) = List.fold_right (fun i -> fun (r,rs) -> let ni,s1 = (transform_inst s i) in (ni::r),(s1::rs)) pbd.instantiation_list ([],[])
	in let rs = verifParam s (ls1@ls2@ls3)
	    in P.tfr_proc_bd rs nal ncl nil 
    
      let transform_sig_declas s sds = 
	let (nisl,ls1) = List.fold_right (fun i -> fun (r,rs) -> let ni,s1 = (transform_sig_decla s i) in (ni::r),(s1::rs)) sds.input_signal_list ([],[])
	and (nosl,ls2) = List.fold_right (fun o -> fun (r,rs) -> let no,s1 = (transform_sig_decla s o) in (no::r),(s1::rs)) sds.output_signal_list ([],[]) 
	and (nlsl,ls3) = List.fold_right (fun l -> fun (r,rs) -> let nl,s1 = (transform_sig_decla s l) in (nl::r),(s1::rs)) sds.local_signal_list ([],[])  
	in let rs = verifParam s (ls1@ls2@ls3)
	    in P.tfr_sig_declas rs nisl nosl nlsl
    
     let rec transform_process s p = 
	let nh,s1 = transform_proc_hd s p.header
	and nb,s2 = transform_proc_bd s p.body
	in let rs1 = verifParam s (s1::[s2])
	    in P.tfr_process rs1 nh nb
     and transform_proc_hd s phd = 
	let (nlpl,ls1) = List.fold_right (fun p -> fun (r,rs) -> let np,s1 = (transform_process s p) in (np::r),(s1::rs)) phd.local_process_list ([],[])
	and npn,s2 = transform_id s phd.process_name
	and sdn,s3 = transform_sig_declas s phd.signal_declarations
	in let rs2 = verifParam s (s3::(s2::ls1))
	    in P.tfr_proc_hd rs2 npn sdn nlpl
	
     let transform_proced_decla s pd = 
	let nil,ls1 = List.fold_right (fun i -> fun (r,rs) -> let ni,s1 = (transform_id s i) in (ni::r),(s1::rs)) pd.procedure_input_list ([],[])
	and npn,s2 = transform_id s pd.procedure_name
	and npo,s3 = transform_id s pd.procedure_output
	in let rs = verifParam s (s3::(s2::ls1))
	    in P.tfr_proced_decla rs npn nil npo
 
     let transform_spec s = 
	let npl,ls1 = List.fold_right (fun p -> fun (r,rs) -> let np,s1 = (transform_process s p) in (np::r),(s1::rs)) s.process_list ([],[])
	and ntdl,ls2 = List.fold_right (fun t -> fun (r,rs) -> let nt,s1 = (transform_typed_var_set s t) in (nt::r),(s1::rs)) s.type_declaration_list ([],[])
	and npdl,ls3 = List.fold_right (fun p -> fun (r,rs) -> let np,s1 = (transform_proced_decla s p) in (np::r),(s1::rs)) s.procedure_declaration_list ([],[])
	in let rs =  verifParam s (ls1@ls2@ls3)
	    in let (r,_) = P.tfr_spec rs npl ntdl npdl in r
end

module Identite:Param = struct
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

    let tfr_sconstr_k s k = (k,s)
    
    let tfr_assign s asn ae = ({
	assigned_signal_name = asn;
	signal_expression = ae;
    },s)
    
    let tfr_sig_exp s e = (e,s)
    
    let tfr_sig_decla s sn st sd = ({
	signal_name = sn;
	signal_type = st;
	signal_direction = sd;
    },s)
    
    let tfr_direc s d = (d,s)
    
    let tfr_typed_var_set s ttn vs = ({
	tv_type_name = ttn;
	variant_set =vs;
    },s)
    
    let tfr_identifier s i = (i,s)
    
    let tfr_identifier_set s st = (st,s)
end

module Tfr_arith_to_call:Param = struct
  include Identite
    let tfr_spec = Identite.tfr_spec

    let tfr_proced_decla = Identite.tfr_proced_decla 

    let tfr_process = Identite.tfr_process

    let tfr_proc_hd = Identite.tfr_proc_hd (*a revoir éventuellement plus tard *)

    let tfr_sig_declas = Identite.tfr_sig_declas (*ok*)

    let tfr_proc_bd = Identite.tfr_proc_bd 

    let tfr_inst = Identite.tfr_inst

    let tfr_sconstr = Identite.tfr_sconstr (*ok*)

    let tfr_sconstr_k  = Identite.tfr_sconstr_k (*ok*)

    let tfr_assign = Identite.tfr_assign

    
    let verifParam s = 
	let rec vp r = function
	    | [] -> r
	    | e::l -> if r = s 
			then if e != s then vp e l else vp r l
			else if e != r then failwith "maaiiiiis ??" else vp r l
	in vp s
	
    let rec tfr_sig_exp s exp =  (*ok*)
	let trait st e1 e2 = 
		let (ne1, s1) = tfr_sig_exp st e1 
		and (ne2, s2) = tfr_sig_exp st e2
		in let rst = verifParam st (s1::[s2])
		    in ne1, ne2, rst
		    
	and chk id res = let pdl = res.procedure_declaration_list
			in if List.exists (fun d -> d.procedure_name = id) pdl
			    then res
			    else ({process_list = res.process_list;
				  type_declaration_list = res.type_declaration_list;
				  procedure_declaration_list = {procedure_name = id;
								procedure_input_list = ["integer";"integer"];
								procedure_output = "integer";}::pdl;
				  })
	in match exp with
		| Plus(e1, e2) -> let (ne1, ne2, rs) = trait s e1 e2
				  in ((FunctionCall("add", [ne1; ne2])) , (chk "add" rs))

		| Minus(e1, e2) ->let (ne1, ne2, rs) = trait s e1 e2
				in  (FunctionCall("sub", [ne1; ne2])) , rs
		| Times(e1, e2) -> let (ne1, ne2, rs) = trait s e1 e2
				in (FunctionCall("mul", [ne1; ne2])) , rs
		
		| ClockPlus(e1, e2) -> let (ne1, ne2, rs) = trait s e1 e2
				in ClockPlus((e1), (e2)) , rs
		| ClockMinus(e1, e2) -> let (ne1, ne2, rs) = trait s e1 e2
				in ClockMinus(ne1, ne2) , rs
		| ClockTimes(e1, e2) -> let(ne1, ne2, rs) = trait s e1 e2
				in ClockTimes(ne1, ne2) , rs
		| Delay (e1, e2) -> let (ne1, ne2, rs) = trait s e1 e2
				in Delay (ne1, ne2) , rs
		| EqualityAtom(e1, e2) -> let (ne1, ne2, rs) = trait s e1 e2
				in EqualityAtom(ne1, ne2) , rs
		| Default(e1, e2) -> let (ne1, ne2, rs) = trait s e1 e2
				in Default(ne1, ne2) , rs
		| When(e1, e2) -> let (ne1, ne2, rs) = trait s e1 e2
				in When(ne1,  ne2) , rs
		| AndExp (e1, e2) -> let (ne1, ne2, rs) = trait s e1 e2
				in AndExp (ne1, ne2) , rs
		| OrExp(e1, e2) -> let (ne1, ne2, rs) = trait s e1 e2
				in OrExp(ne1, ne2)  , rs
		
		(*| FunctionCall(n,el) -> let nel = List.fold_right (fun e -> fun r -> (tfr_sig_exp s e)::r) el []
					in FunctionCall(n, nel)  , s
		| InAtom(e, st) -> InAtom(tfr_sig_exp s e, st) , s*)
		| e -> e,s

    let tfr_sig_decla = Identite.tfr_sig_decla (*ok*)

    let tfr_direc = Identite.tfr_direc (*ok*)

    let tfr_typed_var_set = Identite.tfr_typed_var_set (*ok*)
end

let do_transfo prog =
  let module Apply_transfo = Transformation(Tfr_arith_to_call) in
  Apply_transfo.transform_spec prog