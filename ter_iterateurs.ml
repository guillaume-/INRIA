open Ms_syntax_tree
open SyntaxTree
open Ms_identifier
open Ter_exception
open Ter_util

module type tParam = sig
	type t
	val creerT : specification -> t 
	
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

	let get_param s = 
		let sp = T.creerT s
			in let npl,s1 = List.fold_right (fun p -> fun (r,rs) -> let np,ns = (transform_process rs p) in (np::r),ns) s.process_list ([],sp)
				in let ntdl,s2 = List.fold_right (fun t -> fun (r,rs) -> let nt,ns = (transform_typed_var_set rs t) in (nt::r),ns) s.type_declaration_list ([],s1)
					in let npdl,s3 = List.fold_right (fun p -> fun (r,rs) -> let np,ns = (transform_proced_decla rs p) in (np::r),ns) s.procedure_declaration_list ([],s2)
						in let (_,r) = T.tfr_spec s3 npl ntdl npdl in r
end

module type aParam = sig
	type t
	val creerA : specification -> t 
	
	val apl_spec:  t -> process list -> typed_variant_set list -> procedure_declaration list -> t
	val apl_proced_decla:  t -> Identifier.t -> Identifier.t list -> Identifier.t -> t
	val apl_process: t -> process_header -> process_body -> t
	val apl_proc_hd: t -> Identifier.t -> signal_declarations -> process list -> t
	val apl_sig_declas: t -> signal_declaration list -> signal_declaration list -> signal_declaration list -> t
	val apl_proc_bd: t -> assignment list -> sconstraint list -> instantiation list -> t
	val apl_inst: t -> Identifier.t -> Identifier.t list -> signal_expression list -> t
	val apl_sconstr: t -> sconstraint_kind -> Identifier.t -> Identifier.t -> t
	val apl_sconstr_k: t -> sconstraint_kind -> t
	val apl_assign: t -> Identifier.t -> signal_expression -> t
	val apl_sig_exp: t -> signal_expression -> t
	val apl_sig_decla: t -> Identifier.t -> Identifier.t -> direction -> t
	val apl_direc: t -> direction -> t
	val apl_typed_var_set: t -> Identifier.t -> IdentifierSet.t -> t
	val apl_identifier: t -> Identifier.t -> t
	val apl_identifier_set:  t -> IdentifierSet.t -> t
end

module Application(A: aParam) = struct 
	let apply_id s i = A.apl_identifier s i
	
	let apply_id_set s is = A.apl_identifier_set s is

	let apply_typed_var_set s tvs =  
		let nttn = tvs.tv_type_name
		and nvs = tvs.variant_set
		in  let s1 = apply_id s nttn
			in let s2 = apply_id_set s1 nvs
				in A.apl_typed_var_set s2 nttn nvs

	let apply_direc s d = A.apl_direc s d
   
	let apply_sig_decla s sd = 
		let nsn = sd.signal_name 
		and nst = sd.signal_type
		and nd = sd.signal_direction
		in let s1 = apply_id s nsn
			in let s2 = apply_id s1 nst
				in let s3 = apply_direc s2 nd
				in A.apl_sig_decla s3 nsn nst nd
	  
   
	let apply_sig_exp s e = A.apl_sig_exp s e
	
	let apply_assign s a = 
		let nasn = a.assigned_signal_name
		and nse = a.signal_expression
		in let s1 = apply_id s nasn
			in let s2 = apply_sig_exp s1 nse
				in A.apl_assign s2 nasn nse

	let apply_sconstr_k s sck = A.apl_sconstr_k s sck
	
	let apply_sconstr s sc = 
		let nck = sc.constraint_kind
		and nlsn = sc.left_signal_name
		and nrsn = sc.right_signal_name
		in let s1 = apply_sconstr_k s nck
			in let s2 = apply_id s1 nlsn
				in let s3 = apply_id s2 nrsn
					in A.apl_sconstr s3 nck nlsn nrsn
	
	let apply_inst s i = 
		let niie = i.instance_input_expressions
		and nios = i.instance_output_signals
		and nipn = i.instance_process_name
		in let s1 = List.fold_right (fun e -> fun rs -> let ns = (apply_sig_exp rs e) in ns) niie s
			in let s2 = List.fold_right (fun o -> fun rs -> let ns = (apply_id rs o) in ns) nios s1
				in let s3 = apply_id s2 nipn
					in A.apl_inst s3 nipn nios niie

	let apply_proc_bd s pbd = 
		let nal = pbd.assignment_list
		and ncl = pbd.constraint_list
		and nil = pbd.instantiation_list
		in let s1 = List.fold_right (fun a -> fun rs -> let ns = (apply_assign rs a) in ns) nal s
			in let s2 = List.fold_right (fun c -> fun rs -> let ns = (apply_sconstr rs c) in ns) ncl s1
				in let s3 = List.fold_right (fun i -> fun rs -> let ns = (apply_inst rs i) in ns) nil s2
					in A.apl_proc_bd s3 nal ncl nil 
	
	let apply_sig_declas s sds = 
		let nisl = sds.input_signal_list
		and nosl = sds.output_signal_list
		and nlsl = sds.local_signal_list
		in let s1 = List.fold_right (fun i -> fun rs -> let ns = (apply_sig_decla rs i) in ns) nisl s
			in let s2 = List.fold_right (fun o -> fun rs -> let ns = (apply_sig_decla rs o) in ns) nosl s1
				in let s3 = List.fold_right (fun l -> fun rs -> let ns = (apply_sig_decla rs l) in ns) nlsl s2
					in A.apl_sig_declas s3 nisl nosl nlsl
	
	let rec apply_process sa p = 
		let nh = p.header
		and nb = p.body
		in let s1 = apply_proc_hd sa nh
			in let s2 = apply_proc_bd s1 nb
				in A.apl_process s2 nh nb
	and apply_proc_hd sb phd = 
		let nlpl = phd.local_process_list
		and npn = phd.process_name
		and sdn = phd.signal_declarations
		in let s1 = List.fold_right (fun p -> fun rs -> apply_process rs p) nlpl sb
			in let s2 = apply_id s1 npn
				in let s3 = apply_sig_declas s2 sdn
					in A.apl_proc_hd s3 npn sdn nlpl

	let apply_proced_decla s pd = 
		let nil = pd.procedure_input_list
		and npn = pd.procedure_name
		and npo = pd.procedure_output
		in let s1 = List.fold_right (fun i -> fun rs -> apply_id rs i) nil s
			in let s2 = apply_id s1 npn
				in let s3 = apply_id s2 npo
					in A.apl_proced_decla s3 npn nil npo
 
	let apply_spec s = 
		let sp = A.creerA s
		and npl = s.process_list
		and ntdl = s.type_declaration_list
		and npdl = s.procedure_declaration_list 
			in let s1 = List.fold_right (fun p -> fun rs -> apply_process rs p) npl sp
				in let s2 = List.fold_right (fun t -> fun rs -> apply_typed_var_set rs t) ntdl s1
					in let s3 = List.fold_right (fun p -> fun rs -> apply_proced_decla rs p) npdl s2
						in A.apl_spec s3 npl ntdl npdl
end
