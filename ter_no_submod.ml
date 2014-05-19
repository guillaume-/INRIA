open Ms_syntax_tree
open SyntaxTree
open Ms_identifier
open Ter_exception
open Ter_util
open Ter_iterateurs
open Ter_identite

module Tfr_no_submodule = struct 
	type modf = {n_sig : signal_declaration list ; n_bdy : process_body ; n_loc : process list}
	type ref = {spec : specification; proc_cur : process list; modif : modf}

	module NsParam : tRef with type r = ref = struct
		type r = ref

		let creerRef s =
		let rec locaux pr res = (* res rentre valant [] *)
			let local_pr_list = List.rev pr.header.local_process_list in
			if(List.length local_pr_list > 0)
			then locaux (List.hd local_pr_list) ((local_pr_list)@res)
			else res
		in let loc = locaux (List.hd (List.rev s.process_list)) []
		in let nb = {assignment_list = [] ; constraint_list = [] ; instantiation_list = []}
		in let nmod = {n_sig = []; n_bdy = nb; n_loc = []}
		in {spec = s; proc_cur = loc@(List.rev s.process_list); modif = nmod}
	end

	include Identite(NsParam)
	
	let tfr_spec param pl tvs pd =
		let removeLocals p = {
			header = {
				process_name = p.header.process_name;
				signal_declarations = p.header.signal_declarations;
				local_process_list = [];
			};
			body = p.body;
		}
		in ({
			process_list = [removeLocals (List.hd(List.rev pl))];
			type_declaration_list = tvs;
			procedure_declaration_list = pd;
		}, param)
		
let build_currents param ph pb =
		let rec locals p res newStat =
			let tmp_res = (List.rev p.header.local_process_list) 
			in if (List.length p.header.local_process_list)>0
				then locals (List.hd tmp_res) (tmp_res@res) false
				else res, newStat
		in let res, newState =	try(locals (List.hd (List.tl param.proc_cur)) [] true)
								with Failure(_) -> [], true
			in let noconcat = try((List.hd param.proc_cur)
								= List.hd ((List.hd (List.tl param.proc_cur)).header.local_process_list))
								with _ -> true
				in let delMultiples li =
						let rec del res = function
							|[] -> res
							|e::l -> if( try(e = List.hd l)
										with _ -> false )
									then del (e::res) (List.tl l)
									else del (e::res) l
						in del [] (List.rev li)
					in if (noconcat)
						then (List.tl param.proc_cur), newState
						else delMultiples(res@(List.tl param.proc_cur)), newState

	let tfr_process param ph pb = 
		let nproc_cur, newStat = build_currents param ph pb
		in let loc = try (List.hd param.proc_cur).header.local_process_list
					with | Failure(_) -> failwith ("GNIEEEEE "^(string_of_int (List.length nproc_cur)))
			in let dec = ph.signal_declarations
				and modf = param.modif.n_sig
				in let nv_decls = {input_signal_list = dec.input_signal_list ;
									output_signal_list = dec.output_signal_list ;
									local_signal_list = modf@dec.local_signal_list ;}
					in let nv_mod = {n_sig = [] ; 
										n_bdy = {assignment_list = [] ; constraint_list = [] ; instantiation_list = []};
										n_loc = []}
							in let tst_preceds =  List.fold_left (fun r -> fun p -> 
														List.exists (fun e -> e = p) loc )
														true param.proc_cur
								in if tst_preceds
									then let nv_ph = {process_name = ph.process_name ; 
														signal_declarations = nv_decls ; 
														local_process_list = ph.local_process_list (*[]*) ;} 
										in ({header = nv_ph ; body = pb;},
											{spec = param.spec ; proc_cur = nproc_cur; modif = param.modif })
									else let nv_ph = {process_name = ph.process_name ; 
												signal_declarations = nv_decls ; 
												local_process_list = [] ;} 
										in ({header = nv_ph ; body = pb;},
											{spec = param.spec ; proc_cur = nproc_cur ; modif = nv_mod })


(**********************************************************************
	Fonction tfr_inst :
		- trouve le processus de référence (local ou général)
		- créé les associations entre :
				les noms des signaux du process
			et	les signaux/expressions d'appel de l'instantiation
		- créé les signaux locaux si necessaire
			(si existence de sig loc dans le process 
			ou si expression complexe passée en entrée)
		- pour chaque contrainte / assignation / instantiation :
				change le nom de celle ci (partie gauche)
				TODO : remplace chaque signal par son correspondant
					dans l'expression (partie droite)
 **********************************************************************)
	let tfr_inst param ipn ios iie = 
		let pcur_h_ploc = (List.hd param.proc_cur).header.local_process_list
		and declas = (List.hd param.proc_cur).header.signal_declarations
		(* Fonctions utilitaires :  *)
		in let rec create_name env debut = 
					let s = newStr ()
					in if List.exists (fun e -> e=s) env
						then create_name env debut
						else debut^s  (* TODO : verif nom inexistant *)

			and find_name n li = let _,name = try List.find (fun (n1,_) -> n1 = n) li 
												with | Not_found -> failwith ("FAIL : "^n)
												in name

			and gen_loc l env = let name = create_name env "loc_"
							in (l.signal_name, name),{signal_name = name ; signal_type = l.signal_type ; signal_direction = Local}

			and create_loc sref exp env = match exp with
				| EnumVariantAtom(a)
				| SignalAtom(a) -> ([sref.signal_name, a],[],[])
				| IntegerConstant(a) -> ([sref.signal_name,string_of_int a],[],[])
				| _ -> let name = create_name env "sig_"
						in ([sref.signal_name, name],
							[{signal_name = name ; signal_type = sref.signal_type ; signal_direction = Local}],
							[{assigned_signal_name = name ; signal_expression = exp ;}])

			and create_p_loc p env = let n = p.header.process_name
									in if List.exists (fun pl -> pl.header.process_name = n) pcur_h_ploc
										then let name = create_name env "Proc_"
												in let nhd = {process_name = name ; 
															signal_declarations = p.header.signal_declarations ; 
															local_process_list = p.header.local_process_list}
													in (n,name),{header = nhd;
																body = p.body}
										else ((n,n),p)

			and replace_exp param env exp = 
				let rec repl ex =  match ex with
					| WhenAtom(i) -> WhenAtom(find_name i env)
					| WhenNotAtom(i) -> WhenNotAtom(find_name i env)
					| NotAtom(i) -> NotAtom(find_name i env)
					| SignalAtom(i) -> SignalAtom(find_name i env)
					| FunctionCall(i,el) -> 
							let nel = List.map (fun e -> repl e) el
							in if List.exists (fun n -> n.procedure_name = i) param.spec.procedure_declaration_list
								then FunctionCall(i, nel)
								else raise (Undefined ("Procedure name "^i))
					| InAtom (e, s) -> InAtom (repl e, s)
					| ClockPlus (e1, e2) -> ClockPlus (repl e1,repl e2)
					| ClockMinus (e1, e2) -> ClockMinus (repl e1,repl e2)
					| ClockTimes(e1, e2) -> ClockTimes (repl e1,repl e2)
					| Delay (e1, e2) -> Delay (repl e1,repl e2)
					| EqualityAtom (e1, e2) -> EqualityAtom (repl e1,repl e2)
					| Default (e1, e2) -> Default (repl e1,repl e2)
					| When (e1, e2) -> When (repl e1,repl e2)
					| AndExp (e1, e2) -> AndExp (repl e1,repl e2)
					| OrExp (e1, e2) -> OrExp (repl e1,repl e2)
					| Plus (e1, e2) -> Plus (repl e1,repl e2)
					| Minus (e1, e2) -> Minus (repl e1,repl e2)
					| Times (e1, e2) -> Times (repl e1,repl e2)
					| _ -> ex (* EnumVariantAtom et IntegerConstant *)
				in repl exp

			(* Debut fonction tfr_inst : *)
			in let find = List.find (fun p -> p.header.process_name = ipn)
				in let p_ref = try find pcur_h_ploc
								with Not_found -> try find param.proc_cur
													with Not_found -> try find param.modif.n_loc
																		with Not_found -> failwith "ATTENTION, CHECK NON COMPLET !!"
					in let ref_in = p_ref.header.signal_declarations.input_signal_list 
						and ref_out = p_ref.header.signal_declarations.output_signal_list
						and ref_loc = p_ref.header.signal_declarations.local_signal_list 
						and ref_proc_loc = p_ref.header.local_process_list
						and ref_assign = p_ref.body.assignment_list 
						and ref_inst = p_ref.body.instantiation_list
						and ref_cstr = p_ref.body.constraint_list
						and env0 = List.map (fun o -> o.signal_name) declas.output_signal_list  
									@ List.map (fun i -> i.signal_name) declas.input_signal_list 
									@ List.map (fun l -> l.signal_name) declas.local_signal_list 
						(* Ordre des associations : reférent,actuel *)
						in let assoc_name_out = List.fold_left2 (fun r -> fun out_s -> fun out_r ->
																(out_r.signal_name,out_s)::r)
																[] ios ref_out
							and (assoc_name_in,cr_s,cr_a) = List.fold_left2 (fun (ran,rs,ra) -> fun in_e -> fun in_sr -> 
																		let (nan,ns,na) = create_loc in_sr in_e (env0) in nan@ran,ns@rs,na@ra)
																		([],[],[]) iie ref_in
							in let env1 = List.fold_left (fun r -> fun s -> s.signal_name::r) env0 cr_s
								in let (assoc_name_loc,cr_loc) = List.fold_left (fun (ran,rloc) -> fun loc_s -> 
																			let (nan,nloc) = gen_loc loc_s (env1) in nan::ran,nloc::rloc ) 
																			([],[]) ref_loc
									and env3 = List.map (fun p -> p.header.process_name) pcur_h_ploc
									in let(assoc_proc_loc, cr_pr) = List.fold_left (fun (rpl,rpc) -> fun p -> 
																					let (npl,npc) = create_p_loc p (env3) in npl::rpl,npc::rpc)
																					([],[]) ref_proc_loc
										in let assoc_name = assoc_name_out @ assoc_name_in @ assoc_name_loc
											in let nv_a = List.fold_left (fun r -> fun a -> 
																	{assigned_signal_name = find_name a.assigned_signal_name assoc_name ; 
																	signal_expression = replace_exp param assoc_name a.signal_expression;}::r ) 
																	[] ref_assign
												and nv_c = List.fold_left (fun r -> fun c ->
																		{constraint_kind = c.constraint_kind ; 
																		left_signal_name = (find_name c.left_signal_name assoc_name) ; 
																		right_signal_name = (find_name c.right_signal_name assoc_name) ;}::r)
																		[] ref_cstr
												and nv_i = List.fold_left (fun r -> fun i ->
																		{instance_process_name = find_name i.instance_process_name assoc_proc_loc ;
																		instance_output_signals = List.map (fun o -> find_name o assoc_name) 
																											i.instance_output_signals;
																		instance_input_expressions = 
																				List.fold_left (fun re -> fun e -> (replace_exp param assoc_name e)::re) 
																								[] i.instance_input_expressions;}::r)
																		[] ref_inst

							in let nsig = cr_s @ cr_loc @ param.modif.n_sig
								and n_nv_i = (List.filter (fun i -> i.instance_process_name != ipn )param.modif.n_bdy.instantiation_list) @ nv_i
								in let nbdy = { assignment_list = cr_a @ nv_a @ param.modif.n_bdy.assignment_list; 
												constraint_list = nv_c @ param.modif.n_bdy.constraint_list ; 
												instantiation_list = n_nv_i} 
									and n_cr_pr = (List.filter (fun p -> p.header.process_name != ipn) param.modif.n_loc ) @ cr_pr
									in let modf = {n_sig = nsig ; n_bdy = nbdy ; n_loc = n_cr_pr }
										in let nv_param = {spec = param.spec ; 
															proc_cur = param.proc_cur; 
															modif = modf;}
											in ({ instance_process_name = "vide"^ipn;
												instance_output_signals = ios ;
												instance_input_expressions = iie ;} , nv_param)


	let transform_inst param i = tfr_inst param i.instance_process_name i.instance_output_signals i.instance_input_expressions


	let tfr_proc_bd gparam gal gcl gil =
		let rec no_multiple_out_define = function
			|[] -> []
			|e::l ->	if(List.exists (fun x -> x.assigned_signal_name 
										= e.assigned_signal_name) l)
						then no_multiple_out_define l
						else e::(no_multiple_out_define l)
		in let rec t_proc_bd param al cl il =
			let nal = param.modif.n_bdy.assignment_list
			and ncl = param.modif.n_bdy.constraint_list
			and nil = param.modif.n_bdy.instantiation_list
			and nloc = param.modif.n_loc
			and nsig = param.modif.n_sig
			in(* (print_string ("Test: \n"^Ter_toString.str_assignment al));*)
				if nil = []
				then ({ assignment_list = no_multiple_out_define (nal@gal) ;
						constraint_list = ncl@gcl ;
						instantiation_list = nil ;},param) 
				else 
					let cur = List.hd param.proc_cur
					in let n_sd = let c_sd = cur.header.signal_declarations
									in {input_signal_list = c_sd.input_signal_list ;
										output_signal_list = c_sd.output_signal_list;
										local_signal_list = nsig @ c_sd.local_signal_list;}
						and tl = List.tl param.proc_cur
						in let n_hd = { process_name = cur.header.process_name ; 
											signal_declarations = n_sd ;
											local_process_list = nloc }
							in let n_cur = {header = n_hd ; body = cur.body ;}
								in let npar = {spec = param.spec; proc_cur = n_cur::tl; modif = param.modif;}
									in let n_il,n_param = List.fold_right (fun i -> fun (r,rp) -> let ni,np = (transform_inst rp i) in (ni::r),np) nil ([],npar)
										in t_proc_bd n_param nal ncl n_il
		in t_proc_bd gparam gal gcl gil

end
