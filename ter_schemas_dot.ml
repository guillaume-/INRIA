open Ms_syntax_tree
open SyntaxTree
open Ms_identifier
open Ter_exception
open Ter_util
open Ter_iterateurs
open Ter_identite
open Ter_toString

	type ref = {res : string ; 
				l1 : (string*string) list ; l2 : (string*string) list ; l3 : (string*string) list ; l4 : (string*string) list ; 
				b : string ; e : string ; 
				decl : string ; 
				lab : string * string ;
				box : bool ;}
	(* 	l1 : liste des signaux en entrée, l2 : liste des signaux en sortie, l3 : liste des signaux locaux/cstes/enum
		l2 : list des points d'entrée de boite
		(nom du point , nom du signal )*)
	
	module SdParam : tRef with type r = ref = struct
		type r = ref
		let creerRef s = {res = "" ; l1 = [] ; l2 = [] ; l3 = [] ; l4 = [] ; b = "" ; e = "" ; decl = "" ; lab = "","" ; box = false}
	end
	
	let setLab param n l = { res = param.res ; 
							l1 = param.l1 ; l2 = param.l2 ; l3 = param.l3 ;  l4 = param.l4 ;
							b =  param.b ; e =  param.e ; 
							decl = param.decl ; 
							lab = (n,l) ;
							box = param.box}
	
	include Identite(SdParam)
	
	let dot name label =  
		(name ^ " [margin=0,label=\"        " ^ label ^
		"\",shape=circle,style=filled,width=0.05,fillcolor=black,fixedsize=true];\n")
		
	let box name label = name ^ " [margin=0,label=\"" ^ label ^ "\",size=5];\n" 
	
	let inv_link un deux = un ^ "->" ^ deux ^"[len=0.5,width=0,dir=none,style=invisible];\n"
	
	let link un deux label = un ^ "->" ^ deux ^ " [label=\""^ label ^"\", color=\"blue\", len=1.5];\n"
	
	let get_node s li = try List.find (fun (np,ns) -> ns = s) li with |Not_found -> failwith ("pas trouvé :" ^ s)
	
	let mk_link_out s sp li label =
		let r,_ = get_node s li 
					in link sp r label
					
	let mk_link_in s sp li label =
		let r,_ = get_node s li 
					in link r sp label
	
	let tfr_process param ph pb = 
		({header = ph; body = pb;},
			{ res = param.b^param.decl^param.e ^"\n"^ param.res; 
				l1 = [] ; l2 = [] ; l3 = [] ; l4 = [];
				b = "" ; e = "" ;
				decl = "" ; lab = "","";
				box = false})
	
	let tfr_proc_hd param pn sd lpl = 
		({process_name = pn ; signal_declarations = sd ; local_process_list = lpl;},
		{ res =  param.res; 
			l1 = param.l1 ; l2 = param.l2 ; l3 = param.l3 ; l4 = param.l4 ;
			b = "digraph "^pn^"{\n"^
				"\tgraph [rankdir = LR];\n"^
				"\tnode [shape=record, style=filled];\n"^
				"\tcenter = true \n\n"
				^ param.decl;
			e = "\nlabelloc = \"t\";\n" ^
				"label = \"process : "^ pn ^"\"\n"^
				"}\n\n" ;
			decl = "" ; lab = "","";
			box = false})

	let tfr_sconstr param ck lsn rsn = 
		let lsnlft = (lsn ^ "lft")
		and rsnrgt = (rsn ^ "rgt")
		in let bx = box (snd param.lab) (fst param.lab)
			and left = dot lsnlft lsn 
			and right = dot rsnrgt rsn
			and i_l = inv_link (snd param.lab) lsnlft ^  inv_link (snd param.lab) rsnrgt
			and all = (param.l1 @ param.l2 @ param.l3)
			in let links = (mk_link_out lsn lsnlft all "truc") ^
					(mk_link_in rsn rsnrgt all "chose")
				in ({constraint_kind = ck ; left_signal_name = lsn ; right_signal_name = rsn;},
					{res = param.res; 
						l1 = param.l1 ;
						l2 = param.l2 ; 
						l3 = param.l3 ;
						l4 = param.l4 ;
						b = param.b ;
						e =  param.e;
						decl = bx ^ left ^ right ^ param.decl ^ i_l ^ links ;
						lab = "","";
						box = false})

	let tfr_sconstr_k param = function
		ClockEquality -> 
				(ClockEquality, setLab param "^=" "ClE")
		| ClockLeq  -> 
				(ClockLeq, setLab param "^<=" "ClLE")
		| ClockLess -> 
				(ClockLess, setLab param "^<" "ClL")
		| ClockWhen -> 
				(ClockWhen, setLab param "^= when" "ClW")
		| ClockWhenNot -> 
				(ClockWhenNot, setLab param "^= when not" "ClWN")
		| ClockExclusive -> 
				(ClockExclusive, setLab param "^#" "ClX")

	let tfr_assign param asn ae = 
		let link = if param.box 
		then mk_link_out asn (fst param.lab) (param.l2 @ param.l3) ""
		else mk_link_out asn (fst param.lab) (param.l2 @ param.l3) ":="
			in ({assigned_signal_name = asn ; signal_expression = ae ; },
				{ res = param.res; 
					l1 = param.l1 ; l2 = param.l2 ; l3 = param.l3 ; l4 = param.l4 ;
					b = param.b ; e =  param.e;
					decl = param.decl ^ link;
					lab = "","";
					box = false})

	
	let tfr_sig_decla param sn st sd = 
		let sp = sn ^ fst param.lab
		in let n_decl = dot (sp) sn 
			in let set_param la lb lc =  
					({ signal_name = sn ; signal_type = st ; signal_direction = sd;},
					{ res = param.res; 
						l1 = la ; 
						l2 = lb ; 
						l3 = lc ; 
						l4 = param.l4 ;
						b = param.b ;
						e =  param.e;
						decl = n_decl^param.decl;
						lab = "","";
						box = false})
				in match sd with 
					| Input -> set_param ((sp,sn)::param.l1) (param.l2) (param.l3)
					| Output -> set_param (param.l1) ((sp,sn)::param.l2) (param.l3)
					| Local -> set_param (param.l1) (param.l2) ((sp,sn)::param.l3)

	let tfr_direc param = function
		Input -> (Input, setLab param "In" "")
		| Output -> (Output, setLab param "Out" "")
		| Local -> (Local, setLab param "W" "")
		
	let set_bx param ni lc li s = 
		let np,_ = get_node ni li
		in	{res = param.res; 
			l1 = param.l1 ; l2 = param.l2 ; 
			l3 = lc ; 
			l4 = param.l4 ;
			b = param.b ; e =  param.e;
			decl = param.decl^s;
			lab = np,"";
			box = false}
	
	let crt_var param ni np = if List.exists (fun (np1,ns) -> ns = ni) param.l3
									then let nl3 = param.l3 in set_bx param ni nl3 (nl3) ""
									else let nl3 = (np,ni)::param.l3 
										and n_dot = dot np ni
										in set_bx param ni nl3 (nl3) n_dot
										
	let crt_box param ni niIn niOut nom label = 
		let dot_in = dot niIn ""
		and dot_out = dot niOut ""
		in let boite = box nom label
			and links = inv_link nom niIn ^ inv_link nom niOut
			in {res = param.res; 
				l1 = param.l1 ; 
				l2 = param.l2 ; 
				l3 = param.l3 ; 
				l4 = (niIn,ni)::(niOut,ni)::param.l4 ;
				b = param.b ;
				e =  param.e;
				decl = param.decl^boite^dot_out^dot_in^links;
				lab = niOut,"";
				box = true} 
					
	let crt_box_mul param ni niOut niIn nom label =
		let dot_in,linkIn,li = List.fold_left (fun (d,lin,l) -> fun n -> (dot n "")^d, (inv_link nom n)^lin,(n,ni)::l) ("","",[]) niIn
		and dot_out = dot niOut ""
		in let boite = box nom label
			and links = linkIn ^ inv_link nom niOut
			in {res = param.res; 
				l1 = param.l1 ; 
				l2 = param.l2 ; 
				l3 = param.l3 ; 
				l4 = li@param.l4 ;
				b = param.b ;
				e =  param.e;
				decl = param.decl^boite^dot_out^dot_in^links;
				lab = niOut,"";
				box = true} 
			
	let chg_param param ni niEnum niOut niIn nom label =
		(* Verification de l'existence de boite identique *)
		let n_param = if List.exists (fun (np,ns) -> np = niIn) param.l4
						then param
						else crt_box param ni niIn niOut nom label
		(* Verification de l'existence du point lointain / création du lien *)
		in if List.exists (fun (np,ns) -> ns = ni) param.l3
			then let lien = link niEnum niIn ""
					in {res = n_param.res; 
						l1 = n_param.l1 ; l2 = n_param.l2 ; l3 = n_param.l3 ; l4 = n_param.l4 ;
						b = n_param.b ; e =  n_param.e;
						decl = n_param.decl^lien;
						lab = n_param.lab; box = n_param.box}
			else let dep = dot niEnum ni
					in let lien = link niEnum niIn ""
					in {res = n_param.res; 
						l1 = n_param.l1 ; l2 = n_param.l2 ; 
						l3 = (niEnum,ni)::n_param.l3 ; 
						l4 = n_param.l4 ;
						b = n_param.b ; e =  n_param.e;
						decl = n_param.decl^dep^lien;
						lab = n_param.lab; box = n_param.box}
						
	let rec chg_param2 param e1 e2 exp nom label=
		let enout = str_sig_exp exp
			and enin1 =  "In1" ^ str_sig_exp e1 ^ nom 
			and enin2 = "In2" ^ str_sig_exp e2 ^ nom 
			in let ne1,p1 = tfr_sig_exp param e1
				in let ne2, p2 = tfr_sig_exp p1 e2
					in let n_param = if List.exists (fun (np,ns) -> np = enout^"Out" ) p2.l4
										then p2
										else crt_box_mul p2 enout (enout^"Out") (enin1::[enin2]) enout label
						in(* print_string ("Ici : >"^(fst p1.lab)^"<\n");*) let liens = (link (fst p1.lab) enin1 "") ^ (link (fst p2.lab) enin2 "")
							in ne1, ne2, 
								{res = n_param.res; 
								l1 = n_param.l1 ; l2 = n_param.l2 ; 
								l3 = n_param.l3 ; l4 = n_param.l4 ;
								b = n_param.b ; e =  n_param.e;
								decl = n_param.decl^liens;
								lab = n_param.lab; box = n_param.box}
		
	and tfr_sig_exp param exp = match exp with
		| SignalAtom(i) -> 
			let ni,_ = tfr_identifier param i 
			in let n_param = set_bx param ni param.l3 (param.l1 @ param.l3) "" 
				in (SignalAtom(ni), n_param)
		| EnumVariantAtom(i) -> 
			let ni,_ = tfr_identifier param i
			in let enum = ni^"Enum"
				in let n_param = crt_var param ni enum 
					in (EnumVariantAtom(ni), n_param)
		| IntegerConstant(i) -> 
			let ni = string_of_int i
			in let cst = "Cst"^ni
				in let n_param = crt_var param ni cst
						in (IntegerConstant(i),n_param) 
		| WhenAtom(i) -> 
			let ni,_ = tfr_identifier param i
			in let enum = ni^"Enum"
				and enin = ni^"WhAtIn"
				and enout = ni^"WhAtOut"
					in let n_param = chg_param param ni enum enout enin "WhenAtom" "When" 
						in (WhenAtom(ni),n_param)
		| NotAtom(i) -> 
			let ni,_ = tfr_identifier param i
			in let enum = ni^"Enum"
				and enin = ni^"NAtIn"
				and enout = ni^"NAtOut"
					in let n_param = chg_param param ni enum enout enin "NotAtom" "Not"
			in (NotAtom(ni),n_param)
		| WhenNotAtom(i) -> 
			let ni,_ = tfr_identifier param i
			in let enum = ni^"Enum"
				and enin = ni^"WhNAtIn"
				and enout = ni^"WhNAtOut"
				in let n_param = chg_param param ni enum enout enin "WhenNotAtom" "When not"
					in (WhenNotAtom(ni),n_param)

		
		| Plus(e1, e2) -> 
			let ne1, ne2, n_param = chg_param2 param e1 e2 exp "Plus" "+"
							in (Plus(ne1, ne2),n_param)
						
		| Minus(e1, e2) -> 
			let ne1, ne2, n_param = chg_param2 param e1 e2 exp "Minus" "-"
			in  (Minus(ne1, ne2),n_param)
		| Times(e1, e2) -> 
			let ne1, ne2, n_param = chg_param2 param e1 e2 exp "Times" "*"
			in (Times(ne1, ne2),n_param)
		| ClockPlus(e1, e2) -> 
			let ne1, ne2, n_param = chg_param2 param e1 e2 exp "ClPlus" "^+"
			in (ClockPlus(ne1, ne2),n_param)
		| ClockMinus(e1, e2) -> 
			let ne1, ne2, n_param = chg_param2 param e1 e2 exp "ClMinus" "^-"
			in (ClockMinus(ne1, ne2),n_param)
		| ClockTimes(e1, e2) -> 
			let ne1, ne2, n_param = chg_param2 param e1 e2 exp "ClTimes" "^*"
			in (ClockTimes(ne1, ne2),n_param)
		| Delay(e1, e2) -> 
			let ne1, ne2, n_param = chg_param2 param e1 e2 exp "Delay" "Delay"
			in (Delay(ne1, ne2),n_param)
		| EqualityAtom(e1, e2) -> 
			let ne1, ne2, n_param = chg_param2 param e1 e2 exp "Equality" "="
			in (EqualityAtom(ne1,ne2),n_param)
		| Default(e1, e2) -> 
			let ne1, ne2, n_param = chg_param2 param e1 e2 exp "Default" "Default"
			in (Default(ne1, ne2),n_param)
		| When(e1, e2) -> 
			let ne1, ne2, n_param = chg_param2 param e1 e2 exp "When" "When"
			in (When(ne1, ne2),n_param)
		| AndExp(e1, e2) -> 
			let ne1, ne2, n_param = chg_param2 param e1 e2 exp "And" "And" 
			in (AndExp(ne1, ne2),n_param)
		| OrExp(e1, e2) -> 
			let ne1, ne2, n_param = chg_param2 param e1 e2 exp  "Or" "Or"
			in (OrExp(ne1, ne2),n_param)
		| FunctionCall(i, el) -> 
			let ni,_ = tfr_identifier param i
			and nel = List.fold_right (fun e -> fun r -> let (ne,_) = (tfr_sig_exp param e) in (ne::r)) el []
			in (FunctionCall(ni,nel),param) 
		| InAtom(e, tvs) ->  
			let ne,_ = tfr_sig_exp param e
			and nttn,_ = tfr_identifier param tvs.tv_type_name
			and nvs,_ = tfr_identifier_set param tvs.variant_set
			in  let ntvs,_ = tfr_typed_var_set param nttn nvs
				in (InAtom(ne, ntvs),param)

	(*	let tfr_proc_bd param al cl il = ({
		assignment_list = al ;
		constraint_list = cl;
		instantiation_list = il;
		} ,param)*)
		
	(*let tfr_identifier param i = (i,param)

	let tfr_identifier_set param is = 
		let nis = IdentifierSet.fold (fun e -> fun r -> let ne,_ = (tfr_identifier param e) in (IdentifierSet.add ne r)) is IdentifierSet.empty
		in (nis,param)

	let tfr_typed_var_set param ttn vs = ({
		tv_type_name = ttn;
		variant_set =vs;
		},param)

	let tfr_inst param ipn ios iie = ({
		instance_process_name = ipn;
		instance_output_signals = ios;
		instance_input_expressions = iie;
		},param) *)
