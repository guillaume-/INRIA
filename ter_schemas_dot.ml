open Ms_syntax_tree
open SyntaxTree
open Ms_identifier
open Ter_exception
open Ter_util
open Ter_iterateurs
open Ter_identite
open Ter_toString

	type ref = {res : string ; 
				fathers : (string list) list ;
				l1 : (string*string) list ; l2 : (string*string) list ; l3 : (string*string) list ; l4 : string list ; 
				b : string ; e : string ; 
				decl : string ; 
				lab : (string * string) list ;
				box : bool ;}
	(* 	l1 : liste des signaux en entrée, l2 : liste des signaux en sortie, l3 : liste des signaux locaux/cstes/enum 
		(nom du point , nom du signal )
		l4 : liste des noms de boite (uniques, créés selon les entrées, sorties et label)*)
	
	module SdParam : tRef with type r = ref = struct
		type r = ref
		let creerRef s =
			let init_fathers =
				let rec build_f fathers = function
					|[] -> []
					|e::l -> if(List.length e.header.local_process_list) > 0
							 then	(build_f (e.header.process_name::fathers) (List.rev e.header.local_process_list))
									@[fathers]
									@(build_f fathers l)
							 else (fathers::(build_f fathers l))
				in build_f [] (List.rev s.process_list)
			in {res = "" ; fathers=init_fathers; l1 = [] ; l2 = [] ; l3 = [] ; l4 = [] ; b = "" ; e = "" ; decl = "" ; lab = [] ; box = false}
	end
	
	let setLab param n l = { res = param.res ; fathers = param.fathers ;
							l1 = param.l1 ; l2 = param.l2 ; l3 = param.l3 ;  l4 = param.l4 ;
							b =  param.b ; e =  param.e ; 
							decl = param.decl ; 
							lab = (n,l)::[] ;
							box = param.box}
	
	include Identite(SdParam)
	
	let dot name label =  
		(name ^ " [margin=0,label=\"        " ^ label ^
		"\",shape=circle,style=filled,width=0.05,fillcolor=black,fixedsize=true];\n")
		
	let box name label = name ^ " [margin=0,label=\"" ^ label ^ "\",size=5];\n" 
	
	let inv_link un deux = un ^ "->" ^ deux ^"[len=0.5,width=0,dir=none, style=invisible ];\n" (* style=invisible*)
	
	let link un deux label = un ^ "->" ^ deux ^ " [label=\""^ label ^"\", color=\"blue\", len=1.5];\n"
	let little_link un deux label =  un ^ "->" ^ deux ^ " [label=\""^ label ^"\", color=\"green\", len=1];\n"
	
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
				fathers = (try List.tl param.fathers with _ -> []);
				l1 = [] ; l2 = [] ; l3 = [] ; l4 = [];
				b = "" ; e = "" ;
				decl = "" ; lab = [];
				box = false})
	
	let tfr_proc_hd param pn sd lpl =
		let rec print_pname pn = function
			|[] -> pn
			|e::l -> print_pname (e^"_"^pn) l
		in let name = print_pname pn (List.hd param.fathers)
			in ({process_name = pn ; signal_declarations = sd ; local_process_list = lpl;},
			{ res =  param.res; fathers = param.fathers;
				l1 = param.l1 ; l2 = param.l2 ; l3 = param.l3 ; l4 = param.l4 ;
				b = "digraph "^name^"{\n"^
					"\tgraph [rankdir = LR];\n"^
					"\tnode [shape=record, style=filled];\n"^
					"\tcenter = true \n\n"
					^ param.decl;
				e = "\nlabelloc = \"t\";\n" ^
					"label = \"process : "^ name ^"\"\n"^
					"}\n\n" ;
				decl = "" ; lab = [];
				box = false})

	let tfr_sconstr param ck lsn rsn = 
		let lsnlft = (lsn ^ "lft")
		and rsnrgt = (rsn ^ "rgt")
		and lab = List.hd param.lab
		in let bx = box (snd lab) (fst lab)
			and left = dot lsnlft ""
			and right = dot rsnrgt ""
			and i_l = inv_link (snd lab) lsnlft ^  inv_link (snd lab) rsnrgt
			and all = (param.l1 @ param.l2 @ param.l3)
			in let links = (mk_link_out lsn lsnlft all "") ^
					(mk_link_in rsn rsnrgt all "")
				in ({constraint_kind = ck ; left_signal_name = lsn ; right_signal_name = rsn;},
					{res = param.res; fathers = param.fathers ;
						l1 = param.l1 ;
						l2 = param.l2 ; 
						l3 = param.l3 ;
						l4 = (snd lab)::param.l4 ;
						b = param.b ;
						e =  param.e;
						decl = bx ^ left ^ right ^ param.decl ^ i_l ^ links ;
						lab = [];
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
		let lab = List.hd param.lab
		in let link = if param.box
						then mk_link_out asn (fst lab) (param.l2 @ param.l3) ""
						else mk_link_out asn (fst lab) (param.l2 @ param.l3) ":="
							in ({assigned_signal_name = asn ; signal_expression = ae ; },
								{ res = param.res; fathers = param.fathers ;
									l1 = param.l1 ; l2 = param.l2 ; l3 = param.l3 ; l4 = param.l4 ;
									b = param.b ; e =  param.e;
									decl = param.decl ^ link;
									lab = [];
									box = false})
	
	let tfr_sig_decla param sn st sd = 
		let sp = sn ^ fst (List.hd param.lab)
		in let n_decl = dot (sp) sn 
			in let set_param la lb lc =  
					({ signal_name = sn ; signal_type = st ; signal_direction = sd;},
					{ res = param.res; fathers = param.fathers ;
						l1 = la ; 
						l2 = lb ; 
						l3 = lc ; 
						l4 = param.l4 ;
						b = param.b ; e =  param.e;
						decl = n_decl^param.decl;
						lab = param.lab;
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
		in	{res = param.res; fathers = param.fathers ;
			l1 = param.l1 ; l2 = param.l2 ; 
			l3 = lc ; 
			l4 = param.l4 ;
			b = param.b ; e =  param.e;
			decl = param.decl^s;
			lab = (np,ni)::param.lab;
			box = false}
	
	let crt_var param ni np = if List.exists (fun (np1,ns) -> ns = ni) param.l3
									then let nl3 = param.l3 in set_bx param ni nl3 (nl3) ""
									else let nl3 = (np,ni)::param.l3 
										and n_dot = dot np ni
										in set_bx param ni nl3 (nl3) n_dot
										
	let crt_box param niIn niOut nom label = 
		let dot_in = dot niIn ""
		and dot_out = dot niOut ""
		in let boite = box nom label
			and links = inv_link nom niIn ^ inv_link nom niOut
			in {res = param.res; fathers = param.fathers ;
				l1 = param.l1 ; l2 = param.l2 ; l3 = param.l3 ; 
				l4 = nom::param.l4 ;
				b = param.b ; e =  param.e;
				decl = param.decl^boite^dot_out^dot_in^links;
				lab = (niOut,nom)::param.lab;
				box = true} 
				
	let dot_link nom = List.fold_left (fun (d,lin) -> fun n -> (dot n "")^d, (inv_link nom n)^lin) ("","")
					
	let crt_box_mul param niOut niIn nom label =
		let dot_in,linkIn = dot_link nom niIn
		and dot_out = dot niOut ""
		and boite = box nom label
		in let links = linkIn ^ inv_link nom niOut
			in {res = param.res; fathers = param.fathers ;
				l1 = param.l1 ; l2 = param.l2 ; l3 = param.l3 ; 
				l4 = nom::param.l4 ;
				b = param.b ; e =  param.e;
				decl = param.decl^boite^dot_out^dot_in^links;
				lab = (niOut,nom)::param.lab;
				box = true} 
				
	let crt_box_mul2 param niOut niIn nom label = 
		let boite = box nom label
		and dot_in,linkIn = dot_link nom niIn
		and dot_out,linkOut = dot_link nom niOut
		in {res = param.res; fathers = param.fathers ;
			l1 = param.l1 ; l2 = param.l2 ; l3 = param.l3 ; 
			l4 = nom::param.l4 ;
			b = param.b ; e =  param.e;
			decl = param.decl ^ boite ^ dot_out ^ dot_in ^ linkIn ^ linkOut;
			lab = ("",nom)::param.lab;
			box = true} 
			
	let chg_param param ni niEnum niOut niIn nom label =
		(* Verification de l'existence de boite identique *)
		(*let n_param =*) if List.exists (fun (np) -> np = nom) param.l4
						then param
						else let n_param = crt_box param niIn niOut nom label
		(* Verification de l'existence du point lointain / création du lien *)
		in if List.exists (fun (np,ns) -> ns = ni) param.l3
			then(* let _ = print_string "1 nuuuuuu\n" in*) n_param(*let lien = link niEnum niIn ""
					in {res = n_param.res; fathers = n_param.fathers ;
						l1 = n_param.l1 ; l2 = n_param.l2 ; l3 = n_param.l3 ; l4 = n_param.l4 ;
						b = n_param.b ; e =  n_param.e;
						decl = n_param.decl^lien;
						lab = n_param.lab; box = n_param.box}*)
			else(* let _ = print_string "1 bliiiii\n" in*) let dep = dot niEnum ni
					in let lien = link niEnum niIn ""
					in {res = n_param.res; fathers = n_param.fathers ;
						l1 = n_param.l1 ; l2 = n_param.l2 ; 
						l3 = (niEnum,ni)::n_param.l3 ; 
						l4 = nom::n_param.l4 ;
						b = n_param.b ; e =  n_param.e;
						decl = n_param.decl^dep^lien;
						lab = n_param.lab; box = n_param.box}
						
		
	let rec chg_param2 param e1 e2 exp nom label=
		let enout = str_sig_exp exp
			and enin1 =  "In1" ^ str_sig_exp e1 ^ nom 
			and enin2 = "In2" ^ str_sig_exp e2 ^ nom 
			in let ne1,p1 = tfr_sig_exp param e1
				in let ne2,p2 = tfr_sig_exp p1 e2
					in if List.exists (fun (np) -> np = nom ) p2.l4
						then (*let _ = print_string "2 nuuuuuu\n" in*) ne1, ne2, 
									{res = p2.res; fathers = p2.fathers ;
									l1 = p2.l1 ; l2 = p2.l2 ; 
									l3 = p2.l3 ; l4 = p2.l4 ;
									b = p2.b ; e =  p2.e;
									decl = p2.decl;
									lab = ("",str_sig_exp exp)::p2.lab; box = p2.box}
						else(* let _ = print_string "2 bliiiii\n" in*) let n_param = crt_box_mul p2 (enout^"Out") ((enin1)::[(enin2)]) enout label 
								in let liens = (link (fst (List.hd p1.lab)) enin1 "") ^ (link (fst (List.hd p2.lab)) enin2 "")
									in ne1, ne2, 
									{res = n_param.res; fathers = n_param.fathers ;
									l1 = n_param.l1 ; l2 = n_param.l2 ; 
									l3 = n_param.l3 ; l4 = nom::n_param.l4 ;
									b = n_param.b ; e =  n_param.e;
									decl = n_param.decl^liens;
									lab = n_param.lab; box = n_param.box}
								
	and fct_call e (r_nel,r_p,r_In,i) = 
		let (ne,n_p) = (tfr_sig_exp r_p e) 
		in let nom = ("In"^(string_of_int i)^str_sig_exp ne^"Call")
		in let lien = link (fst (List.hd n_p.lab)) nom ""
			in let n_param = {res = n_p.res; fathers = n_p.fathers ;
								l1 = n_p.l1 ; l2 = n_p.l2 ; l3 = n_p.l3 ; l4 = n_p.l4 ;
								b = n_p.b ; e =  n_p.e;
								decl = n_p.decl^lien;
								lab = n_p.lab; box = n_p.box}
			in (ne::r_nel),n_param,(nom::r_In),(i+1)
		
	and tfr_sig_exp param exp = match exp with
		| FunctionCall(i, el) -> 
			let ni,p1 = tfr_identifier param i
			and origine = str_sig_exp exp
			in let nel,p_tmp,nIn,_ = List.fold_right (fun e -> fun r -> fct_call e r) 
												el ([],p1,[],0)
				in let n_param = if List.exists (fun np -> np = origine) p_tmp.l4
								then p_tmp
								else crt_box_mul p_tmp (origine^"Out") nIn origine ("Call "^i)
				in (FunctionCall(ni,nel),n_param) 
		| SignalAtom(i) -> 
			let ni,_ = tfr_identifier param i 
			in let n_param = set_bx param ni param.l3 (param.l1 @ param.l3 @ param.l2) "" 
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
		| InAtom(e, tvs) -> raise (Undefined "In Atom not defined")
		
	let tfr_inst param ipn ios iie = 
		let all = param.l1@param.l2@param.l3
		and nie = List.fold_left (fun r -> fun e -> (*print_string ("nie : "^(str_sig_exp e)^"\n") ;*) (str_sig_exp e)::r) [] iie
		in let ni,_ = List.fold_left (fun (s,i) -> fun (p,n) -> 
									if List.exists (fun e -> n = e) nie
									then p^(string_of_int i)^"_"^s, i+1
									else s,i)
									("",0) param.lab
			and no,_ = List.fold_left (fun (s,i) -> fun p -> let r,_ = get_node p all in r^(string_of_int i)^"_"^s,i+1) ("",0) ios
			in let nom = "subm"^ipn^"_"^ni^no
				in let niOut,link_out,_ = List.fold_left (fun (l,s,i) -> fun si -> 
										let r,_ = get_node si all
										in let nout = "Out_"^(string_of_int i)^nom^r in (nout)::l, (link nout r "")^s, i+1) ([],"",0) 
										ios
					and niIn,link_in,_ =  List.fold_left (fun (l,s,i) -> fun (p,n) -> (*let _= print_string ("lab : "^p^"  nom : "^ n ^"\n") in*)
										if List.exists (fun e -> n = e) nie
										then let nin = ("In_"^(string_of_int i)^nom^p)in nin::l, (link p nin "")^s, i+1
										else l,s,i) 
										([],"",0)  
										param.lab
					
					in let n_param = crt_box_mul2 param niOut niIn nom ipn
						in ({ instance_process_name = ipn ; instance_output_signals = ios ; instance_input_expressions = iie;},
							{res = n_param.res; fathers = n_param.fathers ;
										l1 = n_param.l1 ; l2 = n_param.l2 ; 
										l3 = n_param.l3 ; 
										l4 = nom::n_param.l4 ;
										b = n_param.b ; e =  n_param.e;
										decl = n_param.decl^link_in^link_out;
										lab = n_param.lab; box = n_param.box})
