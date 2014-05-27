open Ms_syntax_tree
open SyntaxTree
open Ms_identifier
open Ter_exception
open Ter_util
open Ter_iterateurs
open Ter_identite_p

	type tStr_tree = {
		pro_dec : string ; proc : string ; proc_hd : string * string;
		sig_decls : string * string * string ; proc_bd : string ; inst : string ;
		constr : string ; constr_k : string ; assign : string ;
		id : string list; id_set : string ; typ_var_set : string ;
		exp : string list; sig_decl : string list ;(* dir : string;*)
		proc_loc : string list
	}
	
	let treeVide = {
		pro_dec = "" ; proc = "" ; proc_hd = "","";
		sig_decls = "","","" ; proc_bd = "" ; inst = "";
		constr = "" ; constr_k = ""; assign = "";
		id = [] ; id_set = "" ; typ_var_set = "";
		exp = [] ; sig_decl = [] ; (*dir = ""; *)
		proc_loc = []}
		
	let treeId i = {
		pro_dec = "" ; proc = "" ; proc_hd = "","";
		sig_decls = "","","" ; proc_bd = "" ; inst = "";
		constr = "" ; constr_k = ""; assign = "";
		id = i::[] ; id_set = "" ; typ_var_set = "";
		exp = [] ; sig_decl = [] ; (*dir = ""; *)
		proc_loc = []
	}
	
	type refS = {str : string; tree : tStr_tree ; fathers : string list list}
	let creerRefVide = {str = ""; tree = treeVide ; fathers = []}
	let creerRefHd hd li = let dads =
		let rec build_f fathers = function
			| [] -> []
			| e::l -> if(List.length e.header.local_process_list) > 0
							 then	(build_f (e.header.process_name::fathers) (List.rev e.header.local_process_list))
									@[fathers]
									@(build_f fathers l)
							 else (fathers::(build_f fathers l))
		in build_f li (List.rev hd.local_process_list)
	in {str = ""; tree = treeVide ; fathers = dads}

module Apl_to_string : aParam with type t = refS = struct

	module TsParam:tRef with type r = refS = struct
		type r = refS
		let creerRef s = let init_fathers =
				let rec build_f fathers = function
					|[] -> []
					|e::l -> if(List.length e.header.local_process_list) > 0
							 then	(build_f (e.header.process_name::fathers) (List.rev e.header.local_process_list))
									@[fathers]
									@(build_f fathers l)
							 else (fathers::(build_f fathers l))
				in build_f [] (List.rev s.process_list)
			in {str = ""; tree = treeVide ; fathers = init_fathers}
		
	end
	
	
	include Identite(TsParam)
	
	let hd_tl l = (try List.hd l with | _ -> failwith "mééé"), try List.tl l with | _ -> []
	
	let rec str_id_list = function
			| [] -> ""
			| n::[] -> n
			| e::l -> let r = str_id_list l in e^", "^r
	
	let apl_spec s pl tdl pdl = 
		let t = s.tree
		in {str = t.typ_var_set ^"\n"^ t.pro_dec ^"\n"^ t.proc ; tree = t ; fathers = s.fathers}
	
	let apl_identifier s i = 
		let t = s.tree
		in let id = i
			in {
				str = id ; 
				tree = {
					pro_dec = t.pro_dec; proc = t.proc ; proc_hd = t.proc_hd;
					sig_decls = t.sig_decls ; proc_bd = t.proc_bd ; inst = t.inst;
					constr = t.constr ; constr_k = t.constr_k; assign = t.assign;
					id = id :: t.id ; 
					id_set = t.id_set ; typ_var_set = t.typ_var_set;
					exp = t.exp ; sig_decl = t.sig_decl ; (* dir = t.dir; *)
					proc_loc = t.proc_loc} ;
				fathers = s.fathers
				}
				
	let apl_typed_var_set s ttn vs =
		let t = s.tree
			in let rec str_typed_variant_list = function
					| [] -> ""
					| e::[] -> e
					| e:: l -> e^", "^(str_typed_variant_list l)
				in let fin = match (IdentifierSet.elements vs) with
							|[] -> ";\n"
							| l ->" = enum (" ^ (str_typed_variant_list (IdentifierSet.elements vs)) ^ ");\n"
					and name = try List.hd t.id with |_ -> failwith "1"
						in let var_set = "type " ^ name ^ fin
							in {
									str = var_set ; 
									tree = {
										pro_dec = t.pro_dec; 
										proc = t.proc ; proc_hd = t.proc_hd;
										sig_decls = t.sig_decls ; proc_bd = t.proc_bd ; inst = t.inst;
										constr = t.constr ; constr_k = t.constr_k; assign = t.assign;
										id = [] ; id_set = t.id_set ; typ_var_set = var_set ^ t.typ_var_set;
										exp = t.exp ; sig_decl = t.sig_decl ; (* dir = t.dir; *)
										proc_loc = t.proc_loc 
									} ;
									fathers = s.fathers ;
								}

	let apl_proced_decla s pn pi po = 
		let t = s.tree
			in let res,tl1 = hd_tl t.id
				in let name,tl2 = hd_tl tl1
				in let p = str_id_list tl2
					in let proced_decl = 
							"procedure "  ^ name ^ 
							
							" (" ^p^ ") -> " ^ res ^ ";\n" 
						in {
							str = proced_decl ; 
							tree = {
									pro_dec = proced_decl ^ t.pro_dec; 
									proc = t.proc ; proc_hd = t.proc_hd;
									sig_decls = t.sig_decls ; proc_bd = t.proc_bd ; inst = t.inst;
									constr = t.constr ; constr_k = t.constr_k; assign = t.assign;
									id = [] ; id_set = t.id_set ; typ_var_set = t.typ_var_set;
									exp = t.exp ; sig_decl = t.sig_decl ; (* dir = t.dir; *)
									proc_loc = t.proc_loc 
								} ;
							fathers = s.fathers 
							}
	
	let apl_process s ph pb = 
		let t = s.tree
		in let process = (fst t.proc_hd) ^ t.proc_bd ^ (snd t.proc_hd)
			in if (try List.hd s.fathers with |_ -> []) = []
				then {
					str = process ; 
					tree = {
						pro_dec = t.pro_dec; 
						proc = process ^ "\n" ^ t.proc ; proc_hd = "","";
						sig_decls = t.sig_decls ; proc_bd = "" ; inst = t.inst;
						constr = t.constr ; constr_k = t.constr_k; assign = t.assign;
						id = [] ; id_set = t.id_set ; typ_var_set = t.typ_var_set;
						exp = t.exp ; sig_decl = t.sig_decl ; (* dir = t.dir; *)
						proc_loc = []
						} ;
					fathers = try List.tl s.fathers with |_ -> []
					}
				else{
					str = process ; 
					tree = {
						pro_dec = t.pro_dec; 
						proc = t.proc ; proc_hd = "","";
						sig_decls = t.sig_decls ; proc_bd = t.proc_bd ; inst = t.inst;
						constr = t.constr ; constr_k = t.constr_k; assign = t.assign;
						id = [] ; id_set = t.id_set ; typ_var_set = t.typ_var_set;
						exp = t.exp ; sig_decl = t.sig_decl ; (* dir = t.dir; *)
						proc_loc = process :: t.proc_loc 
						} ;
					fathers = List.tl s.fathers 
					}
	
	let apl_proc_hd s pn sd lpl = 
		let rec locals loc = function
			| [] -> false, "", loc
			| _::l -> let hd,tl = (if loc = []
						then "",[]
						else hd_tl loc)
							in let _,r,rl = locals tl l in true, hd ^ r, rl
		in let t = s.tree
			in let sig_in,sig_out,sig_loc = t.sig_decls
				in let header = "process " ^ (try List.hd t.id with | _ -> failwith "3") ^ " = " ^
				"(\n" ^ sig_in ^ sig_out ^ ")\n" 
					and b,p_loc,r_loc = locals t.proc_loc lpl
					in let whr = if  b || not (sig_loc = "")
									then "where "
									else ""
						in let footer = whr ^ p_loc ^ sig_loc ^"end;\n"
							in {
								str = header ; 
								tree = {
									pro_dec = t.pro_dec; proc = t.proc ; 
									proc_hd = header,footer ;
									sig_decls = "","","" ;
									proc_bd = t.proc_bd ; inst = t.inst;
									constr = t.constr ; constr_k = t.constr_k; assign = t.assign;
									id = [] ; id_set = t.id_set ; typ_var_set = t.typ_var_set;
									exp = t.exp ; sig_decl = t.sig_decl ; (* dir = t.dir; *)
									proc_loc = r_loc 
									} ;
								fathers = s.fathers 
								}
	let rec parc d = function
			| [] -> "", d
			| _::l -> let hd,tl = hd_tl d
						in let r,rl = parc tl l in (hd ^ r), rl
	let rec parc_inv d = function
			| [] -> "", d
			| _::l -> let hd,tl = hd_tl d
						in let r,rl = parc tl l in (r ^ hd), rl

	let apl_sig_declas s isl osl lSl = 				
		let t = s.tree
		in let dec = t.sig_decl
			in let sig_loc,dec1 = (*if lSl = []
									then "", dec
									else*) parc dec lSl
				in let sig_out,dec2 = if osl = []
										then "", dec1
										else let r,d = parc dec1 osl
											in ("! " ^ r),d
					in let sig_in,dec3 = if isl = []
											then "", dec2
											else let r,d = parc dec2 isl
												in ("? " ^ r),d
				in {
					str = sig_in ^ sig_out ^ "loc : " ^ sig_loc; 
					tree = {
						pro_dec = t.pro_dec; proc = t.proc ; proc_hd = t.proc_hd ;
						sig_decls = sig_in,sig_out,sig_loc ;
						proc_bd = t.proc_bd ; inst = t.inst; constr = t.constr ; 
						constr_k = t.constr_k; assign = t.assign; id = t.id ; 
						id_set = t.id_set ; typ_var_set = t.typ_var_set;
						exp = t.exp ; sig_decl = [] ; (* dir = t.dir; *)
						proc_loc = t.proc_loc
						} ;
					fathers = s.fathers 
					}

	let apl_sig_decla s sn st sd = 
		let t = s.tree
		in let typ,id1 = hd_tl t.id
			in let name,id2 = hd_tl id1
				in let dec = typ ^ " " ^ name ^ ";\n"
					in {
						str = dec ;
						tree = {
							pro_dec = t.pro_dec; proc = t.proc ; proc_hd = t.proc_hd ;
							sig_decls = t.sig_decls ; proc_bd = t.proc_bd ; inst = t.inst; 
							constr = t.constr ; constr_k = t.constr_k; assign = t.assign; 
							id = []; id_set = t.id_set ; typ_var_set = t.typ_var_set;
							exp = t.exp ; 
							sig_decl =  dec :: t.sig_decl ; 
							(* dir = t.dir; *) proc_loc = t.proc_loc
							} ;
						fathers = s.fathers 
						}
	
	let apl_proc_bd s al cl il =  
		let t = s.tree
		in let body = "(\n" ^ t.inst ^ t.constr ^ t.assign ^ "|)\n"
			in {
				str = body ;
				tree = {
					pro_dec = t.pro_dec; proc = t.proc ; proc_hd = t.proc_hd ;
					sig_decls = t.sig_decls ; proc_bd = body ; inst = ""; 
					constr = "" ; constr_k = t.constr_k; assign = ""; 
					id = []; id_set = t.id_set ; typ_var_set = t.typ_var_set;
					exp = t.exp ; sig_decl = t.sig_decl ; (* dir = t.dir; *) 
					proc_loc = t.proc_loc
					} ;
				fathers = s.fathers 
				}
				
	let apl_inst s ipn ios iie = 
		let t = s.tree
		in let name,id1 = hd_tl t.id
			in let outl,id2 = parc id1 ios
				in let inl,id3 = parc t.exp iie
			in let instanc = "  | submodule " ^ name ^ 
						"(" ^ outl ^ ")" ^ 
						"(" ^ inl ^ ")" ^ 
						"\n"
				in {
					str = instanc ;
					tree = {
						pro_dec = t.pro_dec; proc = t.proc ; proc_hd = t.proc_hd ;
						sig_decls = t.sig_decls ; proc_bd = t.proc_bd ; inst = instanc; 
						constr = t.constr ; constr_k = t.constr_k; assign = t.assign; 
						id = id3; id_set = t.id_set ; typ_var_set = t.typ_var_set;
						exp = t.exp ; sig_decl = t.sig_decl ; (* dir = t.dir; *) 
						proc_loc = t.proc_loc
						} ;
					fathers = s.fathers 
					}

	let apl_assign s asn ae = 
		let t = s.tree 
		in let name,id1 = hd_tl t.id 
			and sel, nel = hd_tl t.exp
			in let assig = "  | " ^ name ^ " := " ^ sel ^ "\n"
			in {
				str = assig ;
				tree = {
					pro_dec = t.pro_dec; proc = t.proc ; proc_hd = t.proc_hd ;
					sig_decls = t.sig_decls ; proc_bd = t.proc_bd ; inst = t.inst; 
					constr = t.constr ; constr_k = t.constr_k; assign = assig ^ t.assign; 
					id = id1; id_set = t.id_set ; typ_var_set = t.typ_var_set;
					exp = nel; 
					sig_decl = t.sig_decl ; (* dir = t.dir; *) proc_loc = t.proc_loc
					} ;
				fathers = s.fathers
				}

	let add_exp nexp nid s = let t = s.tree 
		in {
			str = nexp ;
			tree = {
				pro_dec = t.pro_dec; proc = t.proc ; proc_hd = t.proc_hd ;
				sig_decls = t.sig_decls ; proc_bd = t.proc_bd ; inst = t.inst; 
				constr = t.constr ; constr_k = t.constr_k; assign = t.assign; 
				id = nid; id_set = t.id_set ; typ_var_set = t.typ_var_set;
				exp = nexp::t.exp; 
				sig_decl = t.sig_decl ; (* dir = t.dir; *) proc_loc = t.proc_loc
				} ;
			fathers = s.fathers 
			}
			
	let chg_exp nexp nlexp nid s = let t = s.tree
		in {
			str = nexp ;
			tree = {
				pro_dec = t.pro_dec; proc = t.proc ; proc_hd = t.proc_hd ;
				sig_decls = t.sig_decls ; proc_bd = t.proc_bd ; inst = t.inst; 
				constr = t.constr ; constr_k = t.constr_k; assign = t.assign; 
				id = nid; id_set = t.id_set ; typ_var_set = t.typ_var_set;
				exp = nexp::nlexp; 
				sig_decl = t.sig_decl ; (* dir = t.dir; *) proc_loc = t.proc_loc
				} ;
			fathers = s.fathers 
			}
	
	let rec exp_2 truc s e1 e2 par = 
			let s1 = apl_sig_exp s e1
				in let s2 = apl_sig_exp s1 e2
					in let ne2,exp1 = hd_tl s2.tree.exp
						in let ne1,exp2 = hd_tl exp1
							in let id =  if par 
											then "(" ^ ne1 ^ ")" ^ truc ^ "(" ^ ne2 ^ ")"
											else ne1 ^ truc ^ ne2
								in chg_exp id exp2 s2.tree.id s2
	
	and apl_sig_exp_l s = function
		| [] -> s
		| e::[] -> apl_sig_exp s e
		| e::q -> let se = apl_sig_exp s e
			in let hd,tl = hd_tl se.tree.exp
				in let ns = let t = se.tree in
							{
							str = hd ;
							tree = {
								pro_dec = t.pro_dec; proc = t.proc ; proc_hd = t.proc_hd ;
								sig_decls = t.sig_decls ; proc_bd = t.proc_bd ; inst = t.inst; 
								constr = t.constr ; constr_k = t.constr_k; assign = t.assign; 
								id = t.id; id_set = t.id_set ; typ_var_set = t.typ_var_set;
								exp = (hd ^ ", ")::tl; 
								sig_decl = t.sig_decl ; (* dir = t.dir; *) proc_loc = t.proc_loc
								} ;
							fathers = se.fathers 
							}
					in apl_sig_exp_l ns q

	and apl_sig_exp s = function
		EnumVariantAtom(i) -> let si = apl_identifier s i
			in add_exp i (List.tl si.tree.id) si
		| SignalAtom(i) -> let si = apl_identifier s i
			in add_exp i (List.tl si.tree.id) si

		| WhenAtom(i) -> let si = apl_identifier s i
			in let hd,tl = hd_tl si.tree.id
				in let id = "when " ^ (hd)
					in add_exp id (tl) si
		| NotAtom(i) -> let si = apl_identifier s i
			in let hd,tl = hd_tl si.tree.id
				in let id = "not " ^ (hd)
					in add_exp id (tl) si
		| WhenNotAtom(i) -> let si = apl_identifier s i
			in let hd,tl = hd_tl si.tree.id
				in let id = "when not " ^ (hd)
					in add_exp id (tl) si
			
		| IntegerConstant(i) -> let id = string_of_int i
			in add_exp id s.tree.id s
		
		| ClockPlus(e1, e2) -> exp_2 " ^+ " s e1 e2 false
		| ClockMinus(e1, e2) -> exp_2 " ^- " s e1 e2 false
		| ClockTimes(e1, e2) -> exp_2 " ^* " s e1 e2 false
		| Delay(e1, e2) -> exp_2 " $1 init " s e1 e2 true
		| EqualityAtom(e1, e2) -> exp_2 " = " s e1 e2 false
		| Default(e1, e2) -> exp_2 " default " s e1 e2 true 
		| When(e1, e2) -> exp_2 " when " s e1 e2 true
		| AndExp(e1, e2) -> exp_2 " and " s e1 e2 true
		| OrExp(e1, e2) -> exp_2 " or " s e1 e2 true
		| Plus(e1, e2) -> exp_2 " + " s e1 e2 false
		| Minus(e1, e2) -> exp_2 " - " s e1 e2 false
		| Times(e1, e2) -> exp_2 " * " s e1 e2 false
		| FunctionCall(i, el) -> 
			let s1 = apl_sig_exp_l s el
			in let s2 = apl_identifier s1 i
				in let hd,tl = hd_tl s2.tree.id
					and sel,lexp = parc_inv s2.tree.exp el
			in let exp =  "call " ^ hd ^ "(" ^ sel ^ ")"
				in chg_exp exp lexp tl s2
		| InAtom(e, tvs) ->  
			failwith "Not inplmented in the scanner"

	let apl_sconstr s ck lsn rsn = 
		let t = s.tree
		in let right,s1 = hd_tl t.id
			in let left,s2 = hd_tl s1
				in let kind = t.constr_k
					in let const = "  | " ^ left ^ " " ^ kind ^ " " ^ right ^ "\n"
						in 
							{
							str = const ;
							tree = {
								pro_dec = t.pro_dec; proc = t.proc ; proc_hd = t.proc_hd ;
								sig_decls = t.sig_decls ; proc_bd = t.proc_bd ; inst = t.inst; 
								constr = const ^ t.constr ; constr_k = t.constr_k; assign = t.assign; 
								id = s2; id_set = t.id_set ; typ_var_set = t.typ_var_set;
								exp = t.exp; sig_decl = t.sig_decl; proc_loc = t.proc_loc
								} ;
							fathers = s.fathers 
							}

	let apl_sconstr_k s = 
		let c_k k = let t = s.tree 
					in {
						str = k ;
						tree = {
							pro_dec = t.pro_dec; proc = t.proc ; proc_hd = t.proc_hd ;
							sig_decls = t.sig_decls ; proc_bd = t.proc_bd ; inst = t.inst; 
							constr = t.constr ; constr_k = k; assign = t.assign; 
							id = t.id; id_set = t.id_set ; typ_var_set = t.typ_var_set;
							exp = t.exp; sig_decl = t.sig_decl; proc_loc = t.proc_loc
							} ;
						fathers = s.fathers
						}
		in let trait = function 
			ClockEquality -> c_k " ^= "
			| ClockLeq  -> c_k " ^<= "
			| ClockLess -> c_k " ^< "
			| ClockWhen -> c_k " ^= when "
			| ClockWhenNot -> c_k " ^= when not "
			| ClockExclusive -> c_k " ^# "
			in trait
	
	let apl_direc s =
		let dir d= let t = s.tree 
					in {
						str = d;
						tree = {
							pro_dec = t.pro_dec; proc = t.proc ; proc_hd = t.proc_hd ;
							sig_decls = t.sig_decls ; proc_bd = t.proc_bd ; inst = t.inst; 
							constr = t.constr ; constr_k = t.constr_k; assign = t.assign; 
							id = t.id; id_set = t.id_set ; typ_var_set = t.typ_var_set;
							exp = t.exp; sig_decl = t.sig_decl; proc_loc = t.proc_loc
							} ;
						fathers = s.fathers
						}
		in let trait = function
			| Input ->  dir "?"
			| Output -> dir "!"
			| Local -> dir "where"
			in trait
end
