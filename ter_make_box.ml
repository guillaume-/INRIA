open Ms_syntax_tree
open SyntaxTree
open Ms_identifier
open Ter_exception
open Ter_util
open Ter_iterateurs
open Ter_identite_p
open Ter_struc_box
open Ter_use_box

type ref = {spec:specification; fathers:(string list) list; res:spec_boxes; current_pr:pr_data;}

	let init_current_pr f =
		let fhd = try(List.hd f)with _ -> []
		in {
			pr_boxes = [];
			pr_assigns = [];
			pr_cons = [];
			pr_insts = [];
			pr_lin = [];
			pr_lout = [];
			pr_lloc = [];
			pr_lconst = [];
			pr_name = "";
			pr_fathers = fhd;
		}

	module MbParam : tRef with type r = ref = struct
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
		in	{spec = s; fathers = init_fathers; res = []; current_pr = init_current_pr init_fathers;}
	end


	include Identite(MbParam)

	let rec bin_rec_op bi_name e1 e2 const boxes assigns oldBox oldPort (c: pr_data) =
		let l_box = bin_box bi_name (uniq bi_name boxes)
		in let l_box_id = {box_name = l_box.b_name; box_uniqid = l_box.b_uniqid;}
		in let l_box_in1_id = port_variable "in"
		in let l_box_in2_id = port_variable_1 "in"
		in let tmp_b, tmp_links, tmp_k = 
			build_box
				const
				({l_beg = port_variable "out", Some l_box_id; l_end = oldPort, Some oldBox;}::assigns)
				(l_box::boxes)
				l_box_id
				l_box_in1_id
				c
				e1
		in build_box tmp_k tmp_links tmp_b l_box_id l_box_in2_id c e2
	and call_op (bid: b) (bo: box list) (li: link list) (co: port list) (inL: port list) (x: Ms_syntax_tree.SyntaxTree.signal_expression list) (c: pr_data) = match(x)with
		|[] -> (bo, li, co)
		|exp::lis -> let (boxl, linksl, constl) = build_box co li bo bid (List.hd inL) c exp
					in call_op bid boxl linksl constl (List.tl inL) lis c
	and uni_rec_op uni_name id const boxes assigns oldBox oldPort (c: pr_data) =
		let bid = uniq uni_name boxes
		in if(List.exists (fun x -> x.p_name = id) c.pr_lin
		|| List.exists (fun x -> x.p_name = id) c.pr_lout
		|| List.exists (fun x -> x.p_name = id) c.pr_lloc
		)then
			(uni_box uni_name bid)::boxes,
			{l_beg = (port_variable id), None; l_end = (port_variable "in"), Some {box_name = uni_name; box_uniqid = bid;};}
				::({l_beg = port_variable "out", Some {box_name = uni_name; box_uniqid = bid;}; l_end = oldPort, Some oldBox}
				::assigns),
			const
		else
			let new_v = new_port id const in
			(uni_box uni_name bid)::boxes,
			{l_beg = new_v, None; l_end = (port_variable "in"), Some {box_name = uni_name; box_uniqid = bid;}}
				::({l_beg = (port_variable "out"), Some {box_name = uni_name; box_uniqid = bid;}; l_end = oldPort, Some oldBox}
				::assigns),
			new_v::const
	and build_box (constantes: port list) (links: link list) (boxes: box list) (last_box_id: b) (last_box_in_id: port) (c: pr_data) = function
		SignalAtom(var_name) ->
			boxes,
			(l_port_to_box (port_variable var_name) last_box_in_id last_box_id)::links,
			constantes
		| EnumVariantAtom(k_name) ->
			let newP = new_port k_name constantes in
			boxes,
			(l_port_to_box newP last_box_in_id last_box_id)::links,
			(newP::constantes)
		| IntegerConstant(k_value) ->
			let newP = new_port (string_of_int k_value) constantes in
			boxes,
			(l_port_to_box newP last_box_in_id last_box_id)::links,
			(newP::constantes)
		| ClockPlus(e1, e2) -> bin_rec_op "^+" e1 e2 constantes boxes links last_box_id last_box_in_id c
		| ClockMinus(e1, e2) -> bin_rec_op "^-" e1 e2 constantes boxes links last_box_id last_box_in_id c
		| ClockTimes(e1, e2) -> bin_rec_op "^*" e1 e2 constantes boxes links last_box_id last_box_in_id c
		| Delay(e1, e2) -> bin_rec_op "delay" e1 e2 constantes boxes links last_box_id last_box_in_id c
		| EqualityAtom(e1, e2) -> bin_rec_op "=" e1 e2 constantes boxes links last_box_id last_box_in_id c
		| Default(e1, e2) -> bin_rec_op "default" e1 e2 constantes boxes links last_box_id last_box_in_id c
		| AndExp(e1, e2) -> bin_rec_op "and" e1 e2 constantes boxes links last_box_id last_box_in_id c
		| OrExp(e1, e2) -> bin_rec_op "or" e1 e2 constantes boxes links last_box_id last_box_in_id c
		| Plus(e1, e2) -> bin_rec_op "+" e1 e2 constantes boxes links last_box_id last_box_in_id c
		| Minus(e1, e2) -> bin_rec_op "-" e1 e2 constantes boxes links last_box_id last_box_in_id c
		| Times(e1, e2) -> bin_rec_op "*" e1 e2 constantes boxes links last_box_id last_box_in_id c
		| When(e1, e2) -> bin_rec_op "when" e1 e2 constantes boxes links last_box_id last_box_in_id c
		| WhenAtom(id) -> uni_rec_op "when" id constantes boxes links last_box_id last_box_in_id c
		| WhenNotAtom(id) -> uni_rec_op "when not" id constantes boxes links last_box_id last_box_in_id c
		| NotAtom(id) -> uni_rec_op "not" id constantes boxes links last_box_id last_box_in_id c
		| FunctionCall(id, sig_list) ->
			let u = uniq id boxes
			in let box_id = {box_name = id; box_uniqid = u;}
			in call_op
				box_id
				((build_box_n_1 id (List.length sig_list) boxes)::boxes)
				((l_port_to_box (port_variable "out") last_box_in_id last_box_id)::links)
				constantes
				(inL (List.length sig_list))
				sig_list
				c
		| _ -> (boxes, links, constantes)

	let apl_sig_decla param name stype dir = 
		let c = param.current_pr
		in match(dir)with
			Input	->	{ param with
						  current_pr = {c with pr_lin = (new_port name c.pr_lin)::c.pr_lin;};
						}
			| Output->	{ param with
						  current_pr = {c with pr_lout = (new_port name c.pr_lout)::c.pr_lout;};
						}
			| Local	->	{ param with
						  current_pr = {c  with pr_lloc = (new_port name c.pr_lloc)::c.pr_lloc;}
						}

	let apl_proc_hd param name sp lpl =
		let c = param.current_pr in
		let f = try(List.hd param.fathers)with _ -> [] in
		{	param with
			current_pr = {c with pr_name = name; pr_fathers = f;}; 
		}

	let apl_assign param s_name expr =
		let c = param.current_pr
		in let bin_op bi_name e1 e2 =
				let last_box = bin_box bi_name (uniq bi_name c.pr_boxes)
				in let last_box_id = {box_name = last_box.b_name; box_uniqid = last_box.b_uniqid;}
				in let last_box_in1_id = port_variable "in"
				in let last_box_in2_id = port_variable_1 "in"
				in let tmp_b, tmp_links, tmp_k = 
					build_box 
						c.pr_lconst
						({l_beg = (port_variable "out"), Some last_box_id; l_end = port_variable s_name, None;}::c.pr_assigns)
						(last_box::c.pr_boxes)
						last_box_id
						last_box_in1_id
						c
						e1 
				in build_box tmp_k tmp_links tmp_b last_box_id last_box_in2_id c e2
			in let uni_op uni_name id =
				let bid = uniq uni_name c.pr_boxes
				in if(List.exists (fun x -> x.p_name = id) c.pr_lin
				|| List.exists (fun x -> x.p_name = id) c.pr_lout
				|| List.exists (fun x -> x.p_name = id) c.pr_lloc
				)then
					(uni_box uni_name bid)::c.pr_boxes,
					{l_beg = port_variable id, None; l_end = port_variable "in", Some {box_name = uni_name; box_uniqid = bid;};}
						::({l_beg = port_variable "out", Some {box_name = uni_name; box_uniqid = bid;}; l_end = port_variable s_name, None}
						::c.pr_assigns),
					c.pr_lconst
				else
					let new_v = new_port id c.pr_lconst in
					(uni_box uni_name bid)::c.pr_boxes,
					{l_beg = new_v, None; l_end = port_variable "in", Some {box_name = uni_name; box_uniqid = bid;}}
						::({l_beg = port_variable "out", Some {box_name = uni_name; box_uniqid = bid;}; l_end = port_variable s_name, None}
						::c.pr_assigns),
					new_v::c.pr_lconst
			in let news = match(expr)with
			SignalAtom(var_name) ->
				c.pr_boxes, {
					l_beg = port_variable var_name, None;
					l_end = port_variable s_name, None;
				}::c.pr_assigns,
				c.pr_lconst
			| EnumVariantAtom(k_name) ->
				let newP = new_port k_name c.pr_lconst in
				c.pr_boxes, {
					l_beg = newP, None;
					l_end = port_variable s_name, None;
				}::c.pr_assigns,
				newP::c.pr_lconst
			| IntegerConstant(k_value) ->
				let newP = new_port (string_of_int k_value) c.pr_lconst in
				c.pr_boxes, {
					l_beg = newP, None;
					l_end = port_variable s_name, None;
				}::c.pr_assigns,
				newP::c.pr_lconst
			| ClockPlus(e1, e2) -> bin_op "^+" e1 e2
			| ClockMinus(e1, e2) -> bin_op "^-" e1 e2
			| ClockTimes(e1, e2) -> bin_op "^*" e1 e2
			| Delay(e1, e2) -> bin_op "delay" e1 e2
			| EqualityAtom(e1, e2) -> bin_op "=" e1 e2
			| Default(e1, e2) -> bin_op "default" e1 e2
			| AndExp(e1, e2) -> bin_op "and" e1 e2
			| OrExp(e1, e2) -> bin_op "or" e1 e2
			| Plus(e1, e2) -> bin_op "+" e1 e2
			| Minus(e1, e2) -> bin_op "-" e1 e2
			| Times(e1, e2) -> bin_op "*" e1 e2
			| When(e1, e2) -> bin_op "when" e1 e2
			| WhenAtom(id) -> uni_op "when" id
			| WhenNotAtom(id) -> uni_op "when not" id
			| NotAtom(id) -> uni_op "not" id
 			| FunctionCall(id, sig_list) -> let u = uniq id c.pr_boxes
 			in let inL =
				let rec build_inL i = function
					|[] -> []
					|e::l -> {p_name = "in"; p_uniqid = i;}::(build_inL (i+1) l)
				in build_inL 0 sig_list
			in call_op
				{box_name = id; box_uniqid = u;}
				({b_inL = inL; b_outL = [port_variable "out"]; b_name = id; b_uniqid = u;}::c.pr_boxes)
				({l_beg = (port_variable "out"), Some {box_name = id; box_uniqid = u;};
				 l_end = (port_variable s_name), None
				}::c.pr_assigns)
				c.pr_lconst
				inL
				sig_list
				c
			| _ -> c.pr_boxes, c.pr_assigns, c.pr_lconst
		in let new_boxes, new_links, new_k = news
		in {spec = param.spec; fathers = param.fathers; res = param.res;
			current_pr = {
				c with
				pr_boxes = new_boxes;
				pr_assigns = new_links;
				pr_lconst = new_k;
			}; 
		}

	let apl_sconstr param const_kind sLeft sRight =
		let c = param.current_pr
		in let s = match(const_kind)with
			ClockEquality	-> "^ ="
			| ClockLeq 		-> "^ <="
			| ClockLess		-> "^ <"
			| ClockWhen		-> "^ when"
			| ClockWhenNot	-> "^ when not"
			| ClockExclusive-> "^ #"
		in
		{	param with
			current_pr = {
				c with
				pr_cons = {c_beg = port_variable sRight; c_end = port_variable sLeft; c_con = s;}::c.pr_cons;
			}; 
		}

	let apl_inst param ipn ios iie =
		let c = param.current_pr
		in let init_last_box = (build_box_n_m ipn (List.length iie) (List.length ios) c.pr_boxes)
		in let init_last_box_id = {box_name = ipn; box_uniqid = init_last_box.b_uniqid;}
		in let rec outLinks insts b_id i = function
			|[] -> insts
			|e::l ->{ l_beg = {p_name = "out"; p_uniqid = i}, Some b_id;
					  l_end = port_variable e, None;}
					::(outLinks insts b_id (i+1) l)
		in let init_b = init_last_box::c.pr_boxes
		in let init_l = outLinks c.pr_insts init_last_box_id 0 ios
		in let (boxes, insts, consts) =
			let rec forEach boxes links const last_b_id last_b_port = function
				|[] -> boxes, links, const
				|e::l -> let bo, li, co = build_box const links boxes last_b_id last_b_port c e
						 in forEach bo li co last_b_id {p_name = "out"; p_uniqid = last_b_port.p_uniqid +1} l
			in forEach init_b init_l c.pr_lconst init_last_box_id (port_variable "out") iie
		in {spec = param.spec; fathers = param.fathers; res = param.res;
			current_pr = {
				c with
				pr_boxes = boxes;
				pr_insts = insts;
				pr_lconst = consts;
			}; 
		}

	let apl_process param hd bd =
		let f = try(List.tl param.fathers)with _ -> []
		in {spec = param.spec; 
			fathers = f;
			res = ((param.current_pr)::(param.res));
			current_pr = init_current_pr param.fathers;
		}
