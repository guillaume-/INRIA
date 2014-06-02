open Ms_syntax_tree
open SyntaxTree
open Ms_identifier
open Ter_exception
open Ter_util
open Ter_iterateurs
open Ter_identite_p
open Ter_struc_box
open Ter_use_box

module Apl_mk_box:aParam = struct
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

	let apl_sig_decla param name stype dir = 
		let c = param.current_pr
		in match(dir)with
			Input		-> { spec = param.spec; fathers = param.fathers; res = param.res;
								current_pr = {
									pr_name = c.pr_name;
									pr_fathers = c.pr_fathers;
									pr_boxes = c.pr_boxes;
									pr_assigns = c.pr_assigns;
									pr_cons = c.pr_cons;
									pr_insts = c.pr_insts;
									pr_lin = (new_port name c.pr_lin)::c.pr_lin;
									pr_lout = c.pr_lout;
									pr_lloc = c.pr_lloc;
									pr_lconst = c.pr_lconst;
								}; 
							}
			| Output	-> { spec = param.spec; fathers = param.fathers; res = param.res;
								current_pr = {
									pr_name = c.pr_name;
									pr_fathers = c.pr_fathers;
									pr_boxes = c.pr_boxes;									pr_assigns = c.pr_assigns;
									pr_cons = c.pr_cons;
									pr_insts = c.pr_insts;
									pr_lin = c.pr_lin;
									pr_lout = (new_port name c.pr_lout)::c.pr_lout;
									pr_lloc = c.pr_lloc;
									pr_lconst = c.pr_lconst;
								}; 
							}
			| Local		-> { spec = param.spec; fathers = param.fathers; res = param.res;
								current_pr = {
									pr_name = c.pr_name;
									pr_fathers = c.pr_fathers;
									pr_boxes = c.pr_boxes;									pr_assigns = c.pr_assigns;
									pr_cons = c.pr_cons;
									pr_insts = c.pr_insts;
									pr_lin = c.pr_lin;
									pr_lout = c.pr_lout;
									pr_lloc = (new_port name c.pr_lloc)::c.pr_lloc;
									pr_lconst = c.pr_lconst;
								}; 
							}

(* 	let apl_sig_declas param isl osl losl = param *)

	let apl_proc_hd param name sp lpl =
		let c = param.current_pr in
		let f = try(List.hd param.fathers)with _ -> [] in
		{	spec = param.spec; fathers = param.fathers; res = param.res;
			current_pr = {
				pr_name = name;
				pr_fathers = f;
				pr_boxes = c.pr_boxes;
				pr_assigns = c.pr_assigns;
				pr_cons = c.pr_cons;
				pr_insts = c.pr_insts;
				pr_lin = c.pr_lin;
				pr_lout = c.pr_lout;
				pr_lloc = c.pr_lloc;
				pr_lconst = c.pr_lconst;
			}; 
		}


(* 	let apl_sig_exp param exp =  param *)

	let apl_assign param s_name expr =
		let c = param.current_pr
		in let rec bin_rec_op bi_name e1 e2 =
				let last_box = {
					b_inL = [{p_name = "in"; p_uniqid = 0;};
							 {p_name = "in"; p_uniqid = 1;}];
					b_outL = [{p_name = "out"; p_uniqid = 0;}];
					b_name = bi_name;
					b_uniqid = uniq bi_name c.pr_boxes;
				}
				in let last_box_id = {box_name = last_box.b_name; box_uniqid = last_box.b_uniqid;}
				in let last_box_in1_id = {p_name = "in"; p_uniqid = 0;}
				in let last_box_in2_id = {p_name = "in"; p_uniqid = 1;}
				in let tmp_b, tmp_links, tmp_k = 
					build_box 
						c.pr_lconst
						({l_beg = {p_name = "out"; p_uniqid = 0}, Some last_box_id; l_end = {p_name = s_name; p_uniqid = 0;}, None;}::c.pr_assigns)
						(last_box::c.pr_boxes)
						last_box_id
						last_box_in1_id e1 
				in build_box tmp_k tmp_links tmp_b last_box_id last_box_in2_id e2
		and call_op (bid: b) (bo: box list) (li: link list) (co: port list) (inL: port list) (x: Ms_syntax_tree.SyntaxTree.signal_expression list) = match(x)with
				|[] -> (bo, li, co)
				|exp::lis -> let (boxl, linksl, constl) = build_box co li bo bid (List.hd inL) exp
							in call_op bid boxl linksl constl (List.tl inL) lis
		and build_box (constantes: port list) (links: link list) (boxes: box list) (last_box_id: b) (last_box_in_id: port) = function
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
				let newP = new_port (string_of_int k_value) c.pr_lconst in
				boxes,
				(l_port_to_box newP last_box_in_id last_box_id)::links,
				(newP::constantes)
			| ClockPlus(e1, e2) -> bin_rec_op "^+" e1 e2
			| ClockMinus(e1, e2) -> bin_rec_op "^-" e1 e2
			| ClockTimes(e1, e2) -> bin_rec_op "^*" e1 e2
			| Delay(e1, e2) -> bin_rec_op "delay" e1 e2
			| EqualityAtom(e1, e2) -> bin_rec_op "=" e1 e2
			| Default(e1, e2) -> bin_rec_op "default" e1 e2
			| AndExp(e1, e2) -> bin_rec_op "and" e1 e2
			| OrExp(e1, e2) -> bin_rec_op "or" e1 e2
			| Plus(e1, e2) -> bin_rec_op "+" e1 e2
			| Minus(e1, e2) -> bin_rec_op "-" e1 e2
			| Times(e1, e2) -> bin_rec_op "*" e1 e2
			| When(e1, e2) -> bin_rec_op "when" e1 e2
(*			| WhenAtom(id) ->
			| WhenNotAtom(id) ->
			| NotAtom(id) ->*)
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
			| _ -> (boxes, links, constantes)
		in let bin_op bi_name e1 e2 =
				let last_box = {
					b_inL = [port_variable "in";
							 {p_name = "in"; p_uniqid = 1;}];
					b_outL = [port_variable "out"];
					b_name = bi_name;
					b_uniqid = uniq bi_name c.pr_boxes;
				}
				in let last_box_id = {box_name = last_box.b_name; box_uniqid = last_box.b_uniqid;}
				in let last_box_in1_id = {p_name = "in"; p_uniqid = 0;}
				in let last_box_in2_id = {p_name = "in"; p_uniqid = 1;}
				in let tmp_b, tmp_links, tmp_k = 
					build_box 
						c.pr_lconst
						({l_beg = {p_name = "out"; p_uniqid = 0}, Some last_box_id; l_end = {p_name = s_name; p_uniqid = 0;}, None;}::c.pr_assigns)
						(last_box::c.pr_boxes)
						last_box_id
						last_box_in1_id e1 
				in build_box tmp_k tmp_links tmp_b last_box_id last_box_in2_id e2
			in let uni_op uni_name id =
				let bid = uniq uni_name c.pr_boxes
				in if(List.exists (fun x -> x.p_name = id) c.pr_lin
				|| List.exists (fun x -> x.p_name = id) c.pr_lout
				|| List.exists (fun x -> x.p_name = id) c.pr_lloc
				)then
					{  b_inL = [{p_name = "in"; p_uniqid = 0}];
						b_outL = [{p_name = "out"; p_uniqid = 0}];
						b_name = uni_name;
						b_uniqid = bid;
					}::c.pr_boxes,
					{l_beg = {p_name = id; p_uniqid = 0}, None; l_end = {p_name = "a"; p_uniqid = 0}, Some {box_name = uni_name; box_uniqid = bid;};}
						::({l_beg = {p_name = "out"; p_uniqid = 0}, Some {box_name = uni_name; box_uniqid = bid;}; l_end = {p_name = s_name; p_uniqid = 0;}, None}
						::c.pr_assigns),
					c.pr_lconst
				else
					let new_v = new_port id c.pr_lconst in
					{  b_inL = [{p_name = "in"; p_uniqid = 0}];
						b_outL = [{p_name = "out"; p_uniqid = 0}];
						b_name = uni_name;
						b_uniqid = bid;
					}::c.pr_boxes,
					{l_beg = new_v, None; l_end = {p_name = "in"; p_uniqid = 0}, Some {box_name = uni_name; box_uniqid = bid;}}
						::({l_beg = {p_name = "out"; p_uniqid = 0}, Some {box_name = uni_name; box_uniqid = bid;}; l_end = {p_name = s_name; p_uniqid = 0;}, None}
						::c.pr_assigns),
					new_v::c.pr_lconst
			in let news = match(expr)with
			SignalAtom(var_name) ->
				c.pr_boxes, {
					l_beg = {p_name = var_name; p_uniqid = 0;}, None;
					l_end = {p_name = s_name; p_uniqid = 0;}, None;
				}::c.pr_assigns,
				c.pr_lconst
			| EnumVariantAtom(k_name) ->
				let newP = new_port k_name c.pr_lconst in
				c.pr_boxes, {
					l_beg = newP, None;
					l_end = {p_name = s_name; p_uniqid = 0;}, None;
				}::c.pr_assigns,
				newP::c.pr_lconst
			| IntegerConstant(k_value) ->
				let newP = new_port (string_of_int k_value) c.pr_lconst in
				c.pr_boxes, {
					l_beg = newP, None;
					l_end = {p_name = s_name; p_uniqid = 0;}, None;
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
 			| FunctionCall(id, sig_list) -> let i = uniq id c.pr_boxes
 			in let inL =
				let rec build_inL i = function
					|[] -> []
					|e::l -> {p_name = "in"; p_uniqid = i;}::(build_inL (i+1) l)
				in build_inL 0 sig_list
			in call_op
				{box_name = id; box_uniqid = i;}
				({b_inL = inL; b_outL = [{p_name = "out"; p_uniqid = 0}]; b_name = id; b_uniqid = i;}::c.pr_boxes)
				c.pr_assigns
				c.pr_lconst
				inL
				sig_list
			| _ -> c.pr_boxes, c.pr_assigns, c.pr_lconst
		in let new_boxes, new_links, new_k = news
		in {spec = param.spec; fathers = param.fathers; res = param.res;
			current_pr = {
				pr_name = c.pr_name;
				pr_fathers = c.pr_fathers;
				pr_boxes = new_boxes;
				pr_assigns = new_links;
				pr_cons = c.pr_cons;
				pr_insts = c.pr_insts;
				pr_lin = c.pr_lin;
				pr_lout = c.pr_lout;
				pr_lloc = c.pr_lloc;
				pr_lconst = new_k;
			}; 
		}

	let apl_sconstr param const_kind sLeft sRight = param

	let apl_inst param ipn ios iie = param

	let apl_proc_bd param assignl sconsl instl = param



	let apl_process param hd bd =
		let f = try(List.tl param.fathers)with _ -> []
		in {spec = param.spec; 
			fathers = f;
			res = ((param.current_pr)::(param.res));
			current_pr = init_current_pr param.fathers;
		}
(*
	let apl_proced_decla param name inl out = param
	let apl_typed_var_set param name vs = param
*)
end
