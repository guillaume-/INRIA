open Ter_struc_box

let new_port name ports =
	let rec search_port res = function
		|[] -> res
		|e::l ->if(e.p_name = name && e.p_uniqid = res)
				then search_port (res+1) l
				else search_port res l
	in {p_name = name; p_uniqid = search_port 0 ports;}

let new_b name bs =
	let rec search_b res = function
		|[] -> res
		|e::l ->if(e.box_name = name && e.box_uniqid = res)
				then search_b (res+1) l
				else search_b res l
	in {box_name = name; box_uniqid = search_b 0 bs;}

let uniq name =
	let rec search_box res = function
		|[] -> res
		|e::l ->if(e.b_name = name && e.b_uniqid = res)
				then search_box (res+1) l
				else search_box res l
in search_box 0

let port_variable var_name =
	{p_name = var_name; p_uniqid = 0;}

let port_variable_1 var_name =
	{p_name = var_name; p_uniqid = 1;}

let l_port_to_box port last_box_in_id last_box_id =
	{l_beg = port, None; l_end = last_box_in_id, Some last_box_id;}

let inL n =
	let rec build_inL = function
		|0 -> [{p_name = "in"; p_uniqid = 0;}]
		|x -> {p_name = "in"; p_uniqid = x;}::(build_inL (x-1))
	in build_inL n

let outL n =
	let rec build_outL = function
		|0 -> [{p_name = "out"; p_uniqid = 0;}]
		|x -> {p_name = "out"; p_uniqid = x;}::(build_outL (x-1))
	in build_outL n

let build_box_n_1 name n boxes =
	let u = uniq name boxes
	in {b_inL = (inL n); b_outL = [port_variable "out"]; b_name = name; b_uniqid = u;}

let build_box_n_m name n m boxes =
	let u = uniq name boxes
	in {b_inL = (inL n); b_outL = (outL m); b_name = name; b_uniqid = u;}

let bin_box name id = {
	b_inL = [port_variable "in";
			 port_variable_1 "in"];
	b_outL = [port_variable "out"];
	b_name = name;
	b_uniqid = id;
}

let uni_box name id ={
	b_inL = [port_variable "in"];
	b_outL = [port_variable "out"];
	b_name = name;
	b_uniqid = id;
}
