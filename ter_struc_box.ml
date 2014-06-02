type port = {p_name: string;
			 p_uniqid: int; (* default value : 0
is used only if there is some multiple call of constants like '2' *)
}
type box = {b_inL: port list;
			b_outL: port list;
			b_name: string;
			b_uniqid: int; (* default value : 0
is used only if there is multiple definition of a same box *)
}
type b = {
	box_name: string;
	box_uniqid: int;
}
type link = {
	l_beg: port*(b option);
	l_end: port*(b option);
	(* if b option is None :
		port IN lin+lout+lloc+lconst
	   else
		port.name IN ( b.inL.name + b.outL.name )
	*)
}
type c_link = {
	c_beg: port;
	c_end: port;
	(* no box for a constraint *)
}
type pr_data = {
	pr_name: string;
	pr_fathers: (string list);
	pr_boxes: box list;
	pr_assigns: link list;
	pr_cons: c_link list;
	pr_insts: link list;
	pr_lin: port list;
	pr_lout: port list;
	pr_lloc: port list;
	pr_lconst: port list;
}
type spec_boxes = pr_data list
