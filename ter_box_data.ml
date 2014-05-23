type port = {name: string;
			uniqid: int; (* default value : 0
is used only if there is some multiple call of constants like '2' *)
}
type box = {inL: port list;
			outL: port list;
			name: string;
			uniqid: int; (* default value : 0
is used only if there is multiple definition of a same box *)
}
type b = {
	name: string;
	uniqid: int;
}
type link = {
	bg: port*(b option);
	nd: port*(b option);
	(* if b option is Empty :
		port IN lin+lout+lloc+lconst
	   else
		port.name IN ( b.inL.name + b.outL.name )
	*)
}
type pr_data = {
	name: string;
	fathers: (string list);
	boxes: box list;
	links: link list;
	lin: port list;
	lout: port list;
	lloc: port list;
	lconst: port list;
}
type res = pr_data list
