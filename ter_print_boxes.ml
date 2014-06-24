open Ms_syntax_tree
open SyntaxTree
open Ms_identifier
open Ter_exception
open Ter_util
open Ter_iterateurs
open Ter_identite
open Ter_struc_box

let str_port p = 
	"name = "^p.p_name^", id = "^(string_of_int p.p_uniqid)^"\n"

let rec str_ports = function
	|[] -> ""
	|p::l -> (str_port p)^(str_ports l)

let str_box b =
"name = "^b.b_name^", id = "^(string_of_int b.b_uniqid)^"\n"
^"in :\n"^(str_ports b.b_inL)
^"out :\n"^(str_ports b.b_outL)

let rec str_boxes = function
	|[] -> ""
	|b::l -> (str_box b)^"\n"^(str_boxes l)

let str_b id =
	"name = "^id.box_name^", id = "^(string_of_int id.box_uniqid)^"\n"

let str_link l =
	"from "^(
		match(l.l_beg)with
			|(e, None) -> (str_port e)
			|(e, Some b) -> "box "^(str_b b)^" output "^(str_port e)
	)^" to "^(
		match(l.l_end)with
			|(e, None) -> (str_port e)
			|(e, Some b) -> "box "^(str_b b)^" input "^(str_port e)
	)

let rec str_links = function
	|[] -> ""
	|e::l -> (str_link e)^"\n"^(str_links l)

let str_c c =
	"constraint "^c.c_con^" from "^(str_port c.c_beg)^" to "^(str_port c.c_end)

let rec str_cons = function
	|[] -> ""
	|c::l -> (str_c c)^(str_cons l)

let rec str_fa = function
	|[] -> "\n"
	|f::[] -> f^"\n"
	|f::l -> f^", "^(str_fa l)

let str_pr_data p =
	"Process "^p.pr_name^" "^(str_fa p.pr_fathers)
	^"In\n"^(str_ports p.pr_lin)
	^"Out\n"^(str_ports p.pr_lout)
	^"Local\n"^(str_ports p.pr_lloc)
	^"Constants\n"^(str_ports p.pr_lconst)
	^"Boxes\n"^(str_boxes p.pr_boxes)
	^"Assigns links\n"^(str_links p.pr_assigns)
	^"Instances links\n"^(str_links p.pr_insts)
	^"Constraints links\n"^(str_cons p.pr_cons)


let rec str_spec_b = function
	|[] -> ""
	|e::l ->( str_pr_data e )
			^ "\n"
			^ str_spec_b l
