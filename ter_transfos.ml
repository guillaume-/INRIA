open Ter_iterateurs
open Ter_identite
open Ter_arith_to_call
open Ter_no_submod
open Ter_chk_spec
(*open Ter_schemas_latex*)
open Ter_schemas_dot
open Ter_to_string

let id prog = 
	let module IdParam : tRef = struct
		type r = unit
		let creerRef _ = ()
	end 
	in let module Trans = Identite(IdParam)
	in let module Apply_transfo = Transformation(Trans) 
		in Apply_transfo.transform_spec prog 

let noSub prog =
	let module Trans = Tfr_no_submodule
	in let module Apply_transfo = Transformation(Trans) 
		in (Apply_transfo.transform_spec prog) 

let addCall prog =
	let module Trans = Tfr_arith_to_call
	in let module Apply_transfo = Transformation(Trans) 
		in Apply_transfo.transform_spec prog

let check prog =
	let module Applic = Apl_chk_spec
	in let module Apply_transfo = Application(Applic) 
		in Apply_transfo.apply_spec prog 

(*let schemas_latex prog =
	let module Trans = Ter_schemas_latex
	in let module Apply_transfo = Transformation(Trans) 
		in let p = Apply_transfo.get_param prog in p.res*)
		
let schemas_dot prog =
	let module Trans = Ter_schemas_dot
	in let module Apply_transfo = Transformation(Trans) 
		in let p = Apply_transfo.get_param prog in p.res
		
let to_string prog = 
	let module Applic = Apl_to_string
	in let module Apply_transfo = Application(Applic)
		in let p = (Apply_transfo.apply_spec prog) in p.str
