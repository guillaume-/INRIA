open Ter_iterateurs
open Ter_identite
open Ter_arith_to_call
open Ter_no_submod
open Ter_chk_spec

let noSub prog =
	let module Trans = Tfr_no_submodule
	in let module Apply_transfo = Transformation(Trans) 
		in (Apply_transfo.transform_spec prog) 


let addCall prog =
	let module Trans = Tfr_arith_to_call
	in let module Apply_transfo = Transformation(Trans) 
	in Apply_transfo.transform_spec prog

let check prog =
	let module Trans = Tfr_chk_spec
	in let module Apply_transfo = Transformation(Trans) 
		in Apply_transfo.transform_spec prog 
