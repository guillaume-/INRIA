open Ms_syntax_tree
open SyntaxTree
open Ter_iterateurs
open Ter_to_string

module Applic = Apl_to_string
module Apply_transfo = Application(Applic)

let str_spec s = let a = (Apply_transfo.apply_spec s) in a.str

let str_proced_decla pdec = let a = (Apply_transfo.apply_proced_decla creerRefVide pdec) in a.str

let str_sig_declas sdecs = let a = (Apply_transfo.apply_sig_declas creerRefVide sdecs) in a.str

let str_sig_decla sdec = let a = (Apply_transfo.apply_sig_decla creerRefVide sdec) in a.str

let str_typed_var_set tvs = let a = (Apply_transfo.apply_typed_var_set creerRefVide tvs) in a.str

let str_identifier_set is = let a = (Apply_transfo.apply_id_set creerRefVide is) in a.str

let str_identifier i = let a = (Apply_transfo.apply_id creerRefVide i) in a.str

let str_direc d = let a = (Apply_transfo.apply_direc creerRefVide d) in a.str

let str_inst inst = let a = (Apply_transfo.apply_inst creerRefVide inst) in a.str

let str_sconstr const = let a = (Apply_transfo.apply_sconstr creerRefVide const) in a.str

let str_sconstr_k const_k = let a = (Apply_transfo.apply_sconstr_k creerRefVide const_k) in a.str

let str_assign assign = let a = (Apply_transfo.apply_assign creerRefVide assign) in a.str

let rec str_sig_exp exp = let a = (Apply_transfo.apply_sig_exp creerRefVide exp) in a.str

let str_proc_bd bd = let a = (Apply_transfo.apply_proc_bd creerRefVide bd) in a.str

let str_process p = let a = (Apply_transfo.apply_process (creerRefHd p.header [p.header.process_name]) p) in a.str

let str_proc_hd hd =  let a = (Apply_transfo.apply_proc_hd (creerRefHd hd []) hd) in a.str


