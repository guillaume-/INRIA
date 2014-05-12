open Ms_syntax_tree
open SyntaxTree
open Ms_identifier
open Ter_exception
open Ter_util
open Ter_iterateurs

module Tfr_schemas_latex:tParam  = struct
	type position{
		x: int;
		y: int;
	}
	type str_hd = {
		name: string;
		v_in: (string, position) list;
		v_out: (string, position) list;
		(*v_local: (string, position) list;*)
		loc_proc: (string, position) list;
	}
	type str_bd = {
		assign = (string, position) list;
		instant = (string, position) list;
		constr = (string, position) list;
	}
	type str_proc = {s_bd: str_bd, s_hd: str_hd}
	type ref = {spec: specification; (*proc_cur: process list;*) s: (str_proc, position) list}

	module SlParam : tRef with type r = ref = struct
		type r = ref

		let creerRef s =
		(*
		let rec locaux pr res =
			let local_pr_list = List.rev pr.header.local_process_list in
			if(List.length local_pr_list > 0)
			then locaux (List.hd local_pr_list) ((local_pr_list)@res)
			else res
		in let loc = locaux (List.hd (List.rev s.process_list)) []
		*)
		in {spec = s; (*proc_cur = loc@(List.rev s.process_list);*)[];}
	end

	include Identite(SlParam)



	val tfr_proced_decla:  t -> Identifier.t -> Identifier.t list -> Identifier.t -> procedure_declaration * t
	val tfr_process: t -> process_header -> process_body -> process * t
	val tfr_proc_hd: t -> Identifier.t -> signal_declarations -> process list -> process_header * t
	val tfr_sig_declas: t -> signal_declaration list -> signal_declaration list -> signal_declaration list -> signal_declarations * t
	val tfr_proc_bd: t -> assignment list -> sconstraint list -> instantiation list -> process_body * t
	val tfr_inst: t -> Identifier.t -> Identifier.t list -> signal_expression list -> instantiation * t
	val tfr_sconstr: t -> sconstraint_kind -> Identifier.t -> Identifier.t -> sconstraint * t
	val tfr_sconstr_k: t -> sconstraint_kind -> sconstraint_kind * t
	val tfr_assign: t -> Identifier.t -> signal_expression -> assignment * t
	val tfr_sig_exp: t -> signal_expression -> signal_expression * t
	val tfr_sig_decla: t -> Identifier.t -> Identifier.t -> direction -> signal_declaration * t
	val tfr_direc: t -> direction -> direction * t
	val tfr_typed_var_set: t -> Identifier.t -> IdentifierSet.t -> typed_variant_set * t
	val tfr_identifier: t -> Identifier.t -> Identifier.t * t
	val tfr_identifier_set:  t -> IdentifierSet.t -> IdentifierSet.t * t
end
