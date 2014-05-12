open Ms_syntax_tree
open SyntaxTree
open Ms_identifier
open Ter_exception
open Ter_util
open Ter_iterateurs
open Ter_identite

module Tfr_arith_to_call:tParam  = struct
	module AtcParam : tRef with type r = procedure_declaration list = struct
	type r = procedure_declaration list
	let creerRef _ = []
	end
	
	include Identite(AtcParam)
	
	let sR r p = p::r
	let tR r p = (List.exists (fun d -> d = p) r)
	let vR s = let rec verif =function
		  | [] -> s
		  | e::l ->  let reste = verif l 
				in let rec v = function
				  | [] -> reste
				  | t::q -> let rst = v q
						in if tR rst t then rst else sR rst t
				in v e
		in verif
	let gP s = {procedure_name = s ;
		procedure_input_list = ["integer";"integer"] ; 
		procedure_output = "integer" ;}
		  
	
		let tfr_spec s pl tdl pdl = ({
	process_list = pl;
	type_declaration_list = tdl;
	procedure_declaration_list = vR s [pdl];
		},s) 

		let rec tfr_sig_exp (s:t) exp =  
	let trait st e1 e2 = 
		let (ne1, s1) = tfr_sig_exp st e1 
		and (ne2, s2) = tfr_sig_exp st e2
		in let rst = vR st (s1::[s2])
				in (ne1, ne2, rst)

	and chk p res = if tR res p
			then res
			else sR res p

	in match exp with
		| Plus(e1, e2) -> let (ne1, ne2, rs) = trait s e1 e2
				  in ((FunctionCall("add", [ne1; ne2])),
						  (chk (gP "add") rs))
		| Minus(e1, e2) ->let (ne1, ne2, rs) = trait s e1 e2
				in  ((FunctionCall("sub", [ne1; ne2])) , (chk (gP "sub") rs))
		| Times(e1, e2) -> let (ne1, ne2, rs) = trait s e1 e2
				in ((FunctionCall("mul", [ne1; ne2])) , (chk (gP "mul") rs))
		| EnumVariantAtom(i) -> let ni,rs = tfr_identifier s i
			in (EnumVariantAtom(ni),rs)
		| SignalAtom(i) -> let ni,rs = tfr_identifier s i
			in (SignalAtom(ni),rs)
		| WhenAtom(i) -> let ni,rs = tfr_identifier s i
			in (WhenAtom(ni),rs)
		| NotAtom(i) -> let ni,rs = tfr_identifier s i
			in (NotAtom(ni),rs)
		| WhenNotAtom(i) -> let ni,rs = tfr_identifier s i
			in (WhenNotAtom(ni),rs)
		| IntegerConstant(i) -> (IntegerConstant(i),s)
		| ClockPlus(e1, e2) -> 
			let (ne1, ne2, rs) = trait s e1 e2
			in (ClockPlus(ne1, ne2),rs)
		| ClockMinus(e1, e2) -> 
			let (ne1, ne2, rs) = trait s e1 e2
			in (ClockMinus(ne1, ne2),rs)
		| ClockTimes(e1, e2) -> 
			let (ne1, ne2, rs) = trait s e1 e2
			in (ClockTimes(ne1, ne2),rs)
		| Delay(e1, e2) -> 
			let (ne1, ne2, rs) = trait s e1 e2
			in (Delay(ne1, ne2),rs)
		| EqualityAtom(e1, e2) -> 
			let (ne1, ne2, rs) = trait s e1 e2
			in (EqualityAtom(ne1,ne2),rs)
		| Default(e1, e2) -> 
			let (ne1, ne2, rs) = trait s e1 e2
			in (Default(ne1, ne2),rs)
		| When(e1, e2) -> 
			let (ne1, ne2, rs) = trait s e1 e2
			in (When(ne1, ne2),rs)
		| AndExp(e1, e2) -> 
			let (ne1, ne2, rs) = trait s e1 e2
			in (AndExp(ne1, ne2),rs)
		| OrExp(e1, e2) -> 
			let (ne1, ne2, rs) = trait s e1 e2
			in (OrExp(ne1, ne2),rs)
		| FunctionCall(i, el) -> 
			let ni,s1 = tfr_identifier s i
			and nel,ls1 = List.fold_right (fun e -> fun (r,rs) -> let (ne,ns) = (tfr_sig_exp s e) in (ne::r),(ns::rs)) el ([],[])
			in let rs = vR s (s1::ls1)
			in (FunctionCall(ni,nel),rs) 
		| InAtom(e, tvs) ->  
			let ne,s1 = tfr_sig_exp s e
			and nttn,s2 = tfr_identifier s tvs.tv_type_name
			and nvs,s3 = tfr_identifier_set s tvs.variant_set
			in  let ntvs,s4 = tfr_typed_var_set s nttn nvs
					in let rs = vR s [s1;s2;s3;s4]
					in (InAtom(ne, ntvs),rs)
end
