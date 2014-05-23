open Ms_syntax_tree
open SyntaxTree
open Ms_identifier
open Ter_exception
open Ter_util
open Ter_iterateurs

module type tRef = sig
	type r
	val creerRef: specification -> r
end

module Identite(R : tRef):aParam with type t = R.r = struct
	type t = R.r 
	let creerA = R.creerRef
	
	let apl_spec s pl tdl pdl = s

	let apl_proced_decla s pn pi po = s
	
	let apl_process s ph pb = s
	
	let apl_proc_hd s pn sd lpl = s

	let apl_sig_declas s isl osl lSl = s

	let apl_proc_bd s al cl il = s

	let apl_inst s ipn ios iie = s

	let apl_sconstr s ck lsn rsn = s

	let apl_sconstr_k s = function
		ClockEquality -> s
		| ClockLeq  -> s
		| ClockLess -> s
		| ClockWhen -> s
		| ClockWhenNot -> s
		| ClockExclusive -> s

	let apl_assign s asn ae = s

	let apl_identifier s i = s

	let apl_identifier_set s is = 
		IdentifierSet.fold (fun e -> fun r -> apl_identifier r e) is s

  let apl_typed_var_set s ttn vs = s

	let rec apl_sig_exp s = function
  	EnumVariantAtom(i) -> apl_identifier s i
  	| SignalAtom(i) -> apl_identifier s i
  	| WhenAtom(i) -> apl_identifier s i
  	| NotAtom(i) -> apl_identifier s i
  	| WhenNotAtom(i) -> apl_identifier s i
  
  	| IntegerConstant(i) -> s
  
  	| ClockPlus(e1, e2) -> 
  		let s1 = apl_sig_exp s e1
  		  in apl_sig_exp s1 e2
  	| ClockMinus(e1, e2) -> 
  		let s1 = apl_sig_exp s e1
  		  in apl_sig_exp s1 e2
  	| ClockTimes(e1, e2) ->  
  		let s1 = apl_sig_exp s e1
  		  in apl_sig_exp s1 e2
  	| Delay(e1, e2) -> 
  		let s1 = apl_sig_exp s e1
  		  in apl_sig_exp s1 e2
  	| EqualityAtom(e1, e2) -> 
  		let s1 = apl_sig_exp s e1
  		  in apl_sig_exp s1 e2
  	| Default(e1, e2) -> 
  		let s1 = apl_sig_exp s e1
  		  in apl_sig_exp s1 e2
  	| When(e1, e2) -> 
  		let s1 = apl_sig_exp s e1
  		  in apl_sig_exp s1 e2
  	| AndExp(e1, e2) -> 
  		let s1 = apl_sig_exp s e1
  		  in apl_sig_exp s1 e2
  	| OrExp(e1, e2) -> 
  		let s1 = apl_sig_exp s e1
  	  	in apl_sig_exp s1 e2
  	| Plus(e1, e2) -> 
  		let s1 = apl_sig_exp s e1
  	  	in apl_sig_exp s1 e2
  	| Minus(e1, e2) -> 
  		let s1 = apl_sig_exp s e1
  	  	in apl_sig_exp s1 e2
  	| Times(e1, e2) -> 
  		let s1 = apl_sig_exp s e1
  	  	in apl_sig_exp s1 e2
  	| FunctionCall(i, el) -> 
  		let s1 = apl_identifier s i
  	  	in List.fold_right (fun e -> fun r -> apl_sig_exp r e) el s1
  	| InAtom(e, tvs) ->  
  		let nttn = tvs.tv_type_name
  		and nvs = tvs.variant_set
  		in let s1 = apl_sig_exp s e
  			in let s2 = apl_identifier s1 nttn
  				in let s3 = apl_identifier_set s2 nvs
  					in apl_typed_var_set s3 nttn nvs

	
	let apl_sig_decla s sn st sd = s
	
	let apl_direc s = function
		Input -> s
		| Output -> s
		| Local -> s
	
end
