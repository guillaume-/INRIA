open Ter_util;;
open Ter_plouf;;
open Ter_exception;;
open Ter_toString
open Ms_identifier;;
open Ms_syntax_tree;;
open SyntaxTree ;;

let cvrt_const p cur_p = p.body.constraint_list;;

(***************************************************************************************************
  Fonctions concernant le remplacement des process 
 ***************************************************************************************************)
let rec replace (p:process) (a_cur) (x) =
  match x with 
	| EnumVariantAtom(_) -> x
	| _ -> let rec rep = function
			| (t::l, e::q) -> let tst =(e.signal_name = (get_id x)) 
					  in print_string (">>>> p ref: " ^ e.signal_name ^"\n   t: \n"^ str_signal_expression t ^"\n") ;
					if tst then t else rep (l, q)
			| _ -> failwith "possible ??"
		and lout = p.header.signal_declarations.output_signal_list
		and lin = p.header.signal_declarations.input_signal_list
		and aout = a_cur.instance_output_signals
		and ain = a_cur.instance_input_expressions
		in if List.exists(fun d -> d.signal_name = (get_id x)) lout
			then let rec find = function
				| (i::j,k::r) -> if (i.signal_name) = (get_id x) then SignalAtom(k) else find (j, r)
				| _ -> raise Incompatible_outputs
			      in find (lout, aout)
			else rep (ain, lin)
;;

let f_SigAt p a x = let res = replace p a x in  print_string ("-> 1\n");
    match res with
	| SignalAtom(r) ->compose (SignalAtom(r))
	| EnumVariantAtom(r) -> compose (SignalAtom(r))(*pas sure ici*)
	| WhenAtom(r) -> compose (WhenAtom(r))
	| WhenNotAtom(r) -> compose (WhenNotAtom(r))
	| NotAtom(r) -> compose (NotAtom(r))
	| IntegerConstant(r) -> compose (SignalAtom(string_of_int r))
	| InAtom(_,_) -> failwith ("non encore géré")
	| r ->  compose2 r

	
;;

let f_WnAt p a x = let res = replace p  a x 
		    and cmp2 = compose2B (WhenAtom("when")) in print_string ("-> 2\n");
    match res with
	| EnumVariantAtom(r) -> compose (WhenAtom(r)) (*pas sure ici*)
	| SignalAtom(r) -> compose (WhenAtom(r))
	| WhenAtom(r) -> compose (WhenAtom(r))
	| WhenNotAtom(r) -> compose (WhenNotAtom(r))
	| NotAtom(r) -> compose (WhenNotAtom(r))
	| IntegerConstant(r) -> compose (WhenAtom(string_of_int r))
	| ClockPlus(e1, e2) -> cmp2 (ClockPlus(e1,e2))
	| ClockMinus(e1, e2) -> cmp2 (ClockMinus(e1,e2))
	| ClockTimes(e1, e2) -> cmp2 (ClockTimes(e1,e2))
	| Delay(e1, e2) -> cmp2 (Delay(e1,e2))
	| EqualityAtom(e1, e2) -> cmp2 (EqualityAtom(e1,e2))
	| Default(e1, e2) -> cmp2 (Default(e1,e2))
	| When(e1, e2) -> cmp2 (When(e1,e2))
	| AndExp(e1, e2) -> cmp2 (AndExp(e1,e2))
	| OrExp(e1, e2) -> cmp2 (OrExp(e1,e2))
	| Times(e1, e2) -> cmp2 (Times(e1,e2))
	| Minus(e1, e2) -> cmp2 (Minus(e1,e2))
	| Plus(e1, e2) -> cmp2 (Plus(e1,e2))
	| FunctionCall(e1, e2) -> cmp2 (FunctionCall(e1,e2))
	| _ -> failwith "non encore géré"
;;

let f_WnNAt p  a x = let res = replace p  a x 
   and cmp2 = compose2B (WhenNotAtom("when")) in print_string ("-> 3:"^ get_id x ^"\n");
    match res with
	| EnumVariantAtom(r) -> compose (WhenNotAtom(r)) (*pas sure ici*)
	| SignalAtom(r) -> compose (WhenNotAtom(r))
	| WhenAtom(r) -> compose (WhenNotAtom(r))
	| WhenNotAtom(r) -> compose (WhenAtom(r))
	| NotAtom(r) -> compose (WhenAtom(r))
	| IntegerConstant(r) -> compose (WhenNotAtom(string_of_int r))
	| ClockPlus(e1, e2) -> cmp2 (ClockPlus(e1,e2))
	| ClockMinus(e1, e2) -> cmp2 (ClockMinus(e1,e2))
	| ClockTimes(e1, e2) -> cmp2 (ClockTimes(e1,e2))
	| Delay(e1, e2) -> cmp2 (Delay(e1,e2))
	| EqualityAtom(e1, e2) -> cmp2 (EqualityAtom(e1,e2))
	| Default(e1, e2) -> cmp2 (Default(e1,e2))
	| When(e1, e2) -> cmp2 (When(e1,e2))
	| AndExp(e1, e2) -> cmp2 (AndExp(e1,e2))
	| OrExp(e1, e2) -> cmp2 (OrExp(e1,e2))
	| Times(e1, e2) -> cmp2 (Times(e1,e2))
	| Minus(e1, e2) -> cmp2 (Minus(e1,e2))
	| Plus(e1, e2) -> cmp2 (Plus(e1,e2))
	| FunctionCall(e1, e2) -> cmp2 (FunctionCall(e1,e2))
	| _ -> failwith "non encore géré" 
;;

let f_NAt  p  a x = let res = replace p  a x 
		    and cmp2 = compose2B (NotAtom("not"))  in print_string ("-> 4\n");
    match res with
	| EnumVariantAtom(r) -> compose (NotAtom(r))(*pas sure ici*)
	| SignalAtom(r) -> compose (NotAtom(r))
	| WhenAtom(r) -> compose (WhenNotAtom(r))
	| WhenNotAtom(r) -> compose (WhenAtom(r))
	| NotAtom(r) -> compose (NotAtom(r))
	| IntegerConstant(r) -> compose (NotAtom(string_of_int r))
	| ClockPlus(e1, e2) -> cmp2(ClockPlus(e1,e2))
	| ClockMinus(e1, e2) -> cmp2(ClockMinus(e1,e2))
	| ClockTimes(e1, e2) -> cmp2(ClockTimes(e1,e2))
	| Delay(e1, e2) -> cmp2(Delay(e1,e2))
	| EqualityAtom(e1, e2) ->cmp2(EqualityAtom(e1,e2))
	| Default(e1, e2) -> cmp2(Default(e1,e2))
	| When(e1, e2) -> cmp2(When(e1,e2))
	| AndExp(e1, e2) -> cmp2(AndExp(e1,e2))
	| OrExp(e1, e2) -> cmp2(OrExp(e1,e2))
	| Times(e1, e2) -> cmp2(Times(e1,e2))
	| Minus(e1, e2) -> cmp2(Minus(e1,e2))
	| Plus(e1, e2) -> cmp2(Plus(e1,e2))
	| FunctionCall(e1, e2) -> cmp2(FunctionCall(e1,e2))
	| _ -> failwith "%non encore géré" 
;;

let f_EnVarAt p  a x = let res = replace p  a x 
	 and cmp2 = compose2B (SignalAtom("var"))in print_string ("-> 5\n");
    match res with
	| EnumVariantAtom(r) ->compose (EnumVariantAtom(r)) (*pas sure ici*)
	| SignalAtom(r) -> compose (EnumVariantAtom(r))
	| WhenAtom(r) -> compose (WhenAtom(r))
	| WhenNotAtom(r) -> compose (WhenNotAtom(r))
	| NotAtom(r) -> compose (NotAtom(r))
	| IntegerConstant(r) -> compose (SignalAtom(string_of_int r))
	| ClockPlus(e1, e2) ->cmp2 (ClockPlus(e1,e2))
	| ClockMinus(e1, e2) ->cmp2 (ClockMinus(e1,e2))
	| ClockTimes(e1, e2) ->cmp2 (ClockTimes(e1,e2))
	| Delay(e1, e2) ->cmp2 (Delay(e1,e2))
	| EqualityAtom(e1, e2) ->cmp2 (EqualityAtom(e1,e2))
	| Default(e1, e2) ->cmp2 (Default(e1,e2))
	| When(e1, e2) ->cmp2 (When(e1,e2))
	| AndExp(e1, e2) ->cmp2 (AndExp(e1,e2))
	| OrExp(e1, e2) ->cmp2 (OrExp(e1,e2))
	| Times(e1, e2) ->cmp2 (Times(e1,e2))
	| Minus(e1, e2) ->cmp2 (Minus(e1,e2))
	| Plus(e1, e2) ->cmp2 (Plus(e1,e2))
	| FunctionCall(e1, e2) ->cmp2 (FunctionCall(e1,e2))
	| _ -> failwith "non encore géré" 
;;


let f_IntCst p  a i = [{assigned_signal_name = "bloubloub"; signal_expression = i}];;


let f_InAt p  a e s r  = let res = List.hd r in  print_string ("-> 6\n");
	[{assigned_signal_name = "In_at" ; signal_expression = InAtom(res.signal_expression, s)}];;

let f_Call p  a e t = let tres = List.hd (List.hd t) in  print_string ("-> 7\n");
      [{assigned_signal_name = "F_call" ; signal_expression = FunctionCall(get_id e, [tres.signal_expression])}];;
      
let f_EqAt p  a e1 e2 r1 r2 =  
  let f1 = lazy (compose2 (EqualityAtom((List.hd(List.tl r1)).signal_expression , (List.hd(List.tl r2)).signal_expression)))
  and f2 = lazy (compose2 (EqualityAtom((List.hd(List.tl r1)).signal_expression , (List.hd r2).signal_expression)))
  and f3 = lazy (compose2 (EqualityAtom((List.hd r1).signal_expression , (List.hd(List.tl r2)).signal_expression )))
  and f4 = lazy (compose (EqualityAtom((List.hd r1).signal_expression , (List.hd r2).signal_expression )))
  in  print_string ("-> 8\n"); make r1 r2 f1 f2 f3 f4
;;     

let f_Del p  a e1 e2 r1 r2 =   
  let f1 = lazy (compose2 (Delay((List.hd(List.tl r1)).signal_expression , (List.hd(List.tl r2)).signal_expression)))
  and f2 = lazy (compose2 (Delay((List.hd(List.tl r1)).signal_expression , (List.hd r2).signal_expression)))
  and f3 = lazy (compose2 (Delay((List.hd r1).signal_expression , (List.hd(List.tl r2)).signal_expression )))
  and f4 = lazy (compose (Delay((List.hd r1).signal_expression , (List.hd r2).signal_expression )))
  in  print_string ("-> 9\n");make r1 r2 f1 f2 f3 f4
;;     

let f_ClkP p  a e1 e2 r1 r2 =  
  let f1 = lazy (compose2 (ClockPlus((List.hd(List.tl r1)).signal_expression , (List.hd(List.tl r2)).signal_expression)))
  and f2 = lazy (compose2 (ClockPlus((List.hd(List.tl r1)).signal_expression , (List.hd r2).signal_expression)))
  and f3 = lazy (compose2 (ClockPlus((List.hd r1).signal_expression , (List.hd(List.tl r2)).signal_expression )))
  and f4 = lazy (compose (ClockPlus((List.hd r1).signal_expression , (List.hd r2).signal_expression )))
  in  print_string ("-> 10\n");make r1 r2 f1 f2 f3 f4
;;     
 
let f_ClkM p  a e1 e2 r1 r2 =   
  let f1 = lazy (compose2 (ClockMinus((List.hd(List.tl r1)).signal_expression , (List.hd(List.tl r2)).signal_expression)))
  and f2 = lazy (compose2 (ClockMinus((List.hd(List.tl r1)).signal_expression , (List.hd r2).signal_expression)))
  and f3 = lazy (compose2 (ClockMinus((List.hd r1).signal_expression , (List.hd(List.tl r2)).signal_expression )))
  and f4 = lazy (compose (ClockMinus((List.hd r1).signal_expression , (List.hd r2).signal_expression )))
  in  print_string ("-> 11\n");make r1 r2 f1 f2 f3 f4
;;     

let f_ClkT p  a e1 e2 r1 r2 =  
  let f1 = lazy (compose2 (ClockTimes((List.hd(List.tl r1)).signal_expression , (List.hd(List.tl r2)).signal_expression)))
  and f2 = lazy (compose2 (ClockTimes((List.hd(List.tl r1)).signal_expression , (List.hd r2).signal_expression)))
  and f3 = lazy (compose2 (ClockTimes((List.hd r1).signal_expression , (List.hd(List.tl r2)).signal_expression )))
  and f4 = lazy (compose (ClockTimes((List.hd r1).signal_expression , (List.hd r2).signal_expression )))
  in print_string ("-> 12\n"); make r1 r2 f1 f2 f3 f4
;;     

let f_Def p  a e1 e2 r1 r2 = 
  let f1 = lazy (compose2 (Default((List.hd(List.tl r1)).signal_expression , (List.hd(List.tl r2)).signal_expression)))
  and f2 = lazy (compose2 (Default((List.hd(List.tl r1)).signal_expression , (List.hd r2).signal_expression)))
  and f3 = lazy (compose2 (Default((List.hd r1).signal_expression , (List.hd(List.tl r2)).signal_expression )))
  and f4 = lazy (compose (Default((List.hd r1).signal_expression , (List.hd r2).signal_expression )))
  in  print_string ("-> 13\n");make r1 r2 f1 f2 f3 f4
;;     

let f_Wn p  a e1 e2 r1 r2 = 
  let f1 = lazy (compose2 (When((List.hd(List.tl r1)).signal_expression , (List.hd(List.tl r2)).signal_expression))) 
  and f2 = lazy (compose2 (When((List.hd(List.tl r1)).signal_expression , (List.hd r2).signal_expression))) 
  and f3 = lazy (compose2 (When((List.hd r1).signal_expression , (List.hd(List.tl r2)).signal_expression ))) 
  and f4 = lazy (compose (When((List.hd r1).signal_expression , (List.hd r2).signal_expression )))
  in  print_string ("-> 14\n");make r1 r2 f1 f2 f3 f4
;;

let f_And p  a e1 e2 r1 r2 = 
  let f1 = lazy (compose2 (AndExp((List.hd(List.tl r1)).signal_expression , (List.hd(List.tl r2)).signal_expression))) 
  and f2 = lazy (compose2 (AndExp((List.hd(List.tl r1)).signal_expression , (List.hd r2).signal_expression))) 
  and f3 = lazy (compose2 (AndExp( (List.hd r1).signal_expression , (List.hd(List.tl r2)).signal_expression ))) 
  and f4 = lazy (compose (AndExp( (List.hd r1).signal_expression , (List.hd r2).signal_expression )))
  in  print_string ("-> 15\n");make r1 r2 f1 f2 f3 f4
;;

let f_Or p  a e1 e2 r1 r2 = 
  let f1 = lazy (compose2 (OrExp((List.hd(List.tl r1)).signal_expression , (List.hd(List.tl r2)).signal_expression))) 
  and f2 = lazy (compose2 (OrExp((List.hd(List.tl r1)).signal_expression , (List.hd r2).signal_expression))) 
  and f3 = lazy (compose2 (OrExp( (List.hd r1).signal_expression , (List.hd(List.tl r2)).signal_expression ))) 
  and f4 = lazy  (compose (OrExp( (List.hd r1).signal_expression , (List.hd r2).signal_expression )))
  in  print_string ("-> 16\n");make r1 r2 f1 f2 f3 f4
;; 

let f_P p  a e1 e2 r1 r2 = 
  let f1 = lazy (compose2 (Plus((List.hd(List.tl r1)).signal_expression , (List.hd(List.tl r2)).signal_expression))) 
  and f2 = lazy (compose2 (Plus((List.hd(List.tl r1)).signal_expression , (List.hd r2).signal_expression))) 
  and f3 = lazy (compose2 (Plus( (List.hd r1).signal_expression , (List.hd(List.tl r2)).signal_expression ))) 
  and f4 = lazy (compose (Plus( (List.hd r1).signal_expression , (List.hd r2).signal_expression )))
  in print_string ("-> 17\n"); make r1 r2 f1 f2 f3 f4
;;

let f_M p  a e1 e2 r1 r2 = 
  let f1 = lazy (compose2 (Minus((List.hd(List.tl r1)).signal_expression , (List.hd(List.tl r2)).signal_expression))) 
  and f2 = lazy (compose2 (Minus((List.hd(List.tl r1)).signal_expression , (List.hd r2).signal_expression))) 
  and f3 = lazy (compose2 (Minus( (List.hd r1).signal_expression , (List.hd(List.tl r2)).signal_expression ))) 
  and f4 = lazy (compose (Minus( (List.hd r1).signal_expression , (List.hd r2).signal_expression )))
  in  print_string ("-> 18\n");make r1 r2 f1 f2 f3 f4
;;

let f_T p  a e1 e2 r1 r2 = 
  let f1 = lazy (compose2 (Times((List.hd(List.tl r1)).signal_expression , (List.hd(List.tl r2)).signal_expression))) 
  and f2 = lazy (compose2 (Times((List.hd(List.tl r1)).signal_expression , (List.hd r2).signal_expression))) 
  and f3 = lazy (compose2 (Times( (List.hd r1).signal_expression , (List.hd(List.tl r2)).signal_expression ))) 
  and f4 = lazy (compose (Times( (List.hd r1).signal_expression , (List.hd r2).signal_expression )))
  in  print_string ("-> 1\n");make r1 r2 f1 f2 f3 f4
;;


let rec it_signal_expression_list (p) (a)
    fEnVarAt fSigAt fClkP fClkM fClkT fDel fEqAt fInAt fDef fWn fWnAt fWnNAt fNAt fAnd fOr fIntCst fCall fP fM fT = 
    let rec traitl = function
		| [] -> []
		| e::l -> 
	(it_signal_expression p  a fEnVarAt fSigAt fClkP fClkM fClkT fDel fEqAt fInAt fDef fWn fWnAt fWnNAt fNAt fAnd fOr fIntCst fCall fP fM fT e) 
			  :: (traitl l)
      in (traitl)
and it_signal_expression (p) (a)
    fEnVarAt fSigAt fClkP fClkM fClkT fDel fEqAt fInAt fDef fWn fWnAt fWnNAt fNAt fAnd fOr fIntCst fCall fP fM fT =
	let rec trait t =(* print_string ("OOO \n>>>>"^str_signal_expression t ^"<<<<\n");*)match t with
		| EnumVariantAtom(i) -> fEnVarAt p  a t 
		| SignalAtom(i) -> fSigAt p  a t
		| ClockPlus(e1, e2) -> fClkP p  a e1 e2 (trait e1) (trait e2)
		| ClockMinus(e1, e2) -> fClkM p  a e1 e2 (trait e1) (trait e2)
		| ClockTimes(e1, e2) -> fClkT p  a e1 e2 (trait e1) (trait e2)
		| Delay(e1, e2) -> fDel p  a e1 e2 (trait e1) (trait e2)
		| EqualityAtom(e1, e2) -> fEqAt p  a e1 e2 (trait e1) (trait e2)
		| InAtom(e, s)-> fInAt p  a e s (trait e)
		| Default(e1, e2) -> fDef p  a e1 e2 (trait e1) (trait e2)
		| When(e1, e2) -> fWn p  a e1 e2 (trait e1) (trait e2)
		| WhenAtom(i)-> fWnAt p  a t
		| WhenNotAtom(i)-> fWnNAt p  a t
		| NotAtom(i)-> fNAt p  a t
		| AndExp(e1, e2) -> fAnd p  a e1 e2 (trait e1) (trait e2)
		| OrExp(e1, e2)-> fOr p  a e1 e2 (trait e1) (trait e2)
		| IntegerConstant(i) ->  fIntCst p  a t
		| Plus(e1,e2) -> fP p  a e1 e2 (trait e1) (trait e2)
		| Minus(e1,e2) -> fM p  a e1 e2 (trait e1) (trait e2)
		| Times(e1,e2) -> fT p  a e1 e2 (trait e1) (trait e2)
		| FunctionCall(i, sel)-> fCall p  a t 
    (it_signal_expression_list p  a fEnVarAt fSigAt fClkP fClkM fClkT fDel fEqAt fInAt fDef fWn fWnAt fWnNAt fNAt fAnd fOr fIntCst fCall fP fM fT sel)
	in (trait)
;;

(*let replace_assign nv p a = [{assigned_signal_name ="blaaa"; signal_expression = nv}];;*)
let replace_assign nv p  a_cur = it_signal_expression p  a_cur
    (f_EnVarAt) 
    (f_SigAt) 
    (f_ClkP) 
    (f_ClkM) 
    (f_ClkT) 
    (f_Del) 
    (f_EqAt) 
    (f_InAt) 
    (f_Def) 
    (f_Wn) 
    (f_WnAt) 
    (f_WnNAt) 
    (f_NAt) 
    (f_And) 
    (f_Or) 
    (f_IntCst) 
    (f_Call) 
    (f_P) 
    (f_M) 
    (f_T) nv

let cvrt_inst (p:process) (a_cur:instantiation) = 
    let rec cvrt = function
(*	match (p.header.signal_declarations.output_signal_list, a.instance_output_signals) with*)
	    | ([],[]) -> []
	    | (d::r, id::l) -> let tmp_a = (List.find ( fun e -> e.assigned_signal_name = d.signal_name ) p.body.assignment_list) 
				in let nv_expr_l = replace_assign 
								tmp_a.signal_expression 
								p
								a_cur
				in let debut =
				{ 
					assigned_signal_name = id;
					signal_expression = (List.hd nv_expr_l).signal_expression;
				} :: (cvrt (r,l))
				in if (List.length nv_expr_l) > 1 then (List.tl nv_expr_l)@debut else debut
	    | (_,_) -> raise (Incompatible_outputs)
    in cvrt (p.header.signal_declarations.output_signal_list, a_cur.instance_output_signals)
;;

let cvrt_assign_inst (p:process) (assign_cur(*:assignment_list*)) = (*inst_cur = (assign,inst);;*)
    let rec cvrt = function (* va parcourir les intanciations *)
	| [] -> (assign_cur,[]) (* rend la liste des assign telle qu'elle si vide et la liste vide *)
	| e_c::l_c -> let (r_assign, r_inst) = cvrt l_c in 
		    if e_c.instance_process_name = p.header.process_name 
			then let n_a = cvrt_inst p e_c in (n_a@r_assign,r_inst) (* append car il peut y avoir plusieurs sorties, donc, plusieurs résultat *)
			else (r_assign, e_c::r_inst)
    in cvrt
    
let cvrt_body (p:process) (cur_p :process) = 
   let b_cur = cur_p.body
   and constr_l = cvrt_const p cur_p
   in let (assign_l, inst_l) = cvrt_assign_inst p b_cur.assignment_list b_cur.instantiation_list 
    in {
	assignment_list = assign_l;
	constraint_list = b_cur.constraint_list@constr_l;
	instantiation_list = inst_l;
    }
;;

let cvrt_process (cur_p: process) (p:process) = { 
    header = cur_p.header;
    body = cvrt_body p cur_p;
};;
 
let check_processes (p : process) =
    let rec check = function
	| [] -> []
	| e::l -> (*print_string ("..........................\nCheck  processes : \n" ^ Ter_toString.str_process [e] ^"..........................\n"); *)
	(cvrt_process e p) :: check l
    in check
;;

let rec cvrt_processes (p : process list) = match p with
	| [] -> []
	| [e] -> [e]
	| e::l -> (*print_string ("..........................\nCvrt processes : \n" ^ Ter_toString.str_process [e] ^"..........................\n"); *)
	let res = (check_processes e l) in 
			if res = l
			    then  e::(cvrt_processes res) 
			    else e::(cvrt_processes res)
;;

let cvrt_spec (sp:specification) = {
	process_list = cvrt_processes sp.process_list;
	type_declaration_list = sp.type_declaration_list;
	procedure_declaration_list = sp.procedure_declaration_list;
}
;;