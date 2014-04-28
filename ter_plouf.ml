open Ter_util;;
open Ter_exception;;
open Ms_identifier;;
open Ms_syntax_tree;;
open SyntaxTree ;;

let id = function
  | a -> a
;;

let get_name a = a.assigned_signal_name;;
let get_expr a = a.signal_expression;;

let get_id = function
  |EnumVariantAtom(i) -> i
  | SignalAtom(i) -> i 
  | WhenAtom(i) -> i
  | WhenNotAtom(i) -> i
  | NotAtom(i) -> i
  | _ -> failwith "pas utilisé id ?"

let rename new_n = function
  |EnumVariantAtom(_) -> EnumVariantAtom(new_n)
  | SignalAtom(_) -> SignalAtom(new_n) 
  | WhenAtom(_) -> WhenAtom(new_n)
  | WhenNotAtom(_) -> WhenNotAtom(new_n)
  | NotAtom(_) -> NotAtom(new_n)
(*| FunctionCall of Identifier.t*(signal_expression list)
| AndExp of signal_expression*signal_expression
  | OrExp of signal_expression*signal_expression
  | IntegerConstant of int
  | Plus of signal_expression * signal_expression
  | Minus of signal_expression * signal_expression
  | Times of signal_expression * signal_expression
  | ClockPlus of signal_expression*signal_expression
  | ClockMinus of signal_expression*signal_expression
  | ClockTimes of signal_expression*signal_expression
  | Delay of signal_expression*signal_expression
  | EqualityAtom of signal_expression*signal_expression
  | InAtom of signal_expression*typed_variant_set
  | Default of signal_expression*signal_expression
  | When of signal_expression*signal_expression*)
  | _ -> failwith "pas utilisé rename ?"
;;

let compose2B b r= 
  let loc_n = newStr in
    {assigned_signal_name = "#fDef" ; signal_expression = (rename loc_n b);}::
    [{assigned_signal_name = loc_n ; signal_expression = id r}] 
;;

let compose2 r = 
  let loc_n = newStr in
    {assigned_signal_name = "#fDef" ; signal_expression = SignalAtom(loc_n);}::
    [{assigned_signal_name = loc_n ; signal_expression = id r}] 
;;

let compose r = (*let res =*)
    [{assigned_signal_name = "#fDef" ;  signal_expression = id r}](* in print_string("\t ici ?\n"); res *)
;;

let compose_constr op l_name r_name =
    {constraint_kind = op ; left_signal_name = l_name ; right_signal_name = r_name}

let make r1 r2 f1 f2 f3 f4 = 
 let fl2 l fa fb =
    if l > 1
    then if l <= 2 then Lazy.force fa
	else raise (Bad_construction "l2 plus grande que 2 ???")
    else Lazy.force fb
    in let l1 = List.length r1 
	and l2 = List.length r2
	in
	  if l1 > 1 
	  then if l1 <= 2 
		then (fl2 l2 f1 f2)
	      else raise (Bad_construction "l1 plus grande que 1 ???")
	  else (fl2 l2 f3 f4)
;;