%{
  (* Copyright 2013 Dumitru Potop Butucaru ( email: dumitru.potop_butucaru@inria.fr ).

	 This program is free software: you can redistribute it and/or
	 modify it under the terms of the GNU General Public License as
	 published by the Free Software Foundation, either version 3 of the
	 License, or (at your option) any later version.

	 This program is distributed in the hope that it will be useful,
	 but WITHOUT ANY WARRANTY; without even the implied warranty of
	 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	 GNU General Public License for more details.

	 You should have received a copy of the GNU General Public License
	 along with this program.  If not, see <http://www.gnu.org/licenses/>
  *)

  open Ms_identifier ;;
  open Ms_syntax_tree ;;
  open Ms_idhtbl ;;
  open SyntaxTree ;;

  let parser_debug_mode = true ;;
  let parser_debug_print text =
	if parser_debug_mode 
	then (Printf.printf "Parser debug: %s\n" text ; flush stdout)
	else ()
  ;;
  
  let no_signal_declarations =
	(* Constant to use in the following code 
	   (facilitates factoring). 
	*)
	{
	  input_signal_list = [] ;
	  output_signal_list = [] ;
	  local_signal_list = [] ;
	} 
  ;;

  let build_signal_declarations
	  signal_direction
	  typed_signal_list_list
	  =
	let signal_declaration_list =
	  List.map
	(
	  fun (y,z) ->
		let signal_declaration =
		  {
			signal_name = y ;
			signal_type = z ;
			signal_direction = signal_direction ;
		  } 
		in
		(*
		let _ = gih_get_type z 
		and _ = gih_set_signal y signal_declaration 
		in
		*)
		  signal_declaration
	)
	typed_signal_list_list
	in
	  match signal_direction with
	| Input -> { no_signal_declarations with 
			   input_signal_list = signal_declaration_list }
	| Output -> { no_signal_declarations with 
			output_signal_list = signal_declaration_list }
	| Local -> { no_signal_declarations with 
			   local_signal_list = signal_declaration_list }
  ;;
%}

/* Terminals received from the lexer, and their types (if any). */
%token <string> Lidentifier
%token Leof
%token Larrow
%token Lopen Lclose Lsqopen Lsqclose Lassign 
%token Lclock Lequal Lleq Lless Lplus Lminus Ltimes
%token Lequal Lsemicolon Lcolon Linput Loutput Lcomma Lbar
%token Lclockplus Lclockminus Lclocktimes Ldelay
%token Lnot Lexclusive

/* keywords */
%token Lprocess Lprocedure Lwhen Ldefault Lcall Land Lor
%token Lend Llocal Lsubmodule 
%token Ltype Lenum Lin Lout Lwhere
%token Lconstant
%token<int> LINT

%nonassoc Lwhen Ldefault Lequal Lin Lclockplus Lclockminus Lclocktimes Ldelay 
%nonassoc Land Lor

/* Non-terminals and their types. */
%type <Ms_syntax_tree.SyntaxTree.specification> g_specification

%start g_specification

%%

g_specification : 
  Leof
  {
	{
	 process_list = [] ;
	 type_declaration_list = [] ;
	 procedure_declaration_list = [] ;
	}
  }
| g_type_definition g_specification
  { 
	parser_debug_print "Parser:g_specification: complete type definition" ; 
	{ $2 with 
	type_declaration_list = $1::($2.type_declaration_list)
	}
  }
| g_procedure_definition g_specification
  { 
	parser_debug_print "Parser:g_specification: complete procedure definition" ; 
	{ $2 with 
	procedure_declaration_list = $1::($2.procedure_declaration_list)
	}
  }
| g_process g_specification 
  { 
	parser_debug_print "Parser:g_specification: complete process definition"; 
	{
		$2 with process_list = $1::($2.process_list)
	}
  }
;
  
g_type_definition :
Ltype Lidentifier Lsemicolon
{
	let type_declaration = {
		tv_type_name = Identifier.of_string $2 ;
		variant_set = IdentifierSet.empty ;
	} in (
		gih_set_type type_declaration.tv_type_name type_declaration ;
		type_declaration
	)
}
| Ltype Lidentifier Lequal Lenum Lopen g_nv_identifier_list Lclose Lsemicolon
{
	let type_declaration = {
		tv_type_name = Identifier.of_string $2 ;
		variant_set = IdentifierSet.from_list $6 ;
	} in
	gih_set_type type_declaration.tv_type_name type_declaration;
	List.iter ( fun enum_variant -> gih_set_enum_variant enum_variant type_declaration) $6;
	type_declaration
};

g_procedure_definition : 
  Lprocedure Lidentifier 
  Lopen g_identifier_list Lclose Larrow 
  Lidentifier Lsemicolon
  {
	let procedure_definition =
	  {
			procedure_name = Identifier.of_string $2 ;
			procedure_input_list = $4 ;
			procedure_output = Identifier.of_string $7 ;
	  }
	in
	  (* Check that the types of the input and output are already defined.
	  let _ =  gih_get_type (Identifier.of_string $7)
	  and _ =
	  *)
	List.map
	  ( fun type_name -> gih_get_type type_name )
	  $4 
	  in
	(* Add the new procedure name *)
	gih_set_procedure (Identifier.of_string $2) procedure_definition ;
	(* Produce the result *)
	procedure_definition
  }
;

g_process :
	g_header Lend Lsemicolon 
	{ 
		parser_debug_print "Parser: ProcessV1 completed" ; 
		let process =
		{
			header = (fst $1);
			body = (snd $1);
		}
		in
		gih_set_process process.header.process_name process;
		process
	}
;

g_local_process :
	g_header Lend
	{ 
		parser_debug_print "Parser: ProcessV1 completed" ; 
		let process =
		{
			header = (fst $1);
			body = (snd $1);
		}
		in
		process
	}
;

g_header :
  Lprocess Lidentifier Lequal Lopen 
  g_interface_signal_declaration_list Lclose
  g_body
  { 
	parser_debug_print "Parser: Header (TER no where's rule) completed" ;
	(
		{
			process_name = Identifier.of_string $2 ;
			signal_declarations = $5 ;
			local_process_list = [] ;
		},
		$7
	)
  }
| Lprocess Lidentifier Lequal Lopen
  g_interface_signal_declaration_list Lclose 
  g_body Lwhere g_locals
  { 
	parser_debug_print "Parser: Header (TER where's rule) completed" ;
	match $9 with
	(signal_declarations,local_processes,constant_assignments) ->
	(
		{
			process_name = Identifier.of_string $2 ;
			signal_declarations = {
				$5 with local_signal_list = signal_declarations.local_signal_list
			};
			local_process_list = local_processes ;
		},
		{
			$7 with assignment_list = $7.assignment_list@(constant_assignments);
		}
	)
  }
;

g_interface_signal_declaration_list :
  g_interface_signal_declaration { $1 }
| g_interface_signal_declaration g_interface_signal_declaration_list 
	{ 
	  {
		input_signal_list = $1.input_signal_list@$2.input_signal_list ;
		output_signal_list = $1.output_signal_list@$2.output_signal_list ;
		local_signal_list = $1.local_signal_list@$2.local_signal_list ;
	  }
	}
;

g_interface_signal_declaration : 
  g_signal_direction g_typed_signal_list_list
  {  build_signal_declarations $1 $2 }
;

g_signal_direction : 
	Linput { Input }
	| Loutput { Output }
;

g_typed_signal_list_list :
	g_typed_signal_list Lsemicolon { $1 }
	| g_typed_signal_list Lsemicolon g_typed_signal_list_list { $1@$3 }
;

g_typed_signal_list :
	Lidentifier g_nv_identifier_list 
	{
		let type_id = Identifier.of_string $1
		in
		List.map ( fun signal_id -> (signal_id,type_id) ) $2
	}
;

g_body :
	Lopen Lbar g_statement_list Lclose 
	{ 
		parser_debug_print "Parser: Body completed" ; 
		$3 
	}
;
  
g_statement_list :
	g_statement Lbar { $1 }
	| g_statement Lbar g_statement_list 
	{ 
	  {
	assignment_list = 
	  $1.assignment_list@$3.assignment_list ;
	constraint_list = 
	  $1.constraint_list@$3.constraint_list ;
	instantiation_list = 
	  $1.instantiation_list@$3.instantiation_list ;
	  }
	}
;

g_statement :
g_assignment 
	{
		parser_debug_print "Parser: Assignment completed" ; 
		{
		assignment_list = [$1] ;
		constraint_list = [] ;
		instantiation_list = [] ; 
		}
	}
| g_constraint 
  { 
	parser_debug_print "Parser: Constraint completed" ;
	{
	  assignment_list = [] ;
	  constraint_list = [$1] ;
	  instantiation_list = [] ; 
	}
  }
| g_instantiation 
  { 
	parser_debug_print "Parser: Instantiation completed" ;
	{
	  assignment_list = [] ;
	  constraint_list = [] ;
	  instantiation_list = [$1] ; 
	}
  }
;

g_assignment :
	Lidentifier Lassign g_signal_expression 
	{ 
		{
			assigned_signal_name = Identifier.of_string $1 ;
			signal_expression = $3 ;
		}
	}
;

g_signal_expression :
	| g_signal_expression Lplus g_signal_expression { Plus($1,$3) }
	| g_signal_expression Lminus g_signal_expression { Minus($1,$3) }
	| g_signal_expression Ltimes g_signal_expression { Times($1,$3) }
	| LINT  { IntegerConstant $1 }
	| Lidentifier {
		let target = gih_get_target (Identifier.of_string $1) in
			match target with 
				IH_enum_variant(_) ->
					EnumVariantAtom(Identifier.of_string $1)
				| IH_signal(_) ->
					SignalAtom(Identifier.of_string $1)
				| _ ->
					SignalAtom(Identifier.of_string $1)
	}
	| g_signal_expression Ldelay g_signal_expression {Delay($1,$3)}
	| g_signal_expression Lclockplus g_signal_expression {ClockPlus($1,$3)}
	| g_signal_expression Lclockminus g_signal_expression {ClockMinus($1,$3)}
	| g_signal_expression Lclocktimes g_signal_expression {ClockTimes($1,$3)}
	| g_signal_expression Lequal g_signal_expression { EqualityAtom($1,$3) }
/***| g_signal_expression Lin g_enum_set { InAtom($1,$3) }*******************************/
	| g_signal_expression Lwhen g_signal_expression { When($1,$3) }
	| Lwhen Lidentifier { WhenAtom(Identifier.of_string $2) }
	| Lwhen Lopen Lnot Lidentifier Lclose { 
		WhenNotAtom(Identifier.of_string $4) 
	}
	| Lnot Lidentifier {
		NotAtom(Identifier.of_string $2) 
	}
	| g_signal_expression Land g_signal_expression { AndExp($1,$3) }
	| g_signal_expression Lor g_signal_expression { OrExp($1,$3) }
	| g_signal_expression Ldefault g_signal_expression { Default($1,$3) }
	| Lopen g_signal_expression Lclose { $2 }
	| Lcall Lidentifier Lopen g_signal_expression_list Lclose { 
		(*	First, I do some sanity checks.
			Here I should check that the types produced by the 
			expressions in the g_signal_expression_list correspond
			to the types specified in the definition of the 
			procedure. 
			I'm actually doing smth simpler, which is to check
			that the number of parameters correspond. :) 
		let _ = 
			let procedure = gih_get_procedure (Identifier.of_string $2) in
			if ((List.length procedure.procedure_input_list) = (List.length $4))
			then ()
			else 
				failwith ("Ms_parser:g_signal_expression: "
						^ "The numbers of formal and actual parameters are not equal.");
		in
		*)
		(* The actual construction of the result. *)
		FunctionCall((Identifier.of_string $2),$4) 
	}
;

/***************************** TO DO ****************************************************
g_enum_set :
	Lsqopen g_nv_identifier_list Lsqclose
	{
	  let base_type_name = (gih_get_enum_variant (List.hd $2)).type_name
	  in {
		type_name = base_type_name ;
		variant_set =
		List.fold_left(
			fun acc enum_var ->
			let _ = gih_get_enum_variant enum_var in
			IdentifierSet.add enum_var acc
		)
		IdentifierSet.empty
		$2
	}
};
gih_get_enum_variant :
*****************************************************************************************/

g_signal_expression_list :
	{[]}
  | g_signal_expression_nv_list { $1 }
	;

g_signal_expression_nv_list :
  g_signal_expression { [$1] }
| g_signal_expression Lcomma g_signal_expression_nv_list { $1::$3 }
	;

g_constraint : 
  Lidentifier g_constraint_kind Lidentifier 
  { 
	{
	  constraint_kind = $2 ;
	  left_signal_name = Identifier.of_string $1 ; 
	  right_signal_name = Identifier.of_string $3 ;
	} 
  } 
  ;

g_constraint_kind :
  Lclock Lequal {ClockEquality} 
| Lclock Lleq {ClockLeq}
| Lclock Lless {ClockLess}
| Lclock Lequal Lwhen {ClockWhen}
| Lclock Lequal Lwhen Lnot {ClockWhenNot}
| Lclock Lexclusive {ClockExclusive}
;

g_instantiation :
  Lsubmodule Lidentifier Lopen g_identifier_list Lclose Lopen g_signal_expression_list Lclose
  { 
	let instantiation =
	  {
	   instance_process_name = Identifier.of_string $2 ;
	   instance_output_signals = $4 ; 
	   instance_input_expressions = $7 ;
	  }
	in

	(************************************************************************************
	/* 	/!\ This check is reported later because it cann't support local processes
	/*	Check that the input list of the called process indeed corresponds 
	/*	to the input list specified when the process is defined.
	/*
	/*let _ =
	/*	let process = gih_get_process (Identifier.of_string $2) in
	/*if((List.length (process.header.signal_declarations.input_signal_list)) = (List.length $7))
	/*then()
	/*else
	/*	failwith(	"Ms_parser:g_instantiation: "
	/*				^"The numbers of formal and actual parameters are not equal.");
	/*in
	/***********************************************************************************)
	instantiation
  }
;

g_identifier_list :
{[]} 
| g_nv_identifier_list { $1 }
;

g_nv_identifier_list :
	Lidentifier { [Identifier.of_string $1] }
  | Lidentifier Lcomma g_nv_identifier_list { (Identifier.of_string $1)::$3 } 
;

g_locals :
	g_local Lsemicolon { $1 }
  | g_local Lsemicolon g_locals
	  {
	match ($1,$3) with
		((a,b,c),(d,e,f)) -> 
		(
			{
				input_signal_list = a.input_signal_list@d.input_signal_list ;
				output_signal_list = a.output_signal_list@d.output_signal_list ;
				local_signal_list = a.local_signal_list@d.local_signal_list ;
			},
			(b@e),
			(c@f)
		)
	  }
;

g_local :
g_local_process
{
	(
		no_signal_declarations,
		[$1],
		[]
	)
}
| g_typed_signal_list
{
	(
		( build_signal_declarations Local $1 ),
		[],
		[]
	)
}
| Lconstant Lidentifier Lidentifier Lequal Lidentifier
	/*	For simplicity, constants are treated as a typed signal declaration
		and an assignment. This is handled by adding an extra term to the
		locals, which is included in the body in the g_process rule . 
	*/
{
	(
		(build_signal_declarations 
			Local 
			[(Identifier.of_string $3,Identifier.of_string $2)]
		),
		[],
		[{
			assigned_signal_name = Identifier.of_string $3 ;
			signal_expression = EnumVariantAtom (Identifier.of_string $5) ;
		}]
	)
}
;

%%
