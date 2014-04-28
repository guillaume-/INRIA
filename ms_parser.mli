type token =
  | Lidentifier of (string)
  | Leof
  | Larrow
  | Lopen
  | Lclose
  | Lsqopen
  | Lsqclose
  | Lassign
  | Lclock
  | Lequal
  | Lleq
  | Lless
  | Lplus
  | Lminus
  | Ltimes
  | Lsemicolon
  | Lcolon
  | Linput
  | Loutput
  | Lcomma
  | Lbar
  | Lclockplus
  | Lclockminus
  | Lclocktimes
  | Ldelay
  | Lnot
  | Lexclusive
  | Lprocess
  | Lprocedure
  | Lwhen
  | Ldefault
  | Lcall
  | Land
  | Lor
  | Lend
  | Llocal
  | Lsubmodule
  | Ltype
  | Lenum
  | Lin
  | Lout
  | Lwhere
  | Lconstant
  | LINT of (int)

val g_specification :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Ms_syntax_tree.SyntaxTree.specification
