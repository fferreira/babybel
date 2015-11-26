open Ast_mapper
open Asttypes
open Parsetree

exception Scanning_error of Lexing.position * string
exception Syntax_error of Lexing.position

let file_name = "some_filename.bbel"

let parser menhir_parser lexbuf =
  let position = ref (Sflexer.initial_pos file_name) in
  let lexer () =
    let ante_position = !position in
    let post_position, token = Sflexer.main_scanner !position lexbuf in
    let () = position := post_position in (* Lexing.({!position with pos_lnum = !position.pos_lnum + nlines;}) in *)
    (token, ante_position, post_position) in
  let revised_parser = MenhirLib.Convert.Simplified.traditional2revised menhir_parser
  in try
       revised_parser lexer
    with
      | Sflexer.Error x -> raise (Scanning_error (!position, x))
      | Sfparser.Error  -> raise (Syntax_error !position)

let parse p s =
  let lexbuf = Ulexing.from_utf8_string s in
  parser p lexbuf

let babybel_mapper (argv : string list) : Ast_mapper.mapper =
  { default_mapper with
    expr = (fun mapper expr ->
  	    match expr with
  	    | { pexp_desc = Pexp_constant (Const_string (s, Some "def")) } ->
	       Astgen.decls_to_ast (parse Sfparser.decls s)
  	    | { pexp_desc = Pexp_constant (Const_string (s, Some "term")) } ->
	       Astgen.term_to_ast (parse Sfparser.term_expr s)
  	    | other -> default_mapper.expr mapper other)
  ; pat = (fun mapper pat ->
	   match pat with
	   | { ppat_desc = Ppat_constant (Const_string (s, Some "p"))} ->
	      Astgen.term_to_pat_ast (parse Sfparser.term_expr s)
	   | other -> default_mapper.pat mapper other)
  }

let () = register "babybel_mapper" babybel_mapper
