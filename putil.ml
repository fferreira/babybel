(* Parsing utilities *)

exception Syntax_error of Lexing.position
exception Scanning_error of Lexing.position * string

let file_name = "unknown"

let parser (menhir_parser : (Sfparser.token, 'a) MenhirLib.Convert.traditional)
	   (lexbuf : Ulexing.lexbuf) =
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
