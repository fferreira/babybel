open Sfparser

exception Error of string

let regexp nl  = ('\n' | '\r' | "\r\n" | "\n\r")
let regexp tab = ['\t''\x0b']
let regexp wsp = [' ''\t']
let regexp numeral = ['0' - '9']+

let regexp lower = ['a'-'z']
let regexp upper = ['A'-'Z']

let regexp identifier = lower (lower | upper)*

(* Managing source code positions *)

let initial_pos file_name = { Lexing.pos_fname = file_name ;
			      Lexing.pos_lnum = 1 ;
			      Lexing.pos_bol = 0 ;
			      Lexing.pos_cnum = 0 }
let add_line pos = { pos with
		     Lexing.pos_lnum = pos.Lexing.pos_lnum +1 ;
		     Lexing.pos_bol = pos.Lexing.pos_bol + pos.Lexing.pos_cnum ;
		     Lexing.pos_cnum = 0}
let add_word pos length = { pos with Lexing.pos_cnum = pos.Lexing.pos_cnum + length }

let rec main_scanner pos = lexer
| wsp | tab -> main_scanner (add_word pos 1) lexbuf (* ignore whitespace *)
| nl -> main_scanner (add_line pos) lexbuf   (* ignores new lines *)
| eof -> add_word pos (Ulexing.lexeme_length lexbuf), EOF

| ':' -> add_word pos (Ulexing.lexeme_length lexbuf), COLON
| '(' -> add_word pos (Ulexing.lexeme_length lexbuf), LPAREN
| ')' -> add_word pos (Ulexing.lexeme_length lexbuf), RPAREN
| '.' -> add_word pos (Ulexing.lexeme_length lexbuf), DOT
| "->" -> add_word pos (Ulexing.lexeme_length lexbuf), ARR
| "type" -> add_word pos (Ulexing.lexeme_length lexbuf), TYPE
| "|-" -> add_word pos (Ulexing.lexeme_length lexbuf), VDASH
| identifier -> add_word pos (Ulexing.lexeme_length lexbuf), CON (Ulexing.utf8_lexeme lexbuf)
| '\'' identifier -> add_word pos (Ulexing.lexeme_length lexbuf), VAR (Ulexing.utf8_lexeme lexbuf)

and comment pos level = lexer
		      | "*)" -> if level = 0 then main_scanner (add_word pos 2) lexbuf else comment (add_word pos 2) (level-1) lexbuf
		      | "(*" -> comment (add_word pos 2) (level+1) lexbuf
		      | "\n" -> comment (add_line pos) level lexbuf
		      | _ -> comment (add_word pos (Ulexing.lexeme_length lexbuf)) level lexbuf
