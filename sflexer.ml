open Sfparser

exception Error of string

let regexp nl  = ('\n' | '\r' | "\r\n" | "\n\r")
let regexp tab = ['\t''\x0b']
let regexp wsp = [' ''\t']
let regexp digit = ['0' - '9']+
let regexp numeral = digit+

let regexp lower = ['a'-'z']
let regexp upper = ['A'-'Z']

let regexp identifier = lower (lower | upper | digit)*

(* Managing source code positions *)

let initial_pos file_name = { Lexing.pos_fname = file_name
			    ; Lexing.pos_lnum = 1
			    ; Lexing.pos_bol = 0
			    ; Lexing.pos_cnum = 0
			    }
let add_line pos = { pos with
		     Lexing.pos_lnum = pos.Lexing.pos_lnum +1
		   ; Lexing.pos_bol = pos.Lexing.pos_bol + pos.Lexing.pos_cnum
		   ; Lexing.pos_cnum = 0
		   }
let add_word pos length = { pos with Lexing.pos_cnum = pos.Lexing.pos_cnum + length }

let remove_first (s : string) : string =
  if String.length s = 0 then raise (Error "String to short")
  else let acc = ref "" in
       String.iteri (fun n c -> if n <> 0 then acc := !acc ^ String.make 1 c) s ;
       !acc

let rec main_scanner pos = lexer
| wsp | tab -> main_scanner (add_word pos 1) lexbuf (* ignore whitespace *)
| nl -> main_scanner (add_line pos) lexbuf   (* ignores new lines *)
| "(*" -> comment pos 0 lexbuf
| eof -> add_word pos (Ulexing.lexeme_length lexbuf), EOF

| ':' -> add_word pos (Ulexing.lexeme_length lexbuf), COLON
| '(' -> add_word pos (Ulexing.lexeme_length lexbuf), LPAREN
| ')' -> add_word pos (Ulexing.lexeme_length lexbuf), RPAREN
| '[' -> add_word pos (Ulexing.lexeme_length lexbuf), LSQ
| ']' -> add_word pos (Ulexing.lexeme_length lexbuf), RSQ
| "{|" -> add_word pos (Ulexing.lexeme_length lexbuf), LBOX
| "|}" -> add_word pos (Ulexing.lexeme_length lexbuf), RBOX
(* | '/' -> add_word pos (Ulexing.lexeme_length lexbuf), BAR *)
| '.' -> add_word pos (Ulexing.lexeme_length lexbuf), DOT
| ',' -> add_word pos (Ulexing.lexeme_length lexbuf), COMMA
| ';' -> add_word pos (Ulexing.lexeme_length lexbuf), SEMICOLON
| '^' -> add_word pos (Ulexing.lexeme_length lexbuf), SHIFT
| '\\' -> add_word pos (Ulexing.lexeme_length lexbuf), FN
| "->" -> add_word pos (Ulexing.lexeme_length lexbuf), ARR
| "type" -> add_word pos (Ulexing.lexeme_length lexbuf), TYPE
| "|-" -> add_word pos (Ulexing.lexeme_length lexbuf), VDASH
| numeral -> add_word pos (Ulexing.lexeme_length lexbuf), NUM (int_of_string (Ulexing.utf8_lexeme lexbuf))
| identifier -> add_word pos (Ulexing.lexeme_length lexbuf), ID (Ulexing.utf8_lexeme lexbuf)
| '\'' identifier -> add_word pos (Ulexing.lexeme_length lexbuf), MVAR (remove_first (Ulexing.utf8_lexeme lexbuf))

and comment pos level = lexer
		      | "*)" -> if level = 0 then main_scanner (add_word pos 2) lexbuf else comment (add_word pos 2) (level-1) lexbuf
		      | "(*" -> comment (add_word pos 2) (level+1) lexbuf
		      | "\n" -> comment (add_line pos) level lexbuf
		      | _ -> comment (add_word pos (Ulexing.lexeme_length lexbuf)) level lexbuf
