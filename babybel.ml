open Ast_mapper
open Asttypes
open Parsetree

exception Scanning_error of Lexing.position * string
exception Syntax_error of Lexing.position
exception Some_error of string

let file_name = "unknown"

let sigma : Usf.signature ref = ref []

(* Parsing *)

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

(* Session management *)

let session_file_name = "session.bb"

let save_session (s : Usf.signature) : unit =
  let f = open_out_bin session_file_name in
  Marshal.to_channel f !sigma [] ;
  close_out_noerr f

let load_session unit : unit =
  try
    let f = open_in_bin session_file_name in
    sigma := Marshal.from_channel f ;
    (* print_string "Session file loaded\n" ; *)
    close_in_noerr f
  with _ -> print_string "No session loaded\n" ; ()

(* The rewriter *)

let expr = Astgen.expression
let typ = Astgen.core_type

let process_value_binding (binding : value_binding) : value_binding =
  let extract_annotation (_, payload) =
    match payload with
    | PStr [str_item] -> (match str_item.pstr_desc with
			  | Pstr_eval ({pexp_desc = Pexp_constant(Const_string(ann, _))}, _) ->
			     ann
			  | _ -> raise (Some_error "type annotation has an unexpected structure"))
    | PStr _ -> raise (Some_error "really did not expect more than one structure here")
    | _ -> raise (Some_error "type annotation on unexpected payload")

  in
  try
    let vs, typ_ann = parse Sfparser.typ_ann
			    (extract_annotation (List.find (fun ({txt = t}, _) -> t = "type")
							   binding.pvb_pat.ppat_attributes))
    in

    let pat_no_ann = {binding.pvb_pat with ppat_attributes = []} in
    let tp = Astgen.typ_ann_to_ast vs typ_ann in
    let abstract_type_var e tv =
      expr (Pexp_newtype (tv, e))
    in
    let inner_expr = expr(Pexp_constraint (binding.pvb_expr, tp)) in
    let body = List.fold_left abstract_type_var inner_expr vs in
    { binding with
      pvb_expr = body
    ; pvb_pat = pat_no_ann (* MMM removes all other the attributes also *)
    }
  with
    Not_found -> binding

let is_signature : structure_item -> bool = function
  | {pstr_desc = Pstr_attribute({txt = "signature"}, _)} -> true
  | _ -> false

let expand_signature : structure_item -> structure = function
  | {pstr_desc = Pstr_attribute({txt = "signature"}
			       , PStr [{pstr_desc =
					  Pstr_eval({pexp_desc =
						       Pexp_constant (Const_string (s, _))},_)}])} ->
     let sigma' = parse Sfparser.decls s in
     if !sigma = []
     then sigma := sigma'
     else raise (Some_error "Multiple declaration blocks in the same session") ;
     save_session !sigma ;
     Astgen.decls_to_ast sigma'
  | _ -> raise (Some_error "Violation: expand_signature called on an element lacking the right attribute")

let rec process_structure : structure -> structure = function
  | [] -> []
  | st::sts when is_signature st -> expand_signature st @ process_structure sts
  | st::sts -> st::(process_structure sts)

let babybel_mapper (argv : string list) : Ast_mapper.mapper =
  { default_mapper with
    (* generate the signature and the SF *)
    structure = (fun mapper structure -> default_mapper.structure mapper (process_structure structure))
    (* process type annotations *)
  ; structure_item = (fun mapper item ->
    		      match item with
    		      | { pstr_desc = Pstr_value (rec_flag, bindings)} ->
    			 let new_desc = Pstr_value(rec_flag, List.map process_value_binding bindings)
  		         (* the type annotations were removed and we can continue the mapping *)
    			 in default_mapper.structure_item mapper { item with pstr_desc = new_desc }
    		      | other -> default_mapper.structure_item mapper other)
  (* translate tems in expressions *)
  ; expr = (fun mapper expr ->
  	    match expr with
  	    | { pexp_desc = Pexp_constant (Const_string (s, Some "t")) } ->
  	       load_session() ;
  	       let m = Index.index !sigma (parse Sfparser.ctx_term_expr s) in
  	       Astgen.t1_to_ast m
  	    | other -> default_mapper.expr mapper other)
  (* translate patterns in expressions  *)
  ; pat = (fun mapper pat ->
  	   match pat with
  	   | { ppat_desc = Ppat_constant (Const_string (s, Some "p"))} ->
  	      load_session () ;
  	      let m = Index.index !sigma (parse Sfparser.ctx_term_expr s) in
  	      Astgen.t1_to_pat_ast m
  	   | other -> default_mapper.pat mapper other)
  }

let () = register "babybel_mapper" babybel_mapper
