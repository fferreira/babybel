open Ast_mapper
open Asttypes
open Parsetree

let sigma : Usf.signature ref = ref []

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
  let remove_pat_type_attribute p =
    { p with
      ppat_attributes = List.filter (fun ({txt = t}, _) -> not(t = "type")) p.ppat_attributes
    }
  in
  let extract_annotation (_, payload) =
    match payload with
    | PStr [str_item] -> (match str_item.pstr_desc with
			  | Pstr_eval ({pexp_desc = Pexp_constant(Const_string(ann, _))}, _) ->
			     ann
			  | _ -> raise (Error.Some_error "type annotation has an unexpected structure"))
    | PStr _ -> raise (Error.Some_error "really did not expect more than one structure here")
    | _ -> raise (Error.Some_error "type annotation on unexpected payload")

  in
  try
    let typ_ann_str = (extract_annotation (List.find (fun ({txt = t}, _) -> t = "type")
						     binding.pvb_pat.ppat_attributes))
    in
    let split_on_first_dot s =
      try
	let n = String.index s '.' in
	(Str.string_before s n, Str.string_after s (n +1))
      with
	Not_found -> ("", s)
    in
    let a, b = split_on_first_dot typ_ann_str in
    let vs, typ_ann_str = Str.split (Str.regexp " ") a, b in

    let poly_quantify vs t =
      if List.length vs > 0 then
	typ (Ptyp_poly (vs, t))
      else
	t
    in

    (* removes the annotation and adds the type constraint *)
    let pat_no_att = remove_pat_type_attribute binding.pvb_pat in
    let pat_with_constraint = { pat_no_att with
				ppat_desc = Ppat_constraint (pat_no_att
		     					    , poly_quantify
		     						vs
								(* HACK ALERT: in the call to typ_ann_to_ast takes the [] list
                                 instead of vs because that way the variables become variables
                                 instead of type constructors that will only be bound in the
                                 body of the function *)
		     						(Astgen.typ_ann_to_ast Astgen.Variables [] typ_ann_str))
			      }
    in
    let tp = Astgen.typ_ann_to_ast Astgen.Constructors vs typ_ann_str in
    let abstract_type_var e tv =
      expr (Pexp_newtype (tv, e))
    in
    let inner_expr = expr(Pexp_constraint (binding.pvb_expr, tp)) in
    let body = List.fold_left abstract_type_var inner_expr vs in
    { binding with
      pvb_expr = body
    ; pvb_pat = pat_with_constraint
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
     let sigma' = Putil.parse Sfparser.decls s in
     if !sigma = []
     then sigma := sigma'
     else raise (Error.Some_error "Multiple declaration blocks in the same session") ;
     save_session !sigma ;
     Astgen.decls_to_ast sigma'
  | _ -> raise (Error.Some_error "Violation: expand_signature called on an element lacking the right attribute")

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
  	       let m = Index.index !sigma (Putil.parse Sfparser.ctx_term_expr s) in
  	       Astgen.t1_to_ast m
  	    | other -> default_mapper.expr mapper other)
  (* translate patterns in expressions  *)
  ; pat = (fun mapper pat ->
  	   match pat with
  	   | { ppat_desc = Ppat_constant (Const_string (s, Some "p"))} ->
  	      load_session () ;
  	      let m = Index.index !sigma (Putil.parse Sfparser.ctx_term_expr s) in
  	      Astgen.t1_to_pat_ast m
  	   | other -> default_mapper.pat mapper other)
  }

let () = register "babybel_mapper" babybel_mapper
