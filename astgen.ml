open Usf
open Sf
open Parsetree
open Asttypes
open Ast_convenience
open Longident

exception AST_gen_error of string

(* how to generate names and other configurations*)

let typ_name n = "tp_" ^ n
let con_name n = "CON_" ^ n
let unique_con_name n = "T" ^ n
let signature_typ_name = "signature"
let sf_module_name = "SyntacticFramework"
let sf_signature_typ_name = "constructor"
let sf_instance_name = "SFU"

(* Generate ASTs *)

(* let rec tp_to_ast = function *)
(*   | TConst c -> [%expr TConst [%e str c]] *)
(*   | Arr (s, t) -> [%expr Arr([%e tp_to_ast s], [%e tp_to_ast t])] *)

(* let decl_to_ast = function *)
(*   | c, Is_kind -> [%expr [%e str c], Is_kind] *)
(*   | c, Is_type t -> let ta = tp_to_ast t in [%expr [%e str c], Is_type [%e ta]] *)

(* wraps a value in a loc record *)
let wrap c = { txt = c ; loc = Location.none }

(* utility functions for dealing with ast *)

let wrap_in_signature t  =
  { ptyp_desc = Ptyp_constr ( wrap (Lident signature_typ_name), [t])
  ; ptyp_loc = Location.none
  ; ptyp_attributes = []
  }

let build_base_typ s =
  { ptyp_desc = Ptyp_constr ( wrap (Lident "base")
			    , [{ ptyp_desc = Ptyp_constr (wrap (Lident s), [])
			       ; ptyp_loc = Location.none
			       ; ptyp_attributes = []
			       }])
  ; ptyp_loc = Location.none
  ; ptyp_attributes = []
  }

let decls_to_ast ds =
  (* generate an ocaml type for each kind in the signature *)
  let generate_new_type = function
    | (n, Is_kind) ->
       (* constructors *)
       let cons = { pcd_name = wrap (unique_con_name n)
		  ; pcd_args = []
		  ; pcd_res = None
		  ; pcd_loc = Location.none
		  ; pcd_attributes = []
		  }
       in
       (* type *)
       { pstr_desc = Pstr_type ([{ ptype_name = wrap (typ_name n)
				 ; ptype_params = []
				 ; ptype_cstrs = []
				 ; ptype_kind = Ptype_variant [cons]
				 ; ptype_private = Public
				 ; ptype_manifest = None
				 ; ptype_attributes = []
				 ; ptype_loc = Location.none
				 }])
       ; pstr_loc = Location.none
       }
    | _ -> raise (AST_gen_error "Violation: generate_new_type")
  in
  (* generates the type for the signature that contains all the available constructors *)
  let generate_constr_type cons =
    (* having the constructors build the type *)
    let signature cons_trees =
       { pstr_desc = Pstr_type ([{ ptype_name = wrap signature_typ_name
				 ; ptype_params = [{ ptyp_desc = Ptyp_any
						   ; ptyp_loc = Location.none
						   ; ptyp_attributes = []
						   }, Invariant]
				 ; ptype_cstrs = []
				 ; ptype_kind = Ptype_variant cons_trees
				 ; ptype_private = Public
				 ; ptype_manifest = None
				 ; ptype_attributes = []
				 ; ptype_loc = Location.none
				 }])
       ; pstr_loc = Location.none
       }
    in
    (* generate a constructor available for the signature *)
    let generate_constructor =
      let rec generate_core_type : Usf.tp -> Parsetree.core_type = function
	| TConst n -> build_base_typ (typ_name n)
	| Arr (t1, t2) -> [%type: ([%t generate_core_type t1], [%t generate_core_type t2]) arr]
      in
      function (name, Is_type t) ->
	       { pcd_name = wrap (con_name name)
	       ; pcd_args = []
	       ; pcd_res = Some (wrap_in_signature (generate_core_type t))
	       ; pcd_loc = Location.none
	       ; pcd_attributes = []
	       }
	     | _ -> raise (AST_gen_error "Violation: generate_core_type")
    in
    signature (List.map generate_constructor cons)
  in
  (* Instance of the functor with the module applied *)
  let sf_instance =
    let module_desc d =
      { pmod_desc = d
      ; pmod_loc = Location.none
      ; pmod_attributes = []
      }
    in
    let sf_mod_apply =
      Pmod_structure
        [{pstr_desc =
            Pstr_type
              [{ ptype_name = wrap sf_signature_typ_name
	       ; ptype_params = [({ ptyp_desc = Ptyp_var "a"
				  ; ptyp_loc = Location.none
				  ; ptyp_attributes = []
				  }, Invariant)]
	       ; ptype_cstrs = []
	       ; ptype_kind = Ptype_abstract
               ; ptype_private = Public
               ; ptype_manifest =
                  Some
                    { ptyp_desc =
			Ptyp_constr ( wrap (Lident signature_typ_name)
				    , [{ ptyp_desc = Ptyp_var "a"
				       ; ptyp_loc = Location.none
				       ; ptyp_attributes = []
				       }])
		    ; ptyp_loc = Location.none
		    ; ptyp_attributes = []
		    }
	       ; ptype_attributes = []
	       ; ptype_loc = Location.none
	       }]
	 ; pstr_loc = Location.none
	 }]
    in
    { pstr_desc = Pstr_module
		    { pmb_name = wrap sf_instance_name
		    ; pmb_expr = module_desc (Pmod_apply
						( module_desc (Pmod_ident (wrap (Lident sf_module_name)))
						, module_desc sf_mod_apply))
		    ; pmb_attributes = []
		    ; pmb_loc = Location.none
		    }
    ; pstr_loc = Location.none
    }
  in
  let open_sf =  { pstr_desc =
		     Pstr_open { popen_lid = wrap (Lident sf_instance_name)
			       ; popen_override = Fresh
			       ; popen_loc = Location.none
			       ; popen_attributes = []
			       }
		 ; pstr_loc = Location.none
		 }
  in
  let (tps, cons) = List.partition (function _, Is_kind -> true | _ -> false) ds in
  List.map generate_new_type tps @ [generate_constr_type cons] @ [sf_instance; open_sf]


let rec t1_to_ast = function
  | Lam m ->  [%expr Lam [%e t1_to_ast m]]
  | Tm0 r -> [%expr Tm0 [%e t0_to_ast r ]]
  | AppS (m, s) ->  assert false (* [%expr hsub_nor [%e sub_to_ast s] [%e nor_to_ast m]] *)
  | Meta u ->
     { pexp_desc = Pexp_ident (wrap (Longident.parse u))
     ; pexp_loc = Location.none
     ; pexp_attributes = []
     }

and t0_to_ast = function
  | C (c, sp) ->  [%expr C ([%e constr (con_name c) []], [%e sp_to_ast sp])]
  | Var x -> assert false

and sp_to_ast = function
  | Empty -> [%expr Empty]
  | Cons (m, sp) -> [%expr Cons ([%e t1_to_ast m], [%e sp_to_ast sp])]

and sub_to_ast = function
  | _ -> assert false
  (* | Shift n -> [%expr Shift [%e int n]] *)
  (* | Dot (s, m) -> [%expr Dot ([%e sub_to_ast s], [%e nor_to_ast m])] *)

let rec t1_to_pat_ast = function
  | Lam m ->  [%pat? Lam [%p t1_to_pat_ast m]]
  | Tm0 r -> [%pat? Tm0 [%p t0_to_pat_ast r ]]
  | AppS _ -> raise (AST_gen_error "No explicit substitutions in patterns")
  | Meta u ->
     { ppat_desc = Ppat_var {txt = u ; loc = Location.none }
     ; ppat_loc = Location.none
     ; ppat_attributes = []
     }

and t0_to_pat_ast = function
  | C (c, sp) ->  [%pat? C ([%p pconstr (con_name c) []], [%p sp_to_pat_ast sp])]
  | Var x -> assert false

(* and hd_to_pat_ast = function *)
(*   | _ -> assert false *)
  (* | Const c -> [%pat? Const [%p pstr c]] *)
  (* | Var x -> [%pat? Var [%p pint x]] *)

and sp_to_pat_ast = function
  | Empty -> [%pat? Empty]
  | Cons (m, sp) -> [%pat? Cons ([%p t1_to_pat_ast m], [%p sp_to_pat_ast sp])]

(* and sub_to_pat_ast = function *)
(*   | _ -> assert false *)
  (* | Shift n -> [%pat? Shift [%p pint n]] *)
  (* | Dot (s, m) -> [%pat? Dot ([%p sub_to_pat_ast s], [%p nor_to_pat_ast m])] *)

let rec typ_ann_to_ast =
  let foo s = build_base_typ s in
  function
  | Syntax.BVars (vs, t) -> assert false
  | Syntax.Arr (t1, t2) -> [%type: [%t typ_ann_to_ast t1] -> [%t typ_ann_to_ast t2]]
  | Syntax.TAny -> [%type: _]
  | Syntax.CType s -> [%type: ('a, [%t foo (typ_name s)]) tm1]
