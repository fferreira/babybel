open Usf
open Sf
open Parsetree
open Asttypes
open Ast_convenience
open Longident

exception AST_gen_error of string

let rec tp_to_ast = function
  | TConst c -> [%expr TConst [%e str c]]
  | Arr (s, t) -> [%expr Arr([%e tp_to_ast s], [%e tp_to_ast t])]

let decl_to_ast = function
  | c, Is_kind -> [%expr [%e str c], Is_kind]
  | c, Is_type t -> let ta = tp_to_ast t in [%expr [%e str c], Is_type [%e ta]]

let decls_to_ast ds =
  (* generate an ocaml type for each kind in the signature *)
  let generate_new_type = function
    | (n, Is_kind) ->
       (* constructors *)
       let cons = { pcd_name = {txt = "T" ^ n ; loc = Location.none}
		  ; pcd_args = []
		  ; pcd_res = None
		  ; pcd_loc = Location.none
		  ; pcd_attributes = []
		  }
       in
       (* type *)
       { pstr_desc = Pstr_type ([{ ptype_name = {txt = "tp_" ^ n ; loc = Location.none}
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
       { pstr_desc = Pstr_type ([{ ptype_name = {txt = "signature" ; loc = Location.none}
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
	| TConst n -> { ptyp_desc = Ptyp_constr({txt = Lident ("tp_" ^ n) ; loc = Location.none}, [])
		      ; ptyp_loc = Location.none
		      ; ptyp_attributes = []
		      }
	| Arr (t1, t2) -> [%type: [%t generate_core_type t1] -> [%t generate_core_type t2]]
      in
      let rec constructor_params = function
	| TConst _ -> []
	| Arr (t1, t2) -> generate_core_type t1 :: constructor_params t2
      in
      let rec get_constructed_type = function
	| TConst t -> "tp_" ^ t
	| Arr (_, t) -> get_constructed_type t
      in
      function (name, Is_type t) ->
	       let build_ret_typ s =
		 { ptyp_desc = Ptyp_constr ({txt = Lident "signature" ; loc = Location.none},
					    [{ ptyp_desc =
						 Ptyp_constr ({txt = Lident "base" ; loc = Location.none},
							      [{ ptyp_desc = Ptyp_constr ({ txt = Lident s
											  ; loc = Location.none
											  }, [])
							       ; ptyp_loc = Location.none
							       ; ptyp_attributes = []
							       }])
					     ; ptyp_loc = Location.none
					     ; ptyp_attributes = []
					     }])
		 ; ptyp_loc = Location.none
		 ; ptyp_attributes = []
		 }
	       in
	       { pcd_name = {txt = "CON_" ^ name ; loc = Location.none}
	       ; pcd_args = constructor_params t (* MMMM this is wrong, it should all be in pcd_res and arrs instead of -> (pirate function types) *)
	       ; pcd_res = Some (build_ret_typ (get_constructed_type t)) (* MMM see previous line's comment *)
	       ; pcd_loc = Location.none
	       ; pcd_attributes = []
	       }
	     | _ -> raise (AST_gen_error "Violation: generate_constructor")
    in
    signature (List.map generate_constructor cons)
  in
  let (tps, cons) = List.partition (function _, Is_kind -> true | _ -> false) ds in
  List.map generate_new_type tps @ [generate_constr_type cons]


let rec nor_to_ast = function
  | _ -> assert false
  (* | Lam m ->  [%expr Lam [%e nor_to_ast m]] *)
  (* | Neu r -> [%expr Neu [%e neu_to_ast r ]] *)
  (* | AppS (m, s) -> [%expr hsub_nor [%e sub_to_ast s] [%e nor_to_ast m]] *)
  (* | Meta (u, s) -> *)
  (*    { pexp_desc = Pexp_ident { txt = Longident.parse u *)
  (* 			      ; loc = Location.none *)
  (* 			      } *)
  (*    ; pexp_loc = Location.none *)
  (*    ; pexp_attributes = [] *)
  (*    } *)

and neu_to_ast = function
  | _ -> assert false
  (* | App (h, sp) -> [%expr App ([%e hd_to_ast h], [%e sp_to_ast sp])] *)

and hd_to_ast = function
  | _ -> assert false
  (* | Const c -> [%expr Const [%e str c]] *)
  (* | Var x -> [%expr Var [%e int x]] *)

and sp_to_ast = function
  | _ -> assert false
  (* | Empty -> [%expr Empty] *)
  (* | Cons (m, sp) -> [%expr Cons ([%e nor_to_ast m], [%e sp_to_ast sp])] *)

and sub_to_ast = function
  | _ -> assert false
  (* | Shift n -> [%expr Shift [%e int n]] *)
  (* | Dot (s, m) -> [%expr Dot ([%e sub_to_ast s], [%e nor_to_ast m])] *)

let rec nor_to_pat_ast = function
  | _ -> assert false
  (* | Lam m ->  [%pat? Lam [%p nor_to_pat_ast m]] *)
  (* | Meta (u, s) -> *)
  (*    { ppat_desc = Ppat_var {txt = u ; loc = Location.none } *)
  (*    ; ppat_loc = Location.none *)
  (*    ; ppat_attributes = [] *)
  (*    } *)
  (* | AppS _ -> raise (AST_gen_error "No explicit substitutions in patterns") *)
  (* | Neu r -> [%pat? Neu [%p neu_to_pat_ast r ]] *)

and neu_to_pat_ast = function
  | _ -> assert false
  (* | App (h, sp) -> [%pat? App ([%p hd_to_pat_ast h], [%p sp_to_pat_ast sp])] *)

and hd_to_pat_ast = function
  | _ -> assert false
  (* | Const c -> [%pat? Const [%p pstr c]] *)
  (* | Var x -> [%pat? Var [%p pint x]] *)

and sp_to_pat_ast = function
  | _ -> assert false
  (* | Empty -> [%pat? Empty] *)
  (* | Cons (m, sp) -> [%pat? Cons ([%p nor_to_pat_ast m], [%p sp_to_pat_ast sp])] *)

and sub_to_pat_ast = function
  | _ -> assert false
  (* | Shift n -> [%pat? Shift [%p pint n]] *)
  (* | Dot (s, m) -> [%pat? Dot ([%p sub_to_pat_ast s], [%p nor_to_pat_ast m])] *)

let rec typ_ann_to_ast = function
  | _ -> assert false
  (* | Syntax.BVars (vs, t) -> assert false *)
  (* | Syntax.Arr (t1, t2) -> [%type: [%t typ_ann_to_ast t1] -> [%t typ_ann_to_ast t2]] *)
  (* | Syntax.TAny -> [%type: _] *)
  (* | Syntax.CType _ -> [%type: Sf.nor] *)
