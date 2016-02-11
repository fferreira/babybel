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
let signature_to_string_name = "signature_to_string"
let sf_module_name = "SyntacticFramework"
let sf_signature_typ_name = "constructor"
let sf_signature_to_string = "to_string"
let sf_instance_name = "SFU"

(* Generate ASTs *)

(* wraps a value in a loc record *)
let wrap c = { txt = c ; loc = Location.none }

(* utility functions for dealing with ast *)

let expression e =
  { pexp_desc = e
  ; pexp_loc = Location.none
  ; pexp_attributes = []
  }

let core_type t =
  { ptyp_desc = t
  ; ptyp_loc = Location.none
  ; ptyp_attributes = []
  }


let wrap_in_signature t  = core_type (Ptyp_constr ( wrap (Lident signature_typ_name), [t]))

let wrap_type_in_base t =
  core_type (Ptyp_constr ( wrap (Lident "base")
			 , [t]))

(* build a polymorhpich type variable *)
let build_typ_var s =
  core_type (Ptyp_var s)
let build_typ_const s =
  core_type (Ptyp_constr (wrap (Lident s), []))

(* build a base type with a constructor *)
let build_base_typ_constr s f = wrap_type_in_base (f s)

let rec generate_core_type : Usf.tp -> Parsetree.core_type = function
  | TConst n -> build_base_typ_constr (typ_name n) build_typ_const
  | Arr (t1, t2) -> [%type: ([%t generate_core_type t1], [%t generate_core_type t2]) arr]

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
				 ; ptype_params = [core_type Ptyp_any, Invariant]
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
      Pmod_structure (* first the type for constructors *)
        [{pstr_desc =
            Pstr_type
              [{ ptype_name = wrap sf_signature_typ_name
	       ; ptype_params = [(core_type (Ptyp_var "a"), Invariant)]
	       ; ptype_cstrs = []
	       ; ptype_kind = Ptype_abstract
               ; ptype_private = Public
               ; ptype_manifest =
                   Some (core_type (Ptyp_constr ( wrap (Lident signature_typ_name)
						, [core_type (Ptyp_var "a")])))
	       ; ptype_attributes = []
	       ; ptype_loc = Location.none
	       }]
	 ; pstr_loc = Location.none
	 }
	(* and then the type for the to string function *)
	; {pstr_desc = Pstr_value (Nonrecursive,[{ pvb_pat = { ppat_desc = Ppat_var (wrap sf_signature_to_string)
							     ; ppat_loc = Location.none
							     ; ppat_attributes = []
							     }
						 ; pvb_expr = expression (Pexp_ident (wrap (Lident signature_to_string_name)))
						 ; pvb_loc = Location.none
						 ; pvb_attributes = []
						 }])
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
  let open_sf = { pstr_desc =
		    Pstr_open { popen_lid = wrap (Lident sf_instance_name)
			      ; popen_override = Fresh
			      ; popen_loc = Location.none
			      ; popen_attributes = []
			      }
		; pstr_loc = Location.none
		}
  in
  (* Code to register pretty printers, the level, id, Types module
     need to be changed so it works *)
  (* let register_pretty_printers = *)
  (*   { pstr_desc = *)
  (* 	Pstr_value (Nonrecursive, [{ pvb_pat = { ppat_desc = Ppat_any *)
  (* 					       ; ppat_loc = Location.none *)
  (* 					       ; ppat_attributes = [] *)
  (* 					       } *)
  (* 				   ; pvb_expr = *)
  (* 				       [%expr Toploop.install_printer *)
  (* 					      (Path.Pident (Ident.create "SFU")) *)
  (* 					      ({ desc = Types.Tconstr (Path.Pident (Ident.create "tm1"), [], ref Types.Mnil) *)
  (* 					       ; level = 100 (\* higher => more polymorphic *\) *)
  (* 					       ; id = 42 (\* I don't know what is this for, so... *\) *)
  (* 					       }) *)
  (* 					      (Obj.magic pp_tm1)] *)
  (* 				   ; pvb_loc = Location.none *)
  (* 				   ; pvb_attributes = [] *)
  (* 				   }]) *)
  (*   ; pstr_loc = Location.none *)
  (*   } *)
  (* in *)
  (* generates function to_string *)
  let gen_to_string_fn cons =
    (* constrain *)
    let constr e t =
      expression(Pexp_constraint (e, t))
    in
    let typ var_const = core_type (Ptyp_arrow ( ""
					      , core_type (Ptyp_constr ( wrap (Lident signature_typ_name)
								       , [var_const "a"]))
					      , core_type (Ptyp_constr (wrap (Lident "string"), []))))
    in
    let cons_names = List.map fst cons in
    let function_body =
      let gen_branch n =
	{ pc_lhs = { ppat_desc = Ppat_construct (wrap (Lident (con_name n)), None)
		   ; ppat_loc = Location.none
		   ; ppat_attributes = []
		   }
	; pc_guard = None
	; pc_rhs = str n
	}
      in
      let body = Pexp_function (List.map gen_branch cons_names) in
      [%expr fun (type a) -> [%e constr (expression body) (typ build_typ_const)]]

    in
    { pstr_desc =
	Pstr_value (Nonrecursive,
		    [{ pvb_pat = { ppat_desc = Ppat_var (wrap signature_to_string_name)
				 ; ppat_loc = Location.none
				 ; ppat_attributes = []
				 }
		     ; pvb_expr = constr function_body (typ build_typ_var)
		     ; pvb_loc = Location.none
		     ; pvb_attributes = []
		     }])
    ; pstr_loc = Location.none
    }
  in
  let (tps, cons) = List.partition (function _, Is_kind -> true | _ -> false) ds in
  List.map generate_new_type tps @
    [generate_constr_type cons; gen_to_string_fn cons] @
      [sf_instance; open_sf (*; register_pretty_printers*)]

let rec index_to_var = function
  | 0 -> [%expr Top]
  | n -> [%expr Pop [%e index_to_var (n - 1)]]

let rec t1_to_ast = function
  | Lam m ->  [%expr Lam [%e t1_to_ast m]]
  | Tm0 r -> [%expr Tm0 [%e t0_to_ast r ]]
  | AppS (m, s) -> [%expr sub_tm1 [%e sub_to_ast s] [%e t1_to_ast m]]
  | Meta u -> evar u
  | Par (u, 1) -> [%expr Tm0(Var [%e evar u])]
  | Par (_, n) -> raise (AST_gen_error "unimplemented par n")

and t0_to_ast = function
  | C (c, sp) ->  [%expr C ([%e constr (con_name c) []], [%e sp_to_ast sp])]
  | Var x -> [%expr Var [%e index_to_var x]]

and sp_to_ast = function
  | Empty -> [%expr Empty]
  | Cons (m, sp) -> [%expr Cons ([%e t1_to_ast m], [%e sp_to_ast sp])]

and sub_to_ast =
  let rec shift = function
    | 0 -> [%expr Id ]
    | n -> [%expr Suc [%e shift(n-1)]]
  in
  function
  | sh, [] -> [%expr Shift [%e shift sh]]
  | sh, [m] -> [%expr Dot (Shift [%e shift sh], [%e  t1_to_ast m])]
  | sh, m::ms -> [%expr Dot( [%e sub_to_ast (sh, ms)], [%e  t1_to_ast m])]

let rec index_to_var_pat = function
  | 0 -> [%pat? Top]
  | n -> [%pat? Pop [%p index_to_var_pat (n - 1)]]

let rec gen_pvar_pop_pat v = function
  | 0 -> raise (AST_gen_error "Violation, this is not the integer you are looking for (0)")
  | 1 -> v
  | n ->  [%pat? Pop [%p gen_pvar_pop_pat v (n-1)]]

let rec t1_to_pat_ast = function
  | Lam m ->  [%pat? Lam [%p t1_to_pat_ast m]]
  | Tm0 r -> [%pat? Tm0 [%p t0_to_pat_ast r ]]
  | AppS _ -> raise (AST_gen_error "No explicit substitutions in patterns")
  | Meta u -> pvar u
  | Par (u, n) -> [%pat? Tm0(Var [%p gen_pvar_pop_pat (pvar u) n])]

and t0_to_pat_ast = function
  | C (c, sp) ->  [%pat? C ([%p pconstr (con_name c) []], [%p sp_to_pat_ast sp])]
  | Var x -> [%pat? Var [%p (index_to_var_pat x)]]

and sp_to_pat_ast = function
  | Empty -> [%pat? Empty]
  | Cons (m, sp) -> [%pat? Cons ([%p t1_to_pat_ast m], [%p sp_to_pat_ast sp])]

type contructor_flag
	= Constructors
	| Variables

let rec typ_ann_to_ast flag vs =
  let rec ctx_to_typ_ann = function
    | Syntax.Empty -> [%type: nil]
    (* if the context var is bound in vs then it should be a type constructor *)
    | Syntax.CtxVar v when List.mem v vs ->  build_typ_const v
    (* otherwise it is a polymorphic variable *)
    | Syntax.CtxVar v -> build_typ_var v
    | Syntax.Cons (g, x, t) -> [%type: ([%t ctx_to_typ_ann g], [%t generate_core_type t]) cons]
  in
  function
  | Syntax.Arr (t1, t2) -> [%type: [%t typ_ann_to_ast flag vs t1] -> [%t typ_ann_to_ast flag vs t2]]
  | Syntax.CoreType (t, _) when flag = Variables -> t
  | Syntax.CoreType (_, t) -> t
  | Syntax.CType (g, s) -> [%type: ([%t ctx_to_typ_ann g], [%t build_base_typ_constr (typ_name s) build_typ_const]) tm1]
