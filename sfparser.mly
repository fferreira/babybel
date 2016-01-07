%{
    open Syntax
%}

%token ARR
%token FN
%token DOT
%token COLON
%token TYPE
%token VDASH

%token <string> ID
%token <string> MVAR
%token <int> NUM
%token LPAREN
%token RPAREN
%token LSQ
%token RSQ
%token LBOX
%token RBOX
%token BAR
%token EOF

%right ARR

%start <Sf.signature>  decls
(* %start <Syntax.ctx_term> ctx_term *)
%start <Syntax.term> term_expr
%start <Syntax.typ_ann> typ_ann

%%

tp :
| c = ID { Sf.
TConst c }
| s = tp ARR t = tp { Sf.Arr (s, t) }
| LPAREN t = tp RPAREN { t }

kot :
| TYPE { Sf.Is_kind }
| t = tp { Sf.Is_type t}

decl :
| c = ID COLON kt = kot {(c , kt)}

decls :
| EOF { [] }
| d = decl DOT ds = decls { d :: ds}

(* ctx: *)
(* | v = ID { [] } *)

term_expr:
| m = term EOF { m}

term:
| m = simple_term+ { match m with |[m] -> m | m::ms -> App (m, ms) |_ -> assert false }
| FN x = ID DOT m = term { Lam (x, m) }
| m = term LSQ n = term BAR v = NUM RSQ { AppS (m, (n, v)) }
| m = term LSQ n = term RSQ { AppS (m, (n, 0)) }

simple_term:
| LPAREN m = term RPAREN { m }
| v = ID { Var v }
| v = MVAR { MVar v }

(* ctx_term : *)
(* | g = ctx VDASH m = term { g , m } *)

typ_ann_no_eof:
| ID* { TAny }
| LBOX t = ID RBOX { CType t }
(* | vars = ID+ DOT t = typ_ann { BVars (vars, t) } *)
| t1 = typ_ann_no_eof ARR t2 = typ_ann_no_eof { Arr (t1, t2) }

(* | ID* { TAny} *)

typ_ann:
| t = typ_ann_no_eof EOF { t}
