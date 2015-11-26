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
%token LPAREN
%token RPAREN
%token EOF

%right ARR

%start <Sf.signature>  decls
(* %start <Syntax.ctx_term> ctx_term *)
%start <Syntax.term> term_expr

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
| m = simple_term+ { match m with |[m] -> m | m::ms -> App (m, ms)}
| FN x = ID DOT m = term { Lam (x, m) }

simple_term:
| LPAREN m = term RPAREN { m }
| v = ID { Var v }
| v = MVAR { MVar v }

(* | ms = simple_term* { Var ("l:"^string_of_int (List.length ms)) } (\* { App (List.hd ms, List.tl ms) } *\) *)
(* | t = simple_term { t } *)
(* | m = raw_term { m } *)

(* raw_term: *)

(* | LPAREN m = term RPAREN { m } *)

(* simple_term: *)
(* | LPAREN m = term RPAREN { m } *)




(* ctx_term : *)
(* | g = ctx VDASH m = term { g , m } *)
