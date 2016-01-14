%{
    open Syntax
%}

%token ARR
%token FN
%token DOT
%token COLON
%token COMMA
%token SEMICOLON
%token TYPE
%token VDASH

%token <string> ID
%token <string> MVAR
(* %token <int> NUM *)
%token LPAREN
%token RPAREN
%token LSQ
%token RSQ
%token LBOX
%token RBOX
(* %token BAR *)
%token EOF

%right ARR

%start <Usf.signature>  decls
%start <Syntax.ctx_term> ctx_term_expr
%start <Syntax.term> term_expr
%start <Syntax.typ_ann> typ_ann

%%

tp :
| c = ID { Usf.TConst c }
| s = tp ARR t = tp { Usf.Arr (s, t) }
| LPAREN t = tp RPAREN { t }

kot :
| TYPE { Usf.Is_kind }
| t = tp { Usf.Is_type t}

decl :
| c = ID COLON kt = kot {(c , kt)}

decls :
| EOF { [] }
| d = decl DOT ds = decls { d :: ds}

ctx:
| DOT  { Empty } (* empty context *)
| g = ID { CtxVar g } (* context variable (in patterns only) *)
| v = ID COLON vv = ID  { Cons (Empty, v, Usf.TConst vv) } (* unary context *)
| g = ctx COMMA v = ID COLON t = tp { Cons (g, v, t) }

term_expr:
| m = term EOF { m}

term:
| m = simple_term+ { match m with |[m] -> m | m::ms -> App (m, ms) |_ -> assert false }
| FN x = ID DOT m = term { Lam (x, m) }
| m = term LSQ s = sub RSQ { AppS (m, s) }

simple_term:
| LPAREN m = term RPAREN { m }
| v = ID { Var v }
| v = MVAR { MVar v }

sub:
| s = subs { List.rev s }
(* | ID { [] } *)
(* | s = separated_nonempty_list(COMMA, term) { List.rev s } *)


subs:
| t = term SEMICOLON s = subs { t :: s }
| t = term { [t] }

ctx_term_expr:
| ct = ctx_term EOF {ct}

ctx_term :
| g = ctx VDASH m = term { g , m }
| VDASH m = term { Empty , m }
| m = term { Empty , m }


typ_ann_no_eof:
| vs = ID* { if List.length vs > 1 then TAny None else TAny (Some (List.hd vs))}
| LBOX g = ctx VDASH t = ID RBOX { CType (g, t) }
| LBOX t = ID RBOX { CType (Empty, t) }
| t1 = typ_ann_no_eof ARR t2 = typ_ann_no_eof { Arr (t1, t2) }

typ_ann_quant:
| vars = ID+ DOT t = typ_ann_no_eof { (vars, t) }
| t = typ_ann_no_eof { ([], t) }

typ_ann:
| t = typ_ann_quant EOF { t}
