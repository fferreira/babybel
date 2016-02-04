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
%token SHIFT
%token APOSTROPHE
%token SHARP
%token STAR

%token <string> ID
%token <int> NUM
%token LPAREN
%token RPAREN
%token LSQ
%token RSQ
(* %token LBOX *)
(* %token RBOX *)
%token EOF

%right ARR

%start <Usf.signature>  decls
%start <Syntax.ctx_term> ctx_term_expr
%start <Syntax.term> term_expr
%start <Syntax.typ_ann_body> typ_ann

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

ctx_no_annot:
| STAR { Rest }
| g = ctx_no_annot COMMA v = ID { TCons (g, v) }
| v = ID  { TCons (Rest, v) } (* unary context *)

term_expr:
| m = term EOF { m}

term:
| m = simple_term+ { match m with |[m] -> m | m::ms -> App (m, ms) |_ -> assert false }
| FN x = ID DOT m = term { Lam (x, m) }
| m = term LSQ s = sub RSQ { AppS (m, s) }

simple_term:
| LPAREN m = term RPAREN { m }
| v = ID { Var v }
| APOSTROPHE v = ID { MVar v }
| sh = SHARP+ v = ID { PVar (v, List.length sh) }

shift:
| SHIFT n = NUM SEMICOLON { n }

sub:
| n = shift? s = separated_list(SEMICOLON, term) { (match n with None -> 0 | Some n -> n), List.rev s }


(* | s = subs { assert false } *)
(* | ID { [] } *)
(* | s = separated_nonempty_list(COMMA, term) { List.rev s } *)


(* subs: *)
(* | t = term SEMICOLON s = subs { Dot (t, s) } *)
(* | t = term { Dot (t, Shift 0) } *)
(* | SHIFT n=NUM { Shift n } *)

ctx_term_expr:
| ct = ctx_term EOF {ct}

ctx_term :
| g = ctx_no_annot VDASH m = term { g , m }
| VDASH m = term { Rest , m }
| m = term { Rest , m }


typ_ann_no_eof:
| LSQ g = ctx VDASH t = ID RSQ { CType (g, t) }
| LSQ t = ID RSQ { CType (Empty, t) }

typ_ann:
| t = typ_ann_no_eof EOF { t}
