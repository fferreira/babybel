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
%token EQ
%token UNDERSCORE
%token BAR

%token <string> ID (* starts with lower case *)
%token <string> CID (* starts with upper case *)
%token <string> C_TYPE_ANN (* the type annotation of a constructor *)
%token <int> NUM
%token LPAREN
%token RPAREN
%token LSQ
%token RSQ
%token LCURLY
%token RCURLY
(* %token LBOX *)
(* %token RBOX *)
%token EOF

%right ARR

%start <Usf.signature>  decls
%start <Syntax.ctx_term> ctx_term_expr
%start <Syntax.term> term_expr
%start <Syntax.ctx_tp * Syntax.var> ctx_typ
%start <unit> gadt_type

%%

tp :
| c = ID { Usf.TConst c }
| s = tp ARR t = tp { Usf.Arr (s, t) }
| LPAREN t = tp RPAREN { t }
| LCURLY t = tp RCURLY { Usf.TBox t }

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
| LCURLY m = term RCURLY { Box m }

shift:
| SHIFT n = NUM SEMICOLON { ShiftBy n }
| UNDERSCORE SEMICOLON? { SomeShift }

sub:
| sh = shift? s = separated_list(SEMICOLON, term) { (match sh with None -> ShiftBy 0 | Some sh -> sh), List.rev s }


ctx_term_expr:
| ct = ctx_term EOF {ct}

ctx_term :
| g = ctx_no_annot VDASH m = term { g , m }
| VDASH m = term { Rest , m }
| m = term { Rest , m }

ctx_typ_no_eof:
| LSQ g = ctx VDASH t = ID RSQ { (g, t) }
| LSQ t = ID RSQ { Empty, t }

ctx_typ:
| ct = ctx_typ_no_eof EOF { ct }

(* Parsing gadt with contextual objects *)

gadt_index:
| LPAREN l = separated_list (COMMA, UNDERSCORE) RPAREN { List.length l }
| UNDERSCORE { 1 }

type_header:
| idx = gadt_index n = ID EQ { n }

gadt_constructor :
| BAR n = CID ta = C_TYPE_ANN { () }

gadt_constructors :
| cs = gadt_constructor* { cs }

gadt_type_no_eof:
| hdr = type_header cs = gadt_constructors { () }

gadt_type:
| t = gadt_type_no_eof EOF { t }
