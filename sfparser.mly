%{
    open Syntax
%}

%token ARR
%token DOT
%token COLON
%token TYPE
%token VDASH

%token <string> CON
%token <string> VAR
%token LPAREN
%token RPAREN
%token EOF

%right ARR

%start <Syntax.decl list> decls

%%

tp :
| c = CON { TConst c }
| s = tp ARR t = tp { Arr (s, t) }
| LPAREN t = tp RPAREN { t }

kot :
| TYPE { Is_kind }
| t = tp { Is_type t}

decl :
| c = CON COLON kt = kot {(c , kt)}

decls :
| EOF { [] }
| d = decl DOT ds = decls { d :: ds}
