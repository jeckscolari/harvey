type token =
  | FALSE
  | TRUE
  | LPA
  | RPA
  | LSB
  | RSB
  | COM
  | SC
  | DOT
  | QM
  | LD
  | LESSEQ
  | EQ
  | LESS
  | GTR
  | GTREQ
  | STAR
  | LARROW
  | PLUS
  | MINUS
  | SLASH
  | MOD
  | F2I
  | I2F
  | STR of (string)
  | STR_CST of (string)
  | INT of (float)
  | RAT of (float)
  | TU of (int*char)
  | NOT
  | AND
  | OR
  | IMPL
  | EQUIV
  | EX
  | FA
  | PREV
  | NEXT
  | EVENTUALLY
  | ONCE
  | ALWAYS
  | PAST_ALWAYS
  | SINCE
  | UNTIL
  | CNT
  | MIN
  | MAX
  | SUM
  | AVG
  | MED
  | END
  | EOF

open Parsing;;
let _ = parse_error;;
# 43 "formula_parser.mly"
  open Predicate
  open MFOTL
  open Misc

  let f str = 
    if Misc.debugging Dbg_formula then
      Printf.printf "[Formula_parser] %s\t\n" str
    else
      ()

  let var_cnt = ref 0

  (* by default, the time unit is of 1 second *)
  let timeunits (n,c) = 
    let d = 
      match c with
	| 'd' -> 24 * 60 * 60
	| 'h' -> 60 * 60
	| 'm' -> 60
	| 's' -> 1
	| _ -> failwith "[Formula_parser.time_units] unrecognized time unit"
    in  
    float_of_int (d * n)

  let rec exists varlist f =
    match varlist with
      | [] -> failwith "[Formula_parser.exists] no variables"
      | vl -> Exists (vl, f)

  let rec forall varlist f =
    match varlist with
      | [] -> failwith "[Formula_parser.forall] no variables"
      | vl -> ForAll (vl, f)


  let dfintv = (MFOTL.CBnd 0., MFOTL.Inf) 

  let strip str = 
    let len = String.length str in
    if str.[0] = '\"' && str.[len-1] = '\"' then
      String.sub str 1 (len-2)
    else
      str

  let get_cst str = 
    try 
      Int (int_of_string str)
    with _ -> Str (strip str)

  let check f = 
    let _ = 
      match f with
	| Equal (t1,t2)  
	| Less (t1,t2) 
	| LessEq (t1,t2) 
	  -> ( 	
	    match t1,t2 with
	      | Cst (Int _), Cst (Str _) 
	      | Cst (Str _), Cst (Int _) -> 
		failwith "[Formula_parser.check] \
              Comparisons should be between constants of the same type"
	      | _ -> () 
	  )      
	| _ -> failwith "[Formula_parser.check] internal error"
    in f

  let add_ex p = 
    let args = Predicate.get_args p in
    let rec proc = function
      | [] -> []
      | (Var v) :: rest when v.[0] = '_' -> v :: (proc rest) 
      | _ :: rest -> proc rest
    in
    let vl = proc args in
    let pred = Pred p in
    if vl <> [] then Exists (vl, pred) else pred

  let strip s = 
    let len = String.length s in
    assert(s.[0] = '\"' && s.[len-1] = '\"');
    String.sub s 1 (len-2)

     
  (* The rule is: var LARROW aggreg var SC varlist formula  *)
  let aggreg res_var op agg_var groupby_vars f = 
    let free_vars = MFOTL.free_vars f in
    let msg b x = 
      let kind = if b then "Aggregation" else "Group-by" in
      Printf.sprintf "[Formula_parser.aggreg] %s variable %s is not a free variable in the aggregated formula" kind x
    in	
    if not (List.mem agg_var free_vars) then
      failwith (msg true agg_var)
    else
      begin
	List.iter (fun gby_var ->
	  if not (List.mem gby_var free_vars) then
	    failwith (msg false gby_var)	      
	) groupby_vars;
	Aggreg (res_var, op, agg_var, groupby_vars, f)
      end

# 160 "formula_parser.ml"
let yytransl_const = [|
  257 (* FALSE *);
  258 (* TRUE *);
  259 (* LPA *);
  260 (* RPA *);
  261 (* LSB *);
  262 (* RSB *);
  263 (* COM *);
  264 (* SC *);
  265 (* DOT *);
  266 (* QM *);
  267 (* LD *);
  268 (* LESSEQ *);
  269 (* EQ *);
  270 (* LESS *);
  271 (* GTR *);
  272 (* GTREQ *);
  273 (* STAR *);
  274 (* LARROW *);
  275 (* PLUS *);
  276 (* MINUS *);
  277 (* SLASH *);
  278 (* MOD *);
  279 (* F2I *);
  280 (* I2F *);
  286 (* NOT *);
  287 (* AND *);
  288 (* OR *);
  289 (* IMPL *);
  290 (* EQUIV *);
  291 (* EX *);
  292 (* FA *);
  293 (* PREV *);
  294 (* NEXT *);
  295 (* EVENTUALLY *);
  296 (* ONCE *);
  297 (* ALWAYS *);
  298 (* PAST_ALWAYS *);
  299 (* SINCE *);
  300 (* UNTIL *);
  301 (* CNT *);
  302 (* MIN *);
  303 (* MAX *);
  304 (* SUM *);
  305 (* AVG *);
  306 (* MED *);
  307 (* END *);
    0 (* EOF *);
    0|]

let yytransl_block = [|
  281 (* STR *);
  282 (* STR_CST *);
  283 (* INT *);
  284 (* RAT *);
  285 (* TU *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\006\000\006\000\006\000\006\000\006\000\006\000\007\000\
\008\000\008\000\009\000\009\000\009\000\009\000\010\000\010\000\
\002\000\011\000\003\000\003\000\003\000\003\000\003\000\003\000\
\003\000\003\000\003\000\003\000\003\000\013\000\013\000\013\000\
\012\000\012\000\012\000\004\000\004\000\004\000\005\000\005\000\
\000\000"

let yylen = "\002\000\
\003\000\001\000\001\000\001\000\003\000\003\000\003\000\003\000\
\003\000\003\000\003\000\003\000\003\000\002\000\004\000\004\000\
\005\000\007\000\003\000\002\000\003\000\002\000\003\000\002\000\
\003\000\002\000\003\000\003\000\002\000\004\000\003\000\004\000\
\003\000\001\000\001\000\001\000\001\000\001\000\001\000\003\000\
\002\000\002\000\002\000\002\000\002\000\002\000\001\000\001\000\
\004\000\001\000\003\000\003\000\003\000\003\000\003\000\002\000\
\003\000\004\000\004\000\001\000\001\000\001\000\001\000\001\000\
\003\000\001\000\000\000\003\000\001\000\000\000\001\000\001\000\
\002\000"

let yydefred = "\000\000\
\000\000\000\000\002\000\003\000\000\000\071\000\000\000\000\000\
\000\000\000\000\064\000\062\000\063\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\004\000\
\000\000\000\000\000\000\060\000\000\000\000\000\000\000\072\000\
\000\000\061\000\000\000\000\000\014\000\000\000\069\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\001\000\057\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\047\000\041\000\048\000\042\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\013\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\034\000\
\035\000\036\000\037\000\038\000\039\000\000\000\000\000\000\000\
\058\000\059\000\068\000\000\000\000\000\000\000\040\000\000\000\
\000\000\000\000\000\000\000\000\049\000\045\000\046\000\043\000\
\044\000\000\000\000\000\065\000\000\000\000\000"

let yydgoto = "\002\000\
\029\000\024\000\025\000\038\000\026\000\118\000\044\000\045\000\
\127\000\084\000\027\000\120\000\028\000"

let yysindex = "\022\000\
\142\001\000\000\000\000\000\000\142\001\000\000\013\255\028\255\
\032\255\000\000\000\000\000\000\000\000\142\001\019\255\019\255\
\207\255\207\255\207\255\207\255\073\255\207\255\030\255\000\000\
\009\001\010\255\040\255\000\000\062\255\237\001\013\255\000\000\
\069\255\000\000\013\255\013\255\000\000\090\255\000\000\094\255\
\016\001\097\255\079\255\142\001\042\255\079\255\142\001\079\255\
\142\001\079\255\142\001\097\255\142\001\079\255\142\001\142\001\
\142\001\142\001\142\001\207\255\207\255\013\255\013\255\013\255\
\013\255\013\255\013\255\013\255\013\255\013\255\013\255\234\255\
\013\255\000\000\000\000\000\255\098\255\121\255\019\255\142\001\
\142\001\000\000\000\000\000\000\000\000\000\000\079\255\254\254\
\079\255\079\255\079\255\079\255\079\255\000\000\023\255\025\255\
\025\255\030\255\142\001\030\255\142\001\176\255\176\255\176\255\
\176\255\176\255\069\255\048\255\048\255\176\255\176\255\000\000\
\000\000\000\000\000\000\000\000\000\000\019\255\200\255\056\255\
\000\000\000\000\000\000\079\255\079\255\117\255\000\000\126\255\
\030\255\030\255\058\001\013\255\000\000\000\000\000\000\000\000\
\000\000\019\255\030\255\000\000\100\001\030\255"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\159\255\000\000\000\000\000\000\000\000\137\255\137\255\
\000\000\000\000\000\000\000\000\000\000\000\000\068\000\000\000\
\000\000\251\001\000\000\000\000\000\000\000\000\000\000\000\000\
\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\032\000\000\000\000\000\080\000\000\000\092\000\
\000\000\145\000\000\000\000\000\000\000\149\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\067\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\223\001\000\000\000\000\000\000\000\000\170\000\000\000\
\182\000\199\000\201\000\203\000\206\000\000\000\168\000\018\000\
\051\000\002\000\000\000\003\000\000\000\026\000\059\000\133\000\
\151\000\165\000\034\000\067\000\100\000\114\000\147\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\078\255\000\000\
\000\000\000\000\000\000\211\000\213\000\000\000\000\000\000\000\
\005\000\006\000\000\000\067\255\000\000\000\000\000\000\000\000\
\000\000\184\001\007\000\000\000\000\000\008\000"

let yygindex = "\000\000\
\028\000\000\000\199\001\240\255\121\000\000\000\248\255\000\000\
\000\000\223\255\000\000\222\255\000\000"

let yytablesize = 785
let yytable = "\040\000\
\056\000\031\000\033\000\075\000\030\000\032\000\017\000\018\000\
\086\000\047\000\049\000\051\000\053\000\055\000\126\000\031\000\
\067\000\011\000\068\000\069\000\070\000\071\000\001\000\006\000\
\085\000\006\000\083\000\072\000\023\000\006\000\035\000\020\000\
\007\000\053\000\036\000\008\000\009\000\032\000\011\000\012\000\
\013\000\037\000\073\000\032\000\043\000\046\000\048\000\050\000\
\088\000\054\000\010\000\099\000\101\000\056\000\128\000\056\000\
\057\000\058\000\005\000\133\000\056\000\057\000\058\000\059\000\
\067\000\074\000\051\000\073\000\070\000\071\000\067\000\087\000\
\060\000\061\000\089\000\052\000\090\000\042\000\091\000\022\000\
\092\000\066\000\093\000\094\000\095\000\096\000\097\000\098\000\
\100\000\070\000\071\000\024\000\056\000\057\000\058\000\059\000\
\079\000\140\000\080\000\052\000\079\000\121\000\081\000\000\000\
\060\000\061\000\000\000\124\000\125\000\056\000\057\000\058\000\
\059\000\054\000\067\000\000\000\068\000\069\000\070\000\071\000\
\134\000\141\000\135\000\085\000\122\000\083\000\129\000\034\000\
\130\000\136\000\000\000\137\000\007\000\000\000\000\000\039\000\
\039\000\067\000\000\000\068\000\069\000\070\000\071\000\070\000\
\026\000\070\000\055\000\000\000\029\000\000\000\008\000\034\000\
\000\000\000\000\000\000\034\000\034\000\000\000\139\000\000\000\
\000\000\050\000\072\000\000\000\009\000\000\000\000\000\012\000\
\142\000\019\000\072\000\072\000\072\000\072\000\072\000\072\000\
\072\000\072\000\072\000\072\000\072\000\021\000\034\000\034\000\
\034\000\034\000\034\000\034\000\034\000\034\000\034\000\034\000\
\067\000\034\000\068\000\069\000\070\000\071\000\023\000\123\000\
\025\000\000\000\027\000\000\000\000\000\028\000\132\000\003\000\
\004\000\041\000\015\000\042\000\016\000\000\000\000\000\000\000\
\067\000\006\000\068\000\069\000\070\000\071\000\000\000\000\000\
\000\000\000\000\007\000\000\000\000\000\008\000\009\000\010\000\
\011\000\012\000\013\000\000\000\014\000\000\000\131\000\000\000\
\000\000\015\000\016\000\017\000\018\000\019\000\020\000\021\000\
\022\000\000\000\000\000\000\000\034\000\000\000\000\000\000\000\
\000\000\000\000\039\000\000\000\056\000\031\000\033\000\056\000\
\030\000\032\000\017\000\018\000\056\000\056\000\056\000\056\000\
\056\000\056\000\000\000\056\000\056\000\011\000\112\000\113\000\
\114\000\115\000\116\000\117\000\000\000\006\000\000\000\056\000\
\056\000\056\000\056\000\020\000\000\000\053\000\000\000\000\000\
\053\000\000\000\000\000\056\000\056\000\053\000\053\000\053\000\
\053\000\053\000\053\000\011\000\053\000\053\000\010\000\000\000\
\006\000\006\000\006\000\006\000\011\000\011\000\005\000\000\000\
\053\000\053\000\053\000\053\000\006\000\006\000\051\000\000\000\
\000\000\051\000\020\000\020\000\053\000\053\000\051\000\051\000\
\051\000\051\000\051\000\022\000\010\000\051\000\051\000\000\000\
\000\000\005\000\005\000\005\000\005\000\010\000\010\000\024\000\
\000\000\051\000\051\000\051\000\051\000\005\000\005\000\052\000\
\000\000\000\000\052\000\000\000\000\000\051\000\051\000\052\000\
\052\000\052\000\052\000\052\000\000\000\054\000\052\000\052\000\
\054\000\000\000\022\000\022\000\000\000\054\000\054\000\054\000\
\054\000\054\000\052\000\052\000\052\000\052\000\024\000\024\000\
\007\000\000\000\000\000\000\000\000\000\000\000\052\000\052\000\
\054\000\054\000\054\000\054\000\026\000\000\000\055\000\000\000\
\029\000\055\000\008\000\000\000\054\000\054\000\055\000\055\000\
\055\000\055\000\055\000\007\000\007\000\007\000\007\000\000\000\
\009\000\000\000\000\000\012\000\000\000\019\000\000\000\007\000\
\007\000\055\000\055\000\055\000\055\000\008\000\008\000\008\000\
\008\000\021\000\000\000\026\000\026\000\055\000\055\000\029\000\
\029\000\008\000\008\000\009\000\009\000\009\000\009\000\012\000\
\012\000\012\000\023\000\030\000\025\000\033\000\027\000\009\000\
\009\000\028\000\012\000\012\000\019\000\019\000\015\000\000\000\
\016\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\021\000\021\000\000\000\000\000\000\000\076\000\000\000\000\000\
\000\000\077\000\078\000\000\000\000\000\000\000\000\000\030\000\
\000\000\023\000\023\000\025\000\025\000\027\000\027\000\000\000\
\028\000\028\000\000\000\000\000\000\000\015\000\015\000\016\000\
\016\000\000\000\000\000\000\000\102\000\103\000\104\000\105\000\
\106\000\107\000\108\000\109\000\110\000\111\000\000\000\119\000\
\003\000\004\000\005\000\000\000\062\000\063\000\064\000\065\000\
\066\000\067\000\006\000\068\000\069\000\070\000\071\000\000\000\
\000\000\000\000\000\000\007\000\000\000\000\000\008\000\009\000\
\010\000\011\000\082\000\013\000\083\000\014\000\000\000\000\000\
\000\000\000\000\015\000\016\000\017\000\018\000\019\000\020\000\
\021\000\022\000\003\000\004\000\005\000\000\000\000\000\000\000\
\000\000\138\000\000\000\000\000\006\000\000\000\000\000\000\000\
\000\000\000\000\119\000\000\000\000\000\007\000\000\000\000\000\
\008\000\009\000\010\000\011\000\012\000\013\000\000\000\014\000\
\000\000\000\000\000\000\000\000\015\000\016\000\017\000\018\000\
\019\000\020\000\021\000\022\000\003\000\004\000\005\000\000\000\
\000\000\000\000\079\000\000\000\000\000\000\000\006\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\007\000\
\000\000\000\000\008\000\009\000\010\000\011\000\012\000\013\000\
\000\000\014\000\000\000\000\000\000\000\000\000\015\000\016\000\
\017\000\018\000\019\000\020\000\021\000\022\000\003\000\004\000\
\005\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\006\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\007\000\000\000\000\000\008\000\009\000\010\000\011\000\
\012\000\013\000\000\000\014\000\000\000\000\000\000\000\000\000\
\015\000\016\000\017\000\018\000\019\000\020\000\021\000\022\000\
\070\000\070\000\070\000\000\000\000\000\000\000\070\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\070\000\000\000\000\000\070\000\070\000\
\000\000\070\000\070\000\070\000\000\000\070\000\000\000\000\000\
\000\000\000\000\070\000\070\000\070\000\070\000\070\000\070\000\
\070\000\070\000\062\000\000\000\000\000\048\000\000\000\000\000\
\000\000\000\000\062\000\062\000\062\000\062\000\062\000\062\000\
\075\000\062\000\062\000\062\000\062\000\000\000\000\000\000\000\
\062\000\063\000\064\000\065\000\066\000\067\000\061\000\068\000\
\069\000\070\000\071\000\000\000\000\000\000\000\061\000\061\000\
\061\000\061\000\061\000\061\000\000\000\061\000\061\000\061\000\
\061\000"

let yycheck = "\016\000\
\000\000\000\000\000\000\004\001\000\000\000\000\000\000\000\000\
\042\000\018\000\019\000\020\000\021\000\022\000\017\001\003\001\
\017\001\000\000\019\001\020\001\021\001\022\001\001\000\011\001\
\027\001\000\000\029\001\018\001\001\000\011\001\003\001\000\000\
\020\001\000\000\003\001\023\001\024\001\025\001\026\001\027\001\
\028\001\014\000\003\001\025\001\017\000\018\000\019\000\020\000\
\007\001\022\000\000\000\060\000\061\000\031\001\088\000\031\001\
\032\001\033\001\000\000\004\001\031\001\032\001\033\001\034\001\
\017\001\004\001\000\000\000\000\021\001\022\001\004\001\044\000\
\043\001\044\001\047\000\003\001\049\000\005\001\051\000\000\000\
\053\000\004\001\055\000\056\000\057\000\058\000\059\000\060\000\
\061\000\021\001\022\001\000\000\031\001\032\001\033\001\034\001\
\007\001\132\000\009\001\000\000\007\001\004\001\009\001\255\255\
\043\001\044\001\255\255\080\000\081\000\031\001\032\001\033\001\
\034\001\000\000\017\001\255\255\019\001\020\001\021\001\022\001\
\004\001\138\000\006\001\027\001\004\001\029\001\099\000\007\000\
\101\000\004\001\255\255\006\001\000\000\255\255\255\255\015\000\
\016\000\017\001\255\255\019\001\020\001\021\001\022\001\007\001\
\000\000\009\001\000\000\255\255\000\000\255\255\000\000\031\000\
\255\255\255\255\255\255\035\000\036\000\255\255\131\000\255\255\
\255\255\003\001\004\001\255\255\000\000\255\255\255\255\000\000\
\141\000\000\000\012\001\013\001\014\001\015\001\016\001\017\001\
\018\001\019\001\020\001\021\001\022\001\000\000\062\000\063\000\
\064\000\065\000\066\000\067\000\068\000\069\000\070\000\071\000\
\017\001\073\000\019\001\020\001\021\001\022\001\000\000\079\000\
\000\000\255\255\000\000\255\255\255\255\000\000\007\001\001\001\
\002\001\003\001\000\000\005\001\000\000\255\255\255\255\255\255\
\017\001\011\001\019\001\020\001\021\001\022\001\255\255\255\255\
\255\255\255\255\020\001\255\255\255\255\023\001\024\001\025\001\
\026\001\027\001\028\001\255\255\030\001\255\255\118\000\255\255\
\255\255\035\001\036\001\037\001\038\001\039\001\040\001\041\001\
\042\001\255\255\255\255\255\255\132\000\255\255\255\255\255\255\
\255\255\255\255\138\000\255\255\004\001\004\001\004\001\007\001\
\004\001\004\001\004\001\004\001\012\001\013\001\014\001\015\001\
\016\001\017\001\255\255\019\001\020\001\004\001\045\001\046\001\
\047\001\048\001\049\001\050\001\255\255\004\001\255\255\031\001\
\032\001\033\001\034\001\004\001\255\255\004\001\255\255\255\255\
\007\001\255\255\255\255\043\001\044\001\012\001\013\001\014\001\
\015\001\016\001\017\001\034\001\019\001\020\001\004\001\255\255\
\031\001\032\001\033\001\034\001\043\001\044\001\004\001\255\255\
\031\001\032\001\033\001\034\001\043\001\044\001\004\001\255\255\
\255\255\007\001\043\001\044\001\043\001\044\001\012\001\013\001\
\014\001\015\001\016\001\004\001\034\001\019\001\020\001\255\255\
\255\255\031\001\032\001\033\001\034\001\043\001\044\001\004\001\
\255\255\031\001\032\001\033\001\034\001\043\001\044\001\004\001\
\255\255\255\255\007\001\255\255\255\255\043\001\044\001\012\001\
\013\001\014\001\015\001\016\001\255\255\004\001\019\001\020\001\
\007\001\255\255\043\001\044\001\255\255\012\001\013\001\014\001\
\015\001\016\001\031\001\032\001\033\001\034\001\043\001\044\001\
\004\001\255\255\255\255\255\255\255\255\255\255\043\001\044\001\
\031\001\032\001\033\001\034\001\004\001\255\255\004\001\255\255\
\004\001\007\001\004\001\255\255\043\001\044\001\012\001\013\001\
\014\001\015\001\016\001\031\001\032\001\033\001\034\001\255\255\
\004\001\255\255\255\255\004\001\255\255\004\001\255\255\043\001\
\044\001\031\001\032\001\033\001\034\001\031\001\032\001\033\001\
\034\001\004\001\255\255\043\001\044\001\043\001\044\001\043\001\
\044\001\043\001\044\001\031\001\032\001\033\001\034\001\032\001\
\033\001\034\001\004\001\005\000\004\001\007\000\004\001\043\001\
\044\001\004\001\043\001\044\001\043\001\044\001\004\001\255\255\
\004\001\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\043\001\044\001\255\255\255\255\255\255\031\000\255\255\255\255\
\255\255\035\000\036\000\255\255\255\255\255\255\255\255\041\000\
\255\255\043\001\044\001\043\001\044\001\043\001\044\001\255\255\
\043\001\044\001\255\255\255\255\255\255\043\001\044\001\043\001\
\044\001\255\255\255\255\255\255\062\000\063\000\064\000\065\000\
\066\000\067\000\068\000\069\000\070\000\071\000\255\255\073\000\
\001\001\002\001\003\001\255\255\012\001\013\001\014\001\015\001\
\016\001\017\001\011\001\019\001\020\001\021\001\022\001\255\255\
\255\255\255\255\255\255\020\001\255\255\255\255\023\001\024\001\
\025\001\026\001\027\001\028\001\029\001\030\001\255\255\255\255\
\255\255\255\255\035\001\036\001\037\001\038\001\039\001\040\001\
\041\001\042\001\001\001\002\001\003\001\255\255\255\255\255\255\
\255\255\008\001\255\255\255\255\011\001\255\255\255\255\255\255\
\255\255\255\255\132\000\255\255\255\255\020\001\255\255\255\255\
\023\001\024\001\025\001\026\001\027\001\028\001\255\255\030\001\
\255\255\255\255\255\255\255\255\035\001\036\001\037\001\038\001\
\039\001\040\001\041\001\042\001\001\001\002\001\003\001\255\255\
\255\255\255\255\007\001\255\255\255\255\255\255\011\001\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\020\001\
\255\255\255\255\023\001\024\001\025\001\026\001\027\001\028\001\
\255\255\030\001\255\255\255\255\255\255\255\255\035\001\036\001\
\037\001\038\001\039\001\040\001\041\001\042\001\001\001\002\001\
\003\001\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\011\001\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\020\001\255\255\255\255\023\001\024\001\025\001\026\001\
\027\001\028\001\255\255\030\001\255\255\255\255\255\255\255\255\
\035\001\036\001\037\001\038\001\039\001\040\001\041\001\042\001\
\001\001\002\001\003\001\255\255\255\255\255\255\007\001\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\020\001\255\255\255\255\023\001\024\001\
\255\255\026\001\027\001\028\001\255\255\030\001\255\255\255\255\
\255\255\255\255\035\001\036\001\037\001\038\001\039\001\040\001\
\041\001\042\001\004\001\255\255\255\255\007\001\255\255\255\255\
\255\255\255\255\012\001\013\001\014\001\015\001\016\001\017\001\
\004\001\019\001\020\001\021\001\022\001\255\255\255\255\255\255\
\012\001\013\001\014\001\015\001\016\001\017\001\004\001\019\001\
\020\001\021\001\022\001\255\255\255\255\255\255\012\001\013\001\
\014\001\015\001\016\001\017\001\255\255\019\001\020\001\021\001\
\022\001"

let yynames_const = "\
  FALSE\000\
  TRUE\000\
  LPA\000\
  RPA\000\
  LSB\000\
  RSB\000\
  COM\000\
  SC\000\
  DOT\000\
  QM\000\
  LD\000\
  LESSEQ\000\
  EQ\000\
  LESS\000\
  GTR\000\
  GTREQ\000\
  STAR\000\
  LARROW\000\
  PLUS\000\
  MINUS\000\
  SLASH\000\
  MOD\000\
  F2I\000\
  I2F\000\
  NOT\000\
  AND\000\
  OR\000\
  IMPL\000\
  EQUIV\000\
  EX\000\
  FA\000\
  PREV\000\
  NEXT\000\
  EVENTUALLY\000\
  ONCE\000\
  ALWAYS\000\
  PAST_ALWAYS\000\
  SINCE\000\
  UNTIL\000\
  CNT\000\
  MIN\000\
  MAX\000\
  SUM\000\
  AVG\000\
  MED\000\
  END\000\
  EOF\000\
  "

let yynames_block = "\
  STR\000\
  STR_CST\000\
  INT\000\
  RAT\000\
  TU\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : MFOTL.formula) in
    Obj.repr(
# 178 "formula_parser.mly"
                                        ( f "f()"; _2 )
# 579 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    Obj.repr(
# 179 "formula_parser.mly"
                                        ( f "FALSE"; Less (Cst (Int 0), Cst (Int 0)) )
# 585 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    Obj.repr(
# 180 "formula_parser.mly"
                                        ( f "TRUE"; Equal (Cst (Int 0), Cst (Int 0)) )
# 591 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'predicate) in
    Obj.repr(
# 181 "formula_parser.mly"
                                        ( f "f(pred)"; _1 )
# 598 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 182 "formula_parser.mly"
                                        ( f "f(eq)"; check (Equal (_1,_3)) )
# 606 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 183 "formula_parser.mly"
                                        ( f "f(leq)"; check (LessEq (_1,_3)) )
# 614 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 184 "formula_parser.mly"
                                        ( f "f(less)"; check (Less (_1,_3)) )
# 622 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 185 "formula_parser.mly"
                                        ( f "f(gtr)"; check (Less (_3,_1)) )
# 630 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 186 "formula_parser.mly"
                                        ( f "f(geq)"; check (LessEq (_3,_1)) )
# 638 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : MFOTL.formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : MFOTL.formula) in
    Obj.repr(
# 187 "formula_parser.mly"
                                        ( f "f(<=>)"; Equiv (_1,_3) )
# 646 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : MFOTL.formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : MFOTL.formula) in
    Obj.repr(
# 188 "formula_parser.mly"
                                        ( f "f(=>)"; Implies (_1,_3) )
# 654 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : MFOTL.formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : MFOTL.formula) in
    Obj.repr(
# 189 "formula_parser.mly"
                                        ( f "f(or)"; Or (_1,_3) )
# 662 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : MFOTL.formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : MFOTL.formula) in
    Obj.repr(
# 190 "formula_parser.mly"
                                        ( f "f(and)"; And (_1,_3) )
# 670 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : MFOTL.formula) in
    Obj.repr(
# 191 "formula_parser.mly"
                                        ( f "f(not)"; Neg (_2) )
# 677 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'varlist) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : MFOTL.formula) in
    Obj.repr(
# 192 "formula_parser.mly"
                                        ( f "f(ex)"; exists _2 _4 )
# 685 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'varlist) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : MFOTL.formula) in
    Obj.repr(
# 193 "formula_parser.mly"
                                        ( f "f(fa)"; forall _2 _4 )
# 693 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'var) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'aggreg) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'var) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : MFOTL.formula) in
    Obj.repr(
# 194 "formula_parser.mly"
                                        ( f "f(agg1)"; aggreg _1 _3 _4 [] _5 )
# 703 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 6 : 'var) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'aggreg) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : 'var) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'varlist) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : MFOTL.formula) in
    Obj.repr(
# 196 "formula_parser.mly"
                                        ( f "f(agg2)"; aggreg _1 _3 _4 _6 _7 )
# 714 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'interval) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : MFOTL.formula) in
    Obj.repr(
# 197 "formula_parser.mly"
                                        ( f "f(prev)"; Prev (_2,_3) )
# 722 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : MFOTL.formula) in
    Obj.repr(
# 198 "formula_parser.mly"
                                        ( f "f(prevdf)"; Prev (dfintv,_2) )
# 729 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'interval) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : MFOTL.formula) in
    Obj.repr(
# 199 "formula_parser.mly"
                                        ( f "f(next)"; Next (_2,_3) )
# 737 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : MFOTL.formula) in
    Obj.repr(
# 200 "formula_parser.mly"
                                        ( f "f(nextdf)"; Next (dfintv,_2) )
# 744 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'interval) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : MFOTL.formula) in
    Obj.repr(
# 201 "formula_parser.mly"
                                        ( f "f(ev)"; Eventually (_2,_3) )
# 752 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : MFOTL.formula) in
    Obj.repr(
# 202 "formula_parser.mly"
                                        ( f "f(evdf)"; Eventually (dfintv,_2) )
# 759 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'interval) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : MFOTL.formula) in
    Obj.repr(
# 203 "formula_parser.mly"
                                        ( f "f(once)"; Once (_2,_3) )
# 767 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : MFOTL.formula) in
    Obj.repr(
# 204 "formula_parser.mly"
                                        ( f "f(oncedf)"; Once (dfintv,_2) )
# 774 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'interval) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : MFOTL.formula) in
    Obj.repr(
# 205 "formula_parser.mly"
                                        ( f "f(always)"; Always (_2,_3) )
# 782 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'interval) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : MFOTL.formula) in
    Obj.repr(
# 206 "formula_parser.mly"
                                        ( f "f(palways)"; PastAlways (_2,_3) )
# 790 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : MFOTL.formula) in
    Obj.repr(
# 207 "formula_parser.mly"
                                        ( f "f(palwaysdf)"; PastAlways (dfintv,_2) )
# 797 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : MFOTL.formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'interval) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : MFOTL.formula) in
    Obj.repr(
# 208 "formula_parser.mly"
                                        ( f "f(since)"; Since (_3,_1,_4) )
# 806 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : MFOTL.formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : MFOTL.formula) in
    Obj.repr(
# 209 "formula_parser.mly"
                                        ( f "f(sincedf)"; Since (dfintv,_1,_3) )
# 814 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : MFOTL.formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'interval) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : MFOTL.formula) in
    Obj.repr(
# 210 "formula_parser.mly"
                                        ( f "f(until)"; Until (_3,_1,_4) )
# 823 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : MFOTL.formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : MFOTL.formula) in
    Obj.repr(
# 211 "formula_parser.mly"
                                        ( f "f(untildf)"; Until (dfintv,_1,_3) )
# 831 "formula_parser.ml"
               : MFOTL.formula))
; (fun __caml_parser_env ->
    Obj.repr(
# 214 "formula_parser.mly"
                                ( f "agg(cnt)"; Cnt )
# 837 "formula_parser.ml"
               : 'aggreg))
; (fun __caml_parser_env ->
    Obj.repr(
# 215 "formula_parser.mly"
                                ( f "agg(min)"; Min )
# 843 "formula_parser.ml"
               : 'aggreg))
; (fun __caml_parser_env ->
    Obj.repr(
# 216 "formula_parser.mly"
                                ( f "agg(max)"; Max )
# 849 "formula_parser.ml"
               : 'aggreg))
; (fun __caml_parser_env ->
    Obj.repr(
# 217 "formula_parser.mly"
                                ( f "agg(sum)"; Sum )
# 855 "formula_parser.ml"
               : 'aggreg))
; (fun __caml_parser_env ->
    Obj.repr(
# 218 "formula_parser.mly"
                                ( f "agg(avg)"; Avg )
# 861 "formula_parser.ml"
               : 'aggreg))
; (fun __caml_parser_env ->
    Obj.repr(
# 219 "formula_parser.mly"
                                ( f "agg(med)"; Med )
# 867 "formula_parser.ml"
               : 'aggreg))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'lbound) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'rbound) in
    Obj.repr(
# 223 "formula_parser.mly"
                                ( f "interval"; (_1,_3) )
# 875 "formula_parser.ml"
               : 'interval))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'units) in
    Obj.repr(
# 226 "formula_parser.mly"
                                ( f "opened lbound"; OBnd _2 )
# 882 "formula_parser.ml"
               : 'lbound))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'units) in
    Obj.repr(
# 227 "formula_parser.mly"
                                ( f "closed lbound"; CBnd _2 )
# 889 "formula_parser.ml"
               : 'lbound))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'units) in
    Obj.repr(
# 230 "formula_parser.mly"
                                ( f "opened rbound"; OBnd _1 )
# 896 "formula_parser.ml"
               : 'rbound))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'units) in
    Obj.repr(
# 231 "formula_parser.mly"
                                ( f "closed rbound"; CBnd _1 )
# 903 "formula_parser.ml"
               : 'rbound))
; (fun __caml_parser_env ->
    Obj.repr(
# 232 "formula_parser.mly"
                                ( f "no bound(1)"; Inf )
# 909 "formula_parser.ml"
               : 'rbound))
; (fun __caml_parser_env ->
    Obj.repr(
# 233 "formula_parser.mly"
                                ( f "no bound(2)"; Inf )
# 915 "formula_parser.ml"
               : 'rbound))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int*char) in
    Obj.repr(
# 236 "formula_parser.mly"
                                ( f "ts";  timeunits _1 )
# 922 "formula_parser.ml"
               : 'units))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : float) in
    Obj.repr(
# 237 "formula_parser.mly"
                                ( f "int"; _1 )
# 929 "formula_parser.ml"
               : 'units))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'pred) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'termlist) in
    Obj.repr(
# 241 "formula_parser.mly"
                                ( f "p()"; 
				  let p = Predicate.make_predicate (_1,_3) in 
				  add_ex p
				)
# 940 "formula_parser.ml"
               : 'predicate))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 247 "formula_parser.mly"
                                ( f "pred"; _1 )
# 947 "formula_parser.ml"
               : 'pred))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 251 "formula_parser.mly"
                                ( f "term(plus)"; Plus (_1, _3) )
# 955 "formula_parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 252 "formula_parser.mly"
                                ( f "term(minus)"; Minus (_1, _3) )
# 963 "formula_parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 253 "formula_parser.mly"
                                ( f "term(mult)"; Mult (_1, _3) )
# 971 "formula_parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 254 "formula_parser.mly"
                                ( f "term(div)"; Div (_1, _3) )
# 979 "formula_parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 255 "formula_parser.mly"
                                ( f "term(mod)"; Mod (_1, _3) )
# 987 "formula_parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 256 "formula_parser.mly"
                                ( f "term(uminus)"; UMinus _2 )
# 994 "formula_parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 257 "formula_parser.mly"
                                ( f "term(paren)"; _2 )
# 1001 "formula_parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 258 "formula_parser.mly"
                                ( f "term(f2i)"; F2i _3 )
# 1008 "formula_parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 259 "formula_parser.mly"
                                ( f "term(i2f)"; I2f _3 )
# 1015 "formula_parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'cst) in
    Obj.repr(
# 260 "formula_parser.mly"
                                ( f "term(cst)"; Cst _1 )
# 1022 "formula_parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'var) in
    Obj.repr(
# 261 "formula_parser.mly"
                                ( f "term(var)"; Var _1 )
# 1029 "formula_parser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : float) in
    Obj.repr(
# 265 "formula_parser.mly"
                                ( f "cst(int)"; 
				  assert (_1 < float_of_int max_int);
				  assert (_1 > float_of_int min_int);
				  Int (int_of_float _1) )
# 1039 "formula_parser.ml"
               : 'cst))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : float) in
    Obj.repr(
# 269 "formula_parser.mly"
                                ( f "cst(rat)"; Float _1 )
# 1046 "formula_parser.ml"
               : 'cst))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 270 "formula_parser.mly"
                                ( f "cst(str)"; Str (strip _1) )
# 1053 "formula_parser.ml"
               : 'cst))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'termlist) in
    Obj.repr(
# 274 "formula_parser.mly"
                                ( f "termlist(list)"; _1 :: _3 )
# 1061 "formula_parser.ml"
               : 'termlist))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 275 "formula_parser.mly"
                              ( f "termlist(end)"; [_1] )
# 1068 "formula_parser.ml"
               : 'termlist))
; (fun __caml_parser_env ->
    Obj.repr(
# 276 "formula_parser.mly"
                                ( f "termlist()"; [] )
# 1074 "formula_parser.ml"
               : 'termlist))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'varlist) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'var) in
    Obj.repr(
# 279 "formula_parser.mly"
                                ( f "varlist(list)"; _1 @ [_3] )
# 1082 "formula_parser.ml"
               : 'varlist))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'var) in
    Obj.repr(
# 280 "formula_parser.mly"
                             ( f "varlist(end)"; [_1] )
# 1089 "formula_parser.ml"
               : 'varlist))
; (fun __caml_parser_env ->
    Obj.repr(
# 281 "formula_parser.mly"
                          ( f "varlist()"; [] )
# 1095 "formula_parser.ml"
               : 'varlist))
; (fun __caml_parser_env ->
    Obj.repr(
# 284 "formula_parser.mly"
                                ( f "unnamed var"; incr var_cnt; "_" ^ (string_of_int !var_cnt) )
# 1101 "formula_parser.ml"
               : 'var))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 285 "formula_parser.mly"
                            ( f "var"; assert (String.length _1 > 0); _1 )
# 1108 "formula_parser.ml"
               : 'var))
(* Entry formula *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let formula (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : MFOTL.formula)
