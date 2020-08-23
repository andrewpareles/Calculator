module Name = String
type name = Name.t

type reIm = float * float (* A + iB *)
type exp = float * float (* (A,B) in A e^iB *)
type num = 
| Exp of exp
| ReIm of reIm
| None

type binop = ADD | SUB | MULT | DIV | EXP 
type unop = NEG | ABS


(* vars are the names of the variables that go into the function *)
module Vars = Set.Make(Name)

type vars_t = Vars.t

type expr = (* just for a single expression, eg f(x)= (x^3 + 1) / 2  *)
| Definition of name*vars_t*expr (* (name, params, expression) eg1: "<A|B>" = expr, eg2: f(x) = x^2*)
| Unop of unop*expr (* eg -1*)
| Binop of binop*expr*expr (*eg: 1 + 2 *)
| Number of num (* eg 5*)
| Const of name (* eg g*)
| Var of name (* eg x in f(x) = x, variable in a function*)



module Env = Map.Make(Name) (* env of env, eg x = 1, f(x) *)
(* env_t is name -> num*)
(* vars is the vars, expr is the expr of the fn (to retain understandability) *)
type env_var = EnvNum of num | EnvFn of vars_t*expr*(env_t -> num) 
and env_t = env_var Env.t


type result = 
| ResultNum of num 
| ResultEnv of env_t

let pi = 3.141592653589793238462643383279502884197169399375105820974944592307

exception Error of string
let failwith str = raise (Error str)

(* ------------------------ CONVERSIONS AND OPERATIONS ------------------------*)
let to_ReIm (n:num) = 
  match n with
  | Exp(a,b) -> ReIm(a*.cos(b), a*.sin(b))
  | ReIm(a,b) -> ReIm(a,b)
  | None -> None

let to_Exp (n:num) = 
  match n with 
  | ReIm(a,b) -> Exp(sqrt(a**2.+.b**2.),atan(b/.a))
  | Exp(a,b) -> Exp(a,b)
  | None -> None

let negate_num (n:num) = 
  match n with 
  | Exp(a,b) -> Exp(a, b+.pi/.2.)
  | ReIm(a,b) -> ReIm(-.a, -.b)
  | None -> None

let abs_num (n:num) = 
  match n with 
  | ReIm(a,b) -> ReIm(sqrt(a**2.+.b**2.), 0.)
  | Exp(a,b) -> ReIm(a, 0.)
  | None -> None

let add_nums (n1:num) (n2:num) : num = 
  match (to_ReIm n1, to_ReIm n2) with 
  | (ReIm(a,b), ReIm(c,d)) -> ReIm(a+.c, b+.d)
  | _ -> failwith "Could not add numbers, since they weren't both ReIm format."

let one_over_num (n:num) = 
  match n with 
  | Exp(a,b) -> Exp(1./.a, -.b)
  | ReIm(a,b) -> ReIm(a/.(a**2.+.b**2.), -.b/.(a**2.+.b**2.))
  | None -> None

let rec mult_nums (n1:num) (n2:num) = 
  match (n1, n2) with 
  | (Exp(a,b), Exp(c,d)) -> Exp(a*.c, b+.d)
  | (ReIm(a,b), ReIm(c,d)) -> ReIm(a*.c-.b*.d, b*.c+.a*.d)
  | (ReIm(a,b), Exp(c,d)) | (Exp(c,d), ReIm(a,b)) -> mult_nums (ReIm(a,b)) (to_ReIm (Exp(c,d)))
  | _ -> failwith "Expected a different type for multiplying numbers."

let rec ln n1 = 
  match n1 with 
  | Exp(a,b) -> ReIm(log a, b)
  | ReIm(a,b) -> ln (to_Exp (ReIm(a,b)))
  | None -> None

let rec exp_nums n1 n2 = 
  match (to_Exp n1, to_ReIm n2) with 
  | (Exp(a,b), ReIm(c,d)) -> Exp(a**c *. (exp 1.)**(-.(b*.d)), b*.c +. d*.(log a))
  | (None, _) | (_, None) -> failwith "Could not exponentiate numbers."
  | (n1, n2) -> exp_nums (to_Exp n1) (to_ReIm n2)

let find_num_in_env name env : num = 
  match Env.find_opt name env with 
  | Some (EnvNum(found)) -> found
  | Some (EnvFn(_)) -> failwith ("Constant" ^ name ^ " was found, but it was a function. Expected a number.")
  | None -> failwith ("No such constant " ^ name ^ " defined.")

let env_has_var env name = 
  match Env.find_opt name env with 
  | Some(_) -> true 
  | None -> false

let env_has_all_vars env vars = 
  Vars.for_all (fun elt -> env_has_var env elt) vars

(**  ------------------------ TOSTRING FUNCTIONS ------------------------ *)
let string_of_num num =
  "("^(
  match num with
  | ReIm(a,b) -> (Float.to_string a) ^ "+" ^ (Float.to_string b) ^ "i"
  | Exp(a,b) -> (Float.to_string a) ^ "e^(" ^ (Float.to_string b) ^ "i)"
  | None -> "None")
  ^")"

let string_of_vars (vars:vars_t) : string = 
  let fold_fn elt s = s ^ " " ^ (String.trim elt)
  in "("^String.trim (Vars.fold fold_fn vars "")^")"

let string_of_binop op n1_str n2_str =
  "("^n1_str^(
    match op with
    | ADD -> "+"
    | SUB -> "-"
    | MULT -> "*"
    | DIV -> "/"
    | EXP -> "^")
  ^n2_str^")"

let string_of_unop op num_str = 
  match op with 
  | NEG -> "-("^num_str^")"
  | ABS -> "|"^num_str^"|"

let rec string_of_expr (e:expr) : string = 
  match e with 
  | Definition(name, vars, e) -> (String.trim name)^(string_of_vars vars)^":="^(string_of_expr e)
  | Unop(op, e) -> string_of_unop op (string_of_expr e)
  | Binop(op, e1, e2) -> string_of_binop op (string_of_expr e1) (string_of_expr e2)
  | Number(num) -> string_of_num num
  | Const(name) -> String.trim name
  | Var(name) -> String.trim name

let string_of_envvar (envvar:env_var) : string = 
  match envvar with
  | EnvNum num -> string_of_num num
  | EnvFn(vars,e,_) -> string_of_vars vars^"->"^string_of_expr e

let string_of_env (env:env_t) : string = 
  let fold_fn = (fun k v acc -> acc^"["^k^"]="^string_of_envvar v^" ") in 
  ("<"^String.trim (Env.fold fold_fn env "")^">")

(* ------------------------ EVALUATION ------------------------ *)

let rec evalExpr (e:expr) (env:env_t) : result = 
  match e with 
  | Definition(name, vars, e) -> ResultEnv(evalDefinition name vars e env)
  | e -> ResultNum (begin
    match e with (* these don't change env *)
    | Unop(op, e1) -> evalUnop op e1 env 
    | Binop(op, e1, e2) -> evalBinop op e1 e2 env 
    | Number(num) -> num
    | Const(name) -> find_num_in_env name env
    | Var(name) when (env_has_var env name) -> find_num_in_env name env
    | Var(name) -> failwith ("Could not find variable " ^ name ^ " in environment " ^ string_of_env env ^ ".")
    | _ -> failwith "Just here to shut up about Definition, which was already matched"
    end)

and evalExprNum e env : num =
  match evalExpr e env with 
  | ResultNum(num) -> num
  | ResultEnv(_) -> failwith ("Could not evaluate expression " ^ string_of_expr e ^ " to a number.")

and evalDefinition (name:name) (vars:vars_t) (e:expr) (env:env_t): env_t = 
  Env.add name (EnvFn(vars, e, fun (env:env_t) -> evalExprNum e env)) env

and evalUnop (op:unop) (e1:expr) (env:env_t) : num = 
  let num = (evalExprNum e1 env) in 
  match op with
  | NEG -> negate_num num
  | ABS -> abs_num num 
    
and evalBinop (op:binop) (e1:expr) (e2:expr) (env:env_t): num = 
  let (n1, n2) = (evalExprNum e1 env, evalExprNum e2 env) in
  match op with 
  | ADD -> add_nums n1 n2
  | SUB -> add_nums n1 (negate_num n2)
  | MULT -> mult_nums n1 n2
  | DIV -> mult_nums n1 (one_over_num n2)
  | EXP -> exp_nums n1 n2


(**  ------------------------ TESTING ------------------------ *)

let test_expr = Definition("f", Vars.add "y" (Vars.add "x" Vars.empty), Binop(ADD, Unop(ABS, Var("x")), Const("q")) )
let test_env = Env.add "q" (EnvNum(ReIm(3.,2.))) Env.empty
let res = evalExpr test_expr test_env

let new_env = match res with | ResultEnv e -> e | _ -> failwith "NO"
let e,f = match Env.find "f" new_env with | EnvFn (_,e,f) -> e,f | _ -> failwith "NO"
let ans = f (Env.add "x" (EnvNum(ReIm(3.,1.))) test_env )

let test_env_string = string_of_env test_env
let test_env_string2 = string_of_env new_env
let test_expr_string = string_of_expr test_expr