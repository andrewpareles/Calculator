module Name = String

type name = Name.t


type reIm = float * float (* A + iB *)
type exp = float * float (* (A,B) in A e^iB *)
type num = 
| Exp of exp
| ReIm of reIm
(* | None (* shortcuts the process so no more calculations are needed*) if use, 
rename None to NaN or something, and make it NaN of int or string so can specify the problem
, will have to make to_reIm and to_exp return a type like an option (Some/None),
maybe with a different name than option 
 *)

type binop = ADD | SUB | MULT | DIV | EXP 
type unop = NEG | ABS


(* env_elt_names are the names of the variables (ie elements in env) that go into the function *)
module EnvEltNames = Set.Make(Name)
type env_elt_names = EnvEltNames.t

type expr = (* just for a single expression, eg f(x)= (x^3 + 1) / 2  *)
| Definition of name*env_elt_names*expr (* (name, params, expression) eg1: "<A|B>" = expr, eg2: f(x) = x^2*)
| Unop of unop*expr (* eg -1*)
| Binop of binop*expr*expr (*eg: 1 + 2 *)
| Number of num (* eg 5*)
| Const of name (* eg g*) (* value is evaluated using environment  *)
| Var of name (* eg x in f(x) = x, variable in a function*)


module Env = Map.Make(Name) (* env of env, eg x = 1, f(x) *)
(* env is name -> env_elt *)
(* env_elt_names is the params, expr is the expr of the fn (to retain understandability) *)
type env_elt = EnvNum of num | EnvFn of env_elt_names*expr*(env -> num) 
and env = env_elt Env.t (* Env.t just means an environment from a string. env_elt tells it string -> env_elt *)


type result = 
| ResultNum of num 
| ResultEnv of env

let pi = 3.141592653589793238462643383279502884197169399375105820974944592307

exception Error of string
let failwith str = raise (Error str)

(* ------------------------ num CONVERSIONS AND OPERATIONS ------------------------*)
let to_reIm (n:num) : reIm = 
  match n with
  | Exp(a,b) -> (a*.cos(b), a*.sin(b))
  | ReIm(a,b) -> (a,b)
  (* | None -> None *)

let to_exp (n:num) : exp = 
  match n with 
  | ReIm(a,b) -> (sqrt(a**2.+.b**2.),atan(b/.a))
  | Exp(a,b) -> (a,b)
  (* | None -> None *)

let negate_num (n:num) : num = 
  match n with 
  | Exp(a,b) -> Exp(a, b+.pi/.2.)
  | ReIm(a,b) -> ReIm(-.a, -.b)
  (* | None -> None *)

let abs_num (n:num) : num = 
  match n with 
  | ReIm(a,b) -> ReIm(sqrt(a**2.+.b**2.), 0.)
  | Exp(a,b) -> Exp(a, 0.)
  (* | None -> None *)

let add_nums (n1:num) (n2:num) : num = 
  (* I know we don't need to wrap with ReIm, but I like it more this way *)
  let (a,b), (c,d) = (to_reIm n1), (to_reIm n2) (* CONVERSION *)
  in ReIm(a+.c, b+.d)

let one_over_num (n:num) : num = 
  match n with 
  | Exp(a,b) -> Exp(1./.a, -.b)
  | ReIm(a,b) -> ReIm(a/.(a**2.+.b**2.), -.b/.(a**2.+.b**2.))
  (* | None -> None *)

let rec mult_nums (n1:num) (n2:num) : num = 
  match (n1, n2) with 
  | (Exp(a,b), Exp(c,d)) -> Exp(a*.c, b+.d)
  | (ReIm(a,b), ReIm(c,d)) -> ReIm(a*.c-.b*.d, b*.c+.a*.d)
  | (ReIm(a,b), Exp(c,d)) | (Exp(c,d), ReIm(a,b)) -> (
    let n1' = ReIm(a,b) in 
    let n2' = (ReIm(to_reIm (Exp(c,d)))) (* CONVERSION *) 
    in mult_nums n1' n2'  
  )
  (* | (None, _) | (_, None) -> None *)

let rec ln (n1:num) : num = 
  match n1 with 
  | Exp(a,b) -> ReIm(log a, b)
  | ReIm(a,b) -> ln ( Exp(to_exp (ReIm(a,b))) ) (* CONVERSION *)
  (* | None -> None *)

let rec exp_nums (n1:num) (n2:num) : num = 
  let (a,b), (c,d) = (to_exp n1), (to_reIm n2) (* CONVERSION *) 
  in ( Exp(a**c *. (exp 1.)**(-.(b*.d)), b*.c +. d*.(log a)) )


let find_num_in_env (name:name) (env:env) : num = 
  match Env.find_opt name env with (* env_elt *)
  | Some (EnvNum(found)) -> found
  | Some (EnvFn(_)) -> failwith ("Environment element " ^ name ^ " was found, but it was a function, not a number.")
  | None -> failwith ("No such environment element " ^ name ^ " was defined when looking for a number.")


(**  ------------------------ TOSTRING FUNCTIONS ------------------------ *)
let string_of_num (num:num) : string =
  "("^(
  match num with
  | ReIm(a,b) -> (Float.to_string a) ^ "+" ^ (Float.to_string b) ^ "i"
  | Exp(a,b) -> (Float.to_string a) ^ "e^(" ^ (Float.to_string b) ^ "i)"
  (* | None -> "None" *)
  )
  ^")"

let string_of_env_elt_names (names:env_elt_names) : string = 
  let fold_fn elt s = s ^ " " ^ (String.trim elt)
  in "("^String.trim (EnvEltNames.fold fold_fn names "")^")"

let string_of_binop (op:binop) (n1_str:string) (n2_str:string) : string =
  "("^n1_str^(
    match op with
    | ADD -> "+"
    | SUB -> "-"
    | MULT -> "*"
    | DIV -> "/"
    | EXP -> "^")
  ^n2_str^")"

let string_of_unop (op:unop) (num_str:string) : string = 
  match op with 
  | NEG -> "-("^num_str^")"
  | ABS -> "|"^num_str^"|"

let rec string_of_expr (e:expr) : string = 
  match e with 
  | Definition(name, names, e) -> (String.trim name)^(string_of_env_elt_names names)^"="^(string_of_expr e)
  | Unop(op, e) -> string_of_unop op (string_of_expr e)
  | Binop(op, e1, e2) -> string_of_binop op (string_of_expr e1) (string_of_expr e2)
  | Number(num) -> string_of_num num
  | Const(name) -> String.trim name
  | Var(name) -> String.trim name

let string_of_envelt (envelt:env_elt) : string = 
  match envelt with
  | EnvNum num -> string_of_num num
  | EnvFn(names,e,_) -> string_of_env_elt_names names^"->"^string_of_expr e

let string_of_env (env:env) : string = 
  let fold_fn = (fun k v acc -> acc^"["^k^"]="^string_of_envelt v^" ") in 
  ("<"^String.trim (Env.fold fold_fn env "")^">")

let string_of_result (res:result) : string = 
  match res with 
  | ResultNum num -> string_of_num num
  | ResultEnv env -> string_of_env env 

(* ------------------------ SEARCH ENVIRONMENT FUNCTIONS ------------------------*)

let env_has_elt (env:env) (elt_name:name) : bool = 
  match Env.find_opt elt_name env with 
  | Some(_) -> true 
  | None -> false

let env_has_all_elts (env:env) (elt_names:env_elt_names) : bool = 
  EnvEltNames.for_all (fun elt -> env_has_elt env elt) elt_names


(* ------------------------ EVALUATION ------------------------ *)

let rec evalExpr (e:expr) (env:env) : result = 
  match e with 
  | Definition(name, enveltnames, e) -> ResultEnv(evalDefinition name enveltnames e env)
  | e -> ResultNum (begin
    match e with (* these don't change env *)
    | Unop(op, e1) -> evalUnop op e1 env 
    | Binop(op, e1, e2) -> evalBinop op e1 e2 env 
    | Number(num) -> num
    | Const(name) -> find_num_in_env name env
    | Var(name) when (env_has_elt env name) -> find_num_in_env name env
    | Var(name) -> failwith ("Could not find variable " ^ name ^ " in environment " ^ string_of_env env ^ ".")
    | _ -> failwith "Just here to shut up about Definition, which was already matched"
    end)

and evalExprNum (e:expr) (env:env) : num =
  match evalExpr e env with 
  | ResultNum(num) -> num
  | ResultEnv(_) -> failwith ("Could not evaluate expression " ^ string_of_expr e ^ " to a number.")

and evalDefinition (name:name) (enveltnames:env_elt_names) (e:expr) (env:env): env = 
  Env.add name (EnvFn(enveltnames, e, fun (env:env) -> evalExprNum e env)) env

and evalUnop (op:unop) (e1:expr) (env:env) : num = 
  let num = (evalExprNum e1 env) in 
  match op with
  | NEG -> negate_num num
  | ABS -> abs_num num 
    
and evalBinop (op:binop) (e1:expr) (e2:expr) (env:env): num = 
  let (n1, n2) = (evalExprNum e1 env, evalExprNum e2 env) in
  match op with 
  | ADD -> add_nums n1 n2
  | SUB -> add_nums n1 (negate_num n2)
  | MULT -> mult_nums n1 n2
  | DIV -> mult_nums n1 (one_over_num n2)
  | EXP -> exp_nums n1 n2


(**  ------------------------ TESTING ------------------------ *)

let test_env = Env.add "q" (EnvNum(ReIm(3.,2.))) Env.empty
let _ = print_endline (string_of_env test_env)

let test_expr = Definition("f", EnvEltNames.(empty |> add "x" |> add "y"), Binop(ADD, Unop(ABS, Binop(EXP, Number(ReIm(2.,0.)), Var("x"))), Const("q")) )
let _ = print_endline (string_of_expr test_expr)

let res = evalExpr test_expr test_env
let _ = print_endline (string_of_result res)

let ResultEnv new_env = res
let EnvFn (_,e,f) =  Env.find "f" new_env
let ans = f (Env.add "x" (EnvNum(ReIm(3.,1.))) test_env )
let _ = print_endline (string_of_num ans)

