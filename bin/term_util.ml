open Util
open Syntax

module Term = struct
  let false_ = Const (CBool false)
  let ff = false_
  let bot = false_
  let true_ = Const (CBool true)
  let tt = true_
  let top = true_
  let int n = Const (CInt n)
  let var x = Var x
  let not t =
    match t with
    | Const (CBool b) -> Const (CBool (not b))
    | _ -> Op(Not, [t])
  let or_ ts =
    let ts = List.filter ((<>) (Const (CBool false))) ts in
    match ts with
    | [] -> Const (CBool false)
    | [t] -> t
    | _ when List.mem true_ ts -> true_
    | _ -> Op(Or, ts)
  let (||) t1 t2 = or_ [t1; t2]
  let and_ ts =
    let ts = List.filter ((<>) (Const (CBool true))) ts in
    match ts with
    | [] -> Const (CBool true)
    | [t] -> t
    | _ when List.mem false_ ts -> false_
    | _ -> Op(And, ts)
  let (&&) t1 t2 = and_ [t1; t2]
  let imply ts t2 =
    let t1 = and_ ts in
    match t1 with
    | Const (CBool true) -> t2
    | Const (CBool false) -> true_
    | _ -> Op(Imply, [t1; t2])
  let (=>) = imply
  let leq t1 t2 = Op(Leq, [t1; t2])
  let (<=) = leq
  let lt t1 t2 = Op(Lt, [t1; t2])
  let (<) = lt
  let geq t1 t2 = Op(Geq, [t1; t2])
  let (>=) = geq
  let gt t1 t2 = Op(Gt, [t1; t2])
  let (>) = gt
  let exists binds ts = Exists(binds, ts)
  let forall binds ts = Forall(binds, ts)
  let add ts =
    let ts = List.filter ((<>) (Const (CInt 0))) ts in
    match ts with
    | [] -> Const (CInt 0)
    | [t] -> t
    | _ -> Op(Add, ts)
  let (+) t1 t2 =
    if t1 = Const (CInt 0) then
      t2
    else if t2 = Const (CInt 0) then
      t1
    else
      add [t1; t2]
  let mul ts =
    match ts with
    | [] -> Const (CInt 1)
    | [t] -> t
    | _ when List.mem (Const (CInt 0)) ts -> Const (CInt 0)
    | _ -> Op(Mul, ts)
  let ( * ) t1 t2 =
    if t1 = Const (CInt 1) then
      t2
    else if t2 = Const (CInt 1) then
      t1
    else
      mul [t1; t2]
  let div t1 t2 = Op(Div, [t1; t2])
  let (/) = div
  let (mod) t1 t2 = Op(Mod, [t1; t2])
  let app f ts =
    if ts = [] then
      Var f
    else
      App(f, ts)
  let (@) = app
  let (@@) = app
  let if_ t1 t2 t3 = Op(If, [t1; t2; t3])
  let (=) t1 t2 =
    if t1 = true_ then
      t2
    else if t2 = true_ then
      t1
    else
      Op(Eq, [t1; t2])
end

let is_base_ty = function TInt | TBool -> true | _ -> false

let string_of_var ((s,b):var) =
  if b then
    Format.sprintf "|%s|" s
  else
    s

let pp_var fm x = Format.pp_print_string fm @@ string_of_var x

let var_of_string s : var =
  let s' =
    if s.[0] = '|' then
      let len = String.length s in
      assert (s.[len-1] = '|');
      String.sub s 1 (len-2)
    else
      s
  in
  s', not (String.for_all Char.is_letter s')

let new_var ?wrap s : var =
  match wrap with
  | None -> var_of_string s
  | Some b -> s, b

let pp_const fm c =
  match c with
  | CBool b -> Format.pp_print_bool fm b
  | CInt n -> Format.pp_print_int fm n

let string_of_op op =
  match op with
  | Not -> "not"
  | And -> "and"
  | Or -> "or"
  | Imply -> "=>"
  | Eq -> "="
  | Leq -> "<="
  | Lt -> "<"
  | Geq -> ">="
  | Gt -> ">"
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "div"
  | Mod -> "mod"
  | If -> "if"

let pp_list pp fm xs = print_list pp "@ " fm xs

let rec pp_ty fm ty =
  match ty with
  | TBool -> Format.fprintf fm "Bool"
  | TInt -> Format.fprintf fm "Int"
  | TFun(tys,ty) -> Format.fprintf fm "(%a) %a" (pp_list pp_ty) tys pp_ty ty

let pp_sorted_bind fm (x,ty) =
  Format.fprintf fm "(%s %a)" (string_of_var x) pp_ty ty

let rec pp_term fm t =
  match t with
  | Var x -> Format.pp_print_string fm (string_of_var x)
  | Const c -> pp_const fm c
  | Op(op, ts) -> Format.fprintf fm "(%s %a)" (string_of_op op) (pp_list pp_term) ts
  | Forall(binds, t) -> Format.fprintf fm "(forall (%a) %a)" (pp_list pp_sorted_bind) binds pp_term t
  | Exists(binds, t) -> Format.fprintf fm "(exists (%a) %a)" (pp_list pp_sorted_bind) binds pp_term t
  | Let _ -> unsupported "%s" __FUNCTION__
  | App(f, ts) -> Format.fprintf fm "(%s %a)" (string_of_var f) (pp_list pp_term) ts



let ty_of_smtlib (ty:Ast.ty) : ty =
  match ty with
  | Ty_bool -> TBool
  | Ty_real -> unsupported "Ty_real"
  | Ty_app ("Int", []) -> TInt
  | Ty_app (_, _) -> unsupported "Ty_app"
  | Ty_arrow (_, _) -> unsupported "Ty_arrow"

let aop_of_smtlib (op:Ast.arith_op) : op =
  match op with
  | Leq -> Leq
  | Lt -> Lt
  | Geq -> Geq
  | Gt -> Gt
  | Add -> Add
  | Minus -> Sub
  | Mult -> Mul
  | Div -> unsupported "non-integer division"

let rec term_of_smtlib (t:Ast.term) : term =
  let term_of = term_of_smtlib in
  match t with
  | True -> Const (CBool true)
  | False -> Const (CBool false)
  | Const s ->
      begin
        match int_of_string_opt s with
        | None when Exception.not_raise Z.of_string s ->
            unsupported "Integer literal exceeds the range of representable integers of type int"
        | None -> Var (var_of_string s)
        | Some n -> Const (CInt n)
      end
  | Arith(op,ts) -> Op(aop_of_smtlib op, List.map term_of ts)
  | App("div",[t1;t2]) -> Term.(term_of t1 / term_of t2)
  | App("mod",[t1;t2]) -> Term.(term_of t1 mod term_of t2)
  | App(f,ts) -> App(var_of_string f, List.map term_of ts)
  | HO_app _ -> unsupported "HO_app"
  | Match _ -> unsupported "Match"
  | If(t1,t2,t3) -> Term.if_ (term_of t1) (term_of t2) (term_of t3)
  | Let(binds, t) -> Let(Fmap.(list (var_of_string * term_of)) binds, term_of t)
  | Is_a _ -> unsupported "Is_a"
  | Fun _ -> unsupported "Fun"
  | Eq(t1,t2) -> Op(Eq, [term_of t1; term_of t2])
  | Imply(t1,t2) -> Op(Imply, [term_of t1; term_of t2])
  | And ts -> Op(And, List.map term_of ts)
  | Or ts -> Op(Or, List.map term_of ts)
  | Not t -> Op(Not, [term_of t])
  | Distinct _ -> unsupported "Distinct"
  | Cast _ -> unsupported "Cast"
  | Forall(binds,t) -> Forall(Fmap.(list (var_of_string * ty_of_smtlib)) binds, term_of t)
  | Exists(binds,t) -> Exists(Fmap.(list (var_of_string * ty_of_smtlib)) binds, term_of t)
  | Attr(t,_) -> term_of t

let ty_to_smtlib ty : Ast.ty =
  match ty with
  | TBool -> Ty_bool
  | TInt -> Ty_app ("Int", [])
  | TFun _ -> unsupported "%s" __FUNCTION__

let aop_to_smtlib (op:op) : Ast.arith_op =
  match op with
  | Leq -> Leq
  | Lt -> Lt
  | Geq -> Geq
  | Gt -> Gt
  | Add -> Add
  | Sub -> Minus
  | Mul -> Mult
  | _ -> invalid_arg "%s" __FUNCTION__
let is_aop op =
  Exception.not_raise aop_to_smtlib op

let rec term_to_smtlib t : Ast.term =
  match t with
  | Var x -> Const (string_of_var x)
  | Const (CBool true) -> True
  | Const (CBool false) -> False
  | Const (CInt n) when n < 0 -> Arith(Minus, [Const (string_of_int (-n))])
  | Const (CInt n) -> Const (string_of_int n)
  | Op(op, ts) when is_aop op ->
      Arith(aop_to_smtlib op, List.map term_to_smtlib ts)
  | Op(Div, ts) -> App("div", List.map term_to_smtlib ts)
  | Op(Mod, ts) -> App("mod", List.map term_to_smtlib ts)
  | Op(Not, [t]) -> Not (term_to_smtlib t)
  | Op(And, ts) -> And (List.map term_to_smtlib ts)
  | Op(Or, ts) -> Or (List.map term_to_smtlib ts)
  | Op(Imply, [t1; t2]) -> Imply(term_to_smtlib t1, term_to_smtlib t2)
  | Op(Eq, [t1; t2]) -> Eq(term_to_smtlib t1, term_to_smtlib t2)
  | Op(If, [t1; t2; t3]) -> If(term_to_smtlib t1, term_to_smtlib t2, term_to_smtlib t3)
  | Op _ -> Format.eprintf "%a@." pp_term t; assert false
  | Forall(binds, t) -> Forall(Fmap.(list (Pair.fst * ty_to_smtlib)) binds, term_to_smtlib t)
  | Exists(binds, t) -> Exists(Fmap.(list (Pair.fst * ty_to_smtlib)) binds, term_to_smtlib t)
  | Let(binds, t) -> Let(Fmap.(list (Pair.fst * term_to_smtlib)) binds, term_to_smtlib t)
  | App(f, ts) -> App(string_of_var f, List.map term_to_smtlib ts)

let make_trans f =
  let rec trans (t:term) =
    match f trans t with
    | None ->
        begin
          match t with
          | Var _ -> t
          | Const _ -> t
          | Op(op, ts) -> Op(op, List.map trans ts)
          | Forall(binds, t) -> Forall(binds, trans t)
          | Exists(binds, t) -> Exists(binds, trans t)
          | Let(binds, t) -> Let(List.map (Pair.map_snd trans) binds, trans t)
          | App(f, ts) -> App(f, List.map trans ts)
        end
    | Some t -> t
  in
  trans

let make_col f empty (++) =
  let col_list ?(acc=empty) cl xs = List.fold_left (fun acc x -> acc ++ cl x) acc xs in
  let rec col (t:term) =
    match f col t with
    | None ->
        begin
          match t with
          | Var _ -> empty
          | Const _ -> empty
          | Op(_, ts) -> col_list col ts
          | Forall(_, t) -> col t
          | Exists(_, t) -> col t
          | Let(binds, t) -> col_list ~acc:(col t) (snd |- col) binds
          | App(_, ts) -> col_list col ts
        end
    | Some acc -> acc
  in
  col

let subst_map map =
  make_trans (fun _tr t ->
      match t with
      | Var y when List.mem_assoc y map -> Some (List.assoc y map)
      | _ -> None)

let get_fv =
  let f _ = function Var x -> Some [x] | _ -> None in
  make_col f [] (@@@)

let rec has_app t =
  match t with
  | Var _ -> false
  | Const _ -> false
  | Op(_, ts) -> List.exists has_app ts
  | Forall(_, t) -> has_app t
  | Exists(_, t) -> has_app t
  | Let(binds, t) -> List.exists (snd |- has_app) binds || has_app t
  | App _ -> true

(**
   [is_simple t = true] if [t] does not contain [Forall], [Exists], [And], [Or], [Imply]
   Ignore [And] and [Or] if the conjuncts/disjuncts do not contains [App]
 *)
let rec is_simple (t:term) =
  match t with
   | Var _ | Const _ | App _ | Op((Leq|Lt|Geq|Gt|Add|Sub|Mul|Div|Mod|Imply), _) -> true
   | Op((Not|Eq|If), ts) -> List.for_all is_simple ts
   | Op((And|Or), ts) -> List.for_all (not -| has_app) ts
   | _ -> false

let rec decomp_op op t =
  match t with
  | Op(op', ts) when op = op' -> List.flatten_map (decomp_op op) ts
  | _ -> [t]
let decomp_and t = decomp_op And t
let decomp_or t = decomp_op Or t

let rec decomp_forall t =
  match t with
  | Forall(binds, t) ->
      let binds',t' = decomp_forall t in
      binds@binds', t'
  | _ -> [], t

let rec decomp_exists t =
  match t with
  | Exists(binds, t) ->
      let binds',t' = decomp_exists t in
      binds@binds', t'
  | _ -> [], t

let decomp_TFun ty =
  match ty with
  | TFun(tys, ty) -> tys, ty
  | _ -> invalid_arg "%s" __FUNCTION__

let rec convert2cnf (t:term) : term list list =
  match t with
  | Const (CBool true) -> []
  | Const (CBool false) -> [[]]
  | _ when is_simple t -> [[t]]
  | Op(And, _) ->
      let ts = decomp_and t in
      List.flatten_map convert2cnf ts
  | Op(Or, _) ->
      let ts = decomp_or t in
      let make_or cnf1 cnf2 =
        Combination.product cnf1 cnf2
        |> List.map (Fun.uncurry (@))
      in
      List.fold_right (make_or -| convert2cnf) ts [[]]
  | _ ->
      invalid_arg "%s: %a" __FUNCTION__ pp_term t

let push_not_into (t:term) : term =
  (* (aux true t <=> not t) and (aux false t <=> t)*)
  let rec aux flip (t:term) =
    match t with
    | Op(And, _) ->
        decomp_and t
        |> List.map (aux flip)
        |> if flip then Term.or_ else Term.and_
    | Op(Or, _) ->
        decomp_or t
        |> List.map (aux flip)
        |> if flip then Term.and_ else Term.or_
    | Op(Not, [t]) -> aux (not flip) t
    | Forall(binds, t) ->
        (if flip then Term.exists else Term.forall) binds (aux flip t)
    | Exists(binds, t) ->
        (if flip then Term.forall else Term.exists) binds (aux flip t)
    | Op(Imply, [t1; t2]) ->
        if flip then
          Term.and_ [aux false t1; aux true t2]
        else
          Term.or_ [aux true t1; aux false t2]
    | Let(binds, t) ->
        aux flip (subst_map binds t)
    | _ when is_simple t ->
        if flip then Term.not t else t
    | _ ->
        Format.eprintf "%a@." pp_term t;
        unsupported "%s" __FUNCTION__
  in
  aux false t

let rec eval env (t:term) : const =
  let inv() = invalid_arg "%s" __FUNCTION__ in
  let eval_bool t =
    match eval env t with
    | CBool b -> b
    | _ -> inv()
  in
  let eval_int t =
    match eval env t with
    | CInt b -> b
    | _ -> inv()
  in
  match t with
  | Var x -> List.assoc x env
  | Const c -> c
  | Op(Not, [t]) -> CBool (not (eval_bool t))
  | Op(And, ts) -> CBool (List.for_all eval_bool ts)
  | Op(Or, ts) -> CBool (List.exists eval_bool ts)
  | Op(Imply, [t1; t2]) -> CBool (eval_bool t1 => eval_bool t2)
  | Op(Eq, [t1; t2]) -> CBool (eval env t1 = eval env t2)
  | Op(Leq, [t1; t2]) -> CBool (eval_int t1 <= eval_int t2)
  | Op(Lt, [t1; t2]) -> CBool (eval_int t1 < eval_int t2)
  | Op(Geq, [t1; t2]) -> CBool (eval_int t1 >= eval_int t2)
  | Op(Gt, [t1; t2]) -> CBool (eval_int t1 > eval_int t2)
  | Op(Add, ts) -> CInt (List.fold_left (fun acc t -> eval_int t + acc) 0 ts)
  | Op(Sub, ts) -> CInt (List.reduce_left (-) @@ List.map eval_int ts)
  | Op(Mul, ts) -> CInt (List.fold_left (fun acc t -> eval_int t * acc) 1 ts)
  | Op(Div, ts) -> CInt (List.reduce_left (/) @@ List.map eval_int ts)
  | Op(Mod, [t1; t2]) -> CInt (eval_int t1 mod eval_int t2)
  | Op _ -> inv()
  | Forall _ -> inv()
  | Exists _ -> inv()
  | Let _ -> inv()
  | App _ -> inv()

module Print = struct
  include Print_

  let var = pp_var
  let const = pp_const
  let term = pp_term
end
