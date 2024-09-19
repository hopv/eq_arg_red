open Util
open Syntax
open Term_util

module Dbg = struct
  let dbg = debug_mode_of __MODULE__
  let printf f = if dbg then Format.printf f else Format.iprintf f
  let fprintf fm f = if dbg then Format.fprintf fm f else Format.ifprintf fm f
end

type result = Valid | Invalid of counterexample
and counterexample = (var * const) list

module Z3 = struct
  module A = Z3.Arithmetic
  module I = Z3.Arithmetic.Integer
  module B = Z3.Boolean
  module E = Z3.Expr
  module S = Z3.Solver

  let mk_int_sort ctx = I.mk_sort ctx
  let mk_new_var ctx s ty = E.mk_fresh_const ctx s ty
  let mk_new_int_var ctx s = mk_new_var ctx s (mk_int_sort ctx)

  type expr = E.expr

  module type CTX = sig
    val ctx : Z3.context
  end

  module Make (Ctx:CTX) = struct
    let ctx = Ctx.ctx
    let var = E.mk_const ctx
    let true_ = B.mk_true ctx
    let false_ = B.mk_false ctx
    let int = I.mk_numeral_i ctx
    let not = B.mk_not ctx
    let eq = B.mk_eq ctx
    let add = (fun t1 t2 -> A.mk_add ctx [t1; t2])
    let sub = (fun t1 t2 -> A.mk_sub ctx [t1; t2])
    let mul = (fun t1 t2 -> A.mk_mul ctx [t1; t2])
    let lt = A.mk_lt ctx
    let leq = A.mk_le ctx
    let gt = A.mk_gt ctx
    let geq = A.mk_ge ctx
  end

  let sort_of_ty ctx ty =
    match ty with
    | TInt -> I.mk_sort ctx
    | TBool -> B.mk_sort ctx
    | _ ->
        Format.eprintf "%a@." pp_ty ty;
        invalid_arg "%s" __FUNCTION__

  let const_of_var ctx x ty =
    let x = Z3.Symbol.mk_string ctx (fst x) in
    match ty with
    | TInt -> I.mk_const ctx x
    | TBool -> B.mk_const ctx x
    | _ -> invalid_arg "%s" __FUNCTION__

  let rec expr_of_term (ctx:Z3.context) env (t:term) : E.expr =
    let module T = Make(struct let ctx = ctx end) in
    let tr = expr_of_term ctx env in
    match t with
    | Const (CBool true) -> T.true_
    | Const (CBool false) -> T.false_
    | Const (CInt n) -> T.int n
    | Var x ->
        let ty =
          try
            List.assoc x env
          with Not_found ->
            Format.eprintf "%s not_found@." (string_of_var x);
            assert false
        in
        let sort = sort_of_ty ctx ty in
        E.mk_const ctx (Z3.Symbol.mk_string ctx (fst x)) sort
    | Op(Sub, [t1]) -> A.mk_unary_minus ctx (tr t1)
    | Op((Add|Sub|Mul) as op, ts) ->
        let mk =
          match op with
          | Add -> A.mk_add
          | Sub -> A.mk_sub
          | Mul -> A.mk_mul
          | _ -> assert false
        in
        mk ctx (List.map tr ts)
    | Op((Div|Mod) as op, [t1; t2]) ->
        let mk =
          match op with
          | Div -> A.mk_div
          | Mod -> I.mk_mod
          | _ -> assert false
        in
        mk ctx (tr t1) (tr t2)
    | Op((Leq|Lt|Geq|Gt) as op, [t1;t2]) ->
        let mk =
          match op with
          | Leq -> A.mk_le
          | Lt -> A.mk_lt
          | Geq -> A.mk_ge
          | Gt -> A.mk_gt
          | _ -> assert false
        in
        mk ctx (tr t1) (tr t2)
    | Op(Eq, [t1; t2]) -> B.mk_eq ctx (tr t1) (tr t2)
    | Op(Imply, [t1; t2]) -> B.mk_implies ctx (tr t1) (tr t2)
    | Op(And, ts) -> B.mk_and ctx (List.map tr ts)
    | Op(Or, ts) -> B.mk_or ctx (List.map tr ts)
    | Op(Not, [t]) -> T.not (tr t)
    | Op(If, [t1; t2; t3]) -> B.mk_ite ctx (tr t1) (tr t2) (tr t3)
    | Op(_, _) -> unsupported "%s(%a)" __FUNCTION__ pp_term t
    | App _ -> unsupported "%s(%a)" __FUNCTION__ pp_term t
    | Let _ -> unsupported "%s(%a)" __FUNCTION__ pp_term t
    | Forall(bind, t) ->
        let xs = List.map (Fun.uncurry @@ const_of_var ctx) bind in
        Z3.Quantifier.mk_forall_const ctx xs (tr t) None [] [] None None
        |> Z3.Quantifier.expr_of_quantifier
    | Exists(bind, t) ->
        let xs = List.map (Fun.uncurry @@ const_of_var ctx) bind in
        Z3.Quantifier.mk_exists_const ctx xs (tr t) None [] [] None None
        |> Z3.Quantifier.expr_of_quantifier
  let expr_of_term (ctx:Z3.context) env (t:term) : E.expr =
    Dbg.printf "[%s] t: @[%a@." __FUNCTION__ pp_term t;
    expr_of_term ctx env t


  let const_of_expr e =
    if Z3.Arithmetic.is_int e then
      e
      |> Z3.Arithmetic.Integer.get_big_int
      |> Z.to_int
      |> _CInt
    else if Z3.Boolean.is_bool e then
      match Z3.Boolean.get_bool_value e with
      | L_TRUE -> CBool true
      | L_FALSE -> CBool false
      | L_UNDEF -> unsupported "%s" __FUNCTION__
    else
      unsupported "%s" __FUNCTION__

  let solve env ts =
    (* Format.printf "ts: %a@." Print.(list term) ts; *)
    let ctx = Z3.mk_context [] in
    let es = List.map (expr_of_term ctx env) ts in
    let solver = S.mk_solver ctx None in
    (* Format.printf "es: %s@." (String.join " /\\ " @@ List.map E.to_string es); *)
    match S.check solver es with
    | S.SATISFIABLE ->
        begin
          (* Format.printf "env: %a@." Print.(list (string * ty)) env; *)
          match S.get_model solver with
          | None -> Error ()
          | Some model ->
              Dbg.printf "[%s] model: %s@." __LOC__ (Z3.Model.to_string model);
              let sol =
                model
                |> Z3.Model.get_const_decls
                |> List.map (fun decl ->
                       let x =
                         decl
                         |> Z3.FuncDecl.get_name
                         |> Z3.Symbol.to_string
                       in
                       let r =
                         decl
                         |> Z3.Model.get_const_interp model
                         |> Option.get
                         |> const_of_expr
                       in
                       x, r)
              in
              let sol' =
                env
                |> List.filter_map (fun (x,ty) -> if is_base_ty ty then Some x else None)
                |> List.map fst
                |> List.filter_out (List.mem_assoc -$- sol)
                |> List.map (Pair.pair -$- (CInt 0))
                |> (-$-) (@@@) sol
              in
              Ok sol'
        end
    | S.UNSATISFIABLE | S.UNKNOWN -> Error ()

  let check_valid env t =
    match solve env [Term.not t] with
    | Ok sol -> Error sol
    | Error () -> Ok ()
end

let check_valid env t =
  match Z3.check_valid env t with
  | Ok () -> Valid
  | Error cex -> Invalid (Fmap.(list (fst var_of_string)) cex)
