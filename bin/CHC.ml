open Util
open Syntax
open Term_util

module Dbg = struct
  let dbg = debug_mode_of __MODULE__
  let printf f = if dbg then Format.printf f else Format.iprintf f
  let fprintf fm f = if dbg then Format.fprintf fm f else Format.ifprintf fm f
end

type clause = {env:tenv; head:head; body:body}
and head = Syntax.term
and body = Syntax.term list
and t =
  {rules : clause list;
   genv : env}

and model = (var * (var list * term)) list
and result = (unit, (clause * (var * const) list) list) Result.t [@opaque]
[@@deriving show]

let pp_clause fm {head; body; _} =
  Format.fprintf fm "@[<hov 4>@[(and %a)@] =>@ @[%a@]@]" (pp_list pp_term) body pp_term head

let to_CHC genv asserts =
   let rules =
     asserts
     |> List.flatten_map (fun t ->
            let env,t = decomp_forall @@ push_not_into t in
            t
            |> convert2cnf
            |> List.map (fun conj ->
                   let pos,neg =
                     conj
                     |> List.partition (function
                            | Var x -> not (List.mem_assoc x env)
                            | App _ | Exists _ | Op(Or, _) -> true
                            | _ -> false)
                   in
                   let head =
                     match pos with
                     | [] -> Term.bot
                     | [t] -> t
                     | _ -> unsupported "The input is not CHC?"
                   in
                   let body =
                     List.L.map neg ~f:(function
                         | Op(Not, [t]) -> t
                         | t -> Term.not t)
                   in
                   {env; head; body}))
   in
   {rules; genv}

let from_CHC {rules; genv} =
  let rules =
    rules
    |> List.map (fun {env; head; body} ->
           let t =Term.(body => head) in
           if env = [] then
             t
           else
             Forall(env, t))
  in
  rules, genv

let is_definite (clause : clause) : bool =
  match clause.head with
  | App _ -> true
  | _ -> false

let definite_of (chc : t) : t =
  let rules = List.filter is_definite chc.rules in
  {chc with rules}

let pvars_of {genv; _} : var list =
  List.map fst genv

let apply_model model {head; body; _} : term =
  let app =
    make_trans (fun _tr t ->
        match t with
        | Var x ->
            List.assoc_opt x model
            |> Option.map snd
        | App(f, ts) ->
            let xs,t =
              try
                List.assoc f model
              with Not_found ->
                Format.eprintf "NOT FOUND: %a@." pp_var f;
                assert false
            in
            assert (List.length xs = List.length ts);
            Some (subst_map (List.combine xs ts) t)
        | _ -> None)
  in
  app @@ Term.(body => head)

let check_model_rule model genv rule =
  apply_model model rule
  |> SMT.check_valid (rule.env @@@ genv)

let check_model (model:model) chc : result =
  let rec check rules =
    match rules with
    | [] -> Ok ()
    | rule::rules ->
        match check_model_rule model chc.genv rule with
        | Valid -> check rules
        | Invalid cex -> Error [rule, cex]
  in
  check chc.rules

let check_model_all (model:model) chc : result =
  Dbg.printf "[%s] model: %a@." __FUNCTION__ pp_model model;
  Dbg.printf "[%s] chc: %a@." __FUNCTION__ (pp_list pp_clause) chc.rules;
  match
    chc.rules
    |> List.map (Pair.add_right @@ check_model_rule model chc.genv)
    |> List.filter_map (function _, SMT.Valid -> None | cl, Invalid cex -> Some (cl, cex))
  with
  | [] -> Ok ()
  | cex -> Error cex

let arg_tys_of p env =
  List.assoc p env
  |> Val._TFun
  |> fst

let map_clause f {env; body; head} =
  let body = List.map f body in
  let head = f head in
  {env; body; head}

let map f {genv; rules} =
  let rules = List.map (map_clause f) rules in
  {genv; rules}
