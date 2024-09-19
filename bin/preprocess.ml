open! Util
open! Syntax

type t = Cmd.params -> CHC.t -> CHC.t * (CHC.model -> CHC.model)

let red_arg_eq params =
  if params.Cmd.conditional then
    Red_arg_cond_eq.run
  else
    Red_arg_simp_eq.run

let preprocesses : t list =
  [red_arg_eq]

let apply params (chc,tr) pp =
  let chc',tr' = pp params chc in
  chc', tr -| tr'

let do_all params chc =
  let chc',_inv_model =
    List.fold_left (apply params) (chc,Fun.id) preprocesses
  in
  chc'
