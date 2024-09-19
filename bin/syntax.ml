open Util

module SMTLIB = Smtlib_utils.V_2_6
module Ast = SMTLIB.Ast

type statement =
  | Assert of term
  | Statement of Ast.statement [@printer Ast.pp_stmt]

and term =
  | Var of var
  | Const of const
  | Op of op * term list
  | Forall of sorted_binds * term
  | Exists of sorted_binds * term
  | Let of binds * term
  | App of var * term list

and op =
  | Not
  | And
  | Or
  | Imply
  | Eq
  | Leq
  | Lt
  | Geq
  | Gt
  | Add
  | Sub
  | Mul
  | Div
  | Mod
  | If
and binds = bind list
and bind = var * term
and sorted_binds = sorted_bind list
and sorted_bind = var * ty
and ty =
  | TInt
  | TBool
  | TFun of ty list * ty (* [ty] must not TFun *)
and var = string * bool (* true represents this must be wrapped with || when printing *)
and const =
  | CBool of bool
  | CInt of int
and tenv = (var * ty) list

and env = (var * ty) list
[@@deriving show]

let _Var x = Var x
let _Const c = Const c
let _Op(op, ts) = Op(op, ts)
let _Forall(binds, t) = Forall(binds, t)
let _Exists(binds, t) = Exists(binds, t)
let _Let(binds, t) = Let(binds, t)
let _App(f, ts) = App(f, ts)

let _CBool b = CBool b
let _CInt n = CInt n

module Val = struct
  let _Var    = function Var x            -> x        | _ -> invalid_arg "%s" __FUNCTION__
  let _Const  = function Const c          -> c        | _ -> invalid_arg "%s" __FUNCTION__
  let _Op     = function Op(op, ts)       -> op, ts   | _ -> invalid_arg "%s" __FUNCTION__
  let _Forall = function Forall(binds, t) -> binds, t | _ -> invalid_arg "%s" __FUNCTION__
  let _Exists = function Exists(binds, t) -> binds, t | _ -> invalid_arg "%s" __FUNCTION__
  let _Let    = function Let(binds, t)    -> binds, t | _ -> invalid_arg "%s" __FUNCTION__
  let _App    = function App(f, ts)       -> f, ts    | _ -> invalid_arg "%s" __FUNCTION__

  let _TFun = function TFun(tys, ty) -> tys, ty | _ -> invalid_arg "%s" __FUNCTION__
end

let string_of_var ((s,b):var) =
  if b then
    Format.sprintf "|%s|" s
  else
    s

let pp_var fm x = Format.pp_print_string fm (string_of_var x)
