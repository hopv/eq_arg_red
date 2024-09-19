open Util

module SMTLIB = Smtlib_utils.V_2_6
module Ast = SMTLIB.Ast

type state =
  {origs_rev : Ast.stmt list;
   env : Syntax.env;
   asserts : Syntax.term list}

let init_env = []
let init_state =
  {origs_rev = [];
   env = init_env;
   asserts = []}

let read st (statement:Ast.statement) =
  let origs_rev = statement.stmt :: st.origs_rev in
  let asserts,env =
    match statement.stmt with
    | Stmt_assert t ->
        let t = Term_util.term_of_smtlib t in
        t::st.asserts, st.env
    | Stmt_reset -> [], init_env
    | Stmt_reset_assertions -> [], st.env
    | Stmt_decl {fun_ty_vars; fun_name; fun_args; fun_ret} ->
        if fun_ty_vars <> [] then unsupported "%s" __FUNCTION__;
        if fun_ret <> Ty_bool then unsupported "%s" __FUNCTION__;
        let p = Term_util.var_of_string fun_name in
        let ty = Syntax.TFun(List.map Term_util.ty_of_smtlib fun_args, Term_util.ty_of_smtlib fun_ret) in
        st.asserts,
        (p,ty)::st.env
    | _ -> st.asserts, st.env
  in
  {origs_rev; env; asserts}

let to_statements get_model (chc,env) =
  let decl_of (p,ty) =
    let tys,ty' = Syntax.Val._TFun ty in
    let tyvars = [] in
    let fun_name = Term_util.string_of_var p in
    let fun_args = List.map Term_util.ty_to_smtlib tys in
    let fun_ret = Term_util.ty_to_smtlib ty' in
    Ast.decl_fun ~tyvars fun_name fun_args fun_ret
  in
  Ast.set_logic "HORN" ::
    List.map decl_of env @
    List.rev_map (Ast.assert_ -| Term_util.term_to_smtlib) chc @
    [Ast.check_sat ()] @
    if get_model then [Ast.get_model ()] else []

let print_error e =
  match e with
  | Unsupported s -> Printf.eprintf "Unsupported: %s\n" s
  | TimeOut -> Printf.eprintf "Timeout\n"
  | Killed -> Printf.eprintf "Killed\n"
  | e -> Printf.eprintf "Error: %s\n" (Printexc.to_string e)

let main params =
  let cin,close =
    if params.Cmd.input = "" then
      stdin, ignore
    else
      let cin = open_in params.input in
      cin, fun () -> close_in cin
  in
  Exception.finally close
    (fun () ->
      let st =
        cin
        |> SMTLIB.parse_chan_exn
        |> List.fold_left read init_state
      in
      st.asserts
      |> CHC.to_CHC st.env
      |> Preprocess.do_all params
      |> CHC.from_CHC
      |> to_statements false
      |> List.iter (Format.printf "%a@." Ast.pp_stmt)) ()

let () =
  if !Sys.interactive then
    ()
  else
    try
      Cmd.parse_and_run main
    with e ->
      print_error e;
      exit 1
