type params = {
  conditional: bool;
  (** find conditional equalities *)

  input: string; [@pos 0] [@docv "INPUT"] [@default ""]
  (** The input file *)
} [@@deriving cmdliner]

let parse_and_run f =
  let info = Cmdliner.Cmd.info "eq_arg_red" in
  let term = Cmdliner.Term.(const f $ params_cmdliner_term ()) in
  let cmd = Cmdliner.Cmd.v info term in
  exit (Cmdliner.Cmd.eval cmd)
