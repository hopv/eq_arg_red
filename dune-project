(lang dune 3.6)

(name eq_arg_red)

(generate_opam_files true)

(source
 (bitbucket hopv/eq_arg_red))

(authors "Ryosuke Sato")

(maintainers "Ryosuke Sato")

(license "Apache-2.0")

;(documentation https://url/to/documentation)

(package
 (name eq_arg_red)
 (synopsis "eq_arg_red: a preprocessor for CHC solving")
 (description "eq_arg_red: a preprocessor for CHC solving")
 (depends
  ocaml
  dune
  (z3 (>= 4.11.0))
  zarith
  smtlib-utils
  ppx_deriving_cmdliner
  sexplib
  batteries))
