`eq_arg_red` reduces the arguments of the predicates in an input CHC file.
See [Ikeda, Sato & Kobayashi, APLAS 2013] for the details.


How to build
============
The following commands produce the executable `bin/main.exe`:
```
$ dune build eq_arg_red.opam
$ opam install --deps-only .
$ dune build --release
```

How to use
==========

See `bin/main.exe --help`.


Licenses
========

 This software is licensed under the Apache License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0.txt).


Author
======

 `eq_arg_red` is developed/maintained by Ryosuke SATO <rsato@acm.org>
