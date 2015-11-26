# Constructors
An example Coq plugin.

> Copyright 2010 Matthieu Sozeau <mattam@mattam.org>
Distributed under the terms of the New BSD License,
see LICENSE for details.

> Updated for Coq 8.4pl2 and 8.4pl3 by Wojciech Jedynak <wjedynak@gmail.com>.

This archive contains an example Coq plugin that implements a
tactic to get the constructors of an inductive type in Ltac.
It serves as a documented example on both the plugin system
and how to write simple tactics in OCaml.

The archive has 3 subdirectories:

* `src/` contains the code of the plugin in `constructors.ml` and a support file
  for building the constructors plugin;
* `theories/` contains support Coq files for the plugin. `Dynamic.v`
  is referenced from the code of the plugin above. `Constructors.v` declares
  the plugin on the Coq side;
* `test-suite/` just demonstrates a use of the plugin.

## Installation
### With OPAM
Make sure that you added the Coq repository:

    opam repo add coq-released https://coq.inria.fr/opam/released

and run:

    opam install coq-constructors

### From the sources
First, you should have `coqc`, `ocamlc` and `make` in your path. Then simply do:

    coq_makefile -f Make -o Makefile

to generate a `Makefile` from the description in `Make`, then `make`.
This will consecutively build the plugin, the supporting
theories and the test-suite file.

You can then either `make install` the plugin or leave it in its
current directory. To be able to import it from anywhere in Coq,
simply add the following to `~/.coqrc`:

    Add Rec LoadPath "path_to_constructors/theories" as Constructors.
    Add ML Path "path_to_constructors/src".
