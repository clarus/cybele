# Cybele
> A Coq plugin for simpler proofs by reflection or OCaml certificates.

![logo](http://cybele.gforge.inria.fr/img/icon.png)

[http://cybele.gforge.inria.fr/](http://cybele.gforge.inria.fr/)

## Install with OPAM
Make sure that you added the [Coq repository](http://coq.io/opam/):

    opam repo add coq-released https://coq.inria.fr/opam/released

and run:

    opam install coq-cybele

## Install from source
This plugin works with the 8.5 branch of Coq.

### Compilation
Before anything else, make sure that all the utilities of Coq are in
your path. Compile by typing:

    ./configure.sh
    make

Finally, install your plugin:

    make install

(as root if necessary).

### Examples
Go to `test-suite/`. You can try out each example doing a:

    ./configure.sh
    make
