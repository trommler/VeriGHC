# VeriGHC
Towards a verified back-end for The Glorious Glasgow Haskell Compilation System

To check out:

``git clone --recursive``

When updating:

``git pull``

``git submodule update``

VeriGHC installs its own sandboxed copy of coq and libraries at
the required versions.
To set up the sandbox run the following once:

``make builddep``

Then run

``make``


To build hs-to-coq:

You need the `stack` tool available from
https://docs.haskellstack.org/en/stable/install_and_upgrade/
or as a package from your favourite distribution.

You also need `opam` on your path. See [How to install
opam](https://opam.ocaml.org/doc/Install.html#Binary-distribution) for
instructions.
