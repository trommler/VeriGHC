# VeriGHC
Towards a verified back-end for The Glorious Glasgow Haskell Compilation System

To check out:

``git clone --recursive``

When updating:

``git pull``

``git submodule update``

``cd ext/VST``

``make``

(and wait for very long time)

``cd ../..``

``make``


To build hs-to-coq:

You need the `stack` tool available from
[[https://docs.haskellstack.org/en/stable/install_and_upgrade/]]
or as a package from your favourite distribution.

``cd ext/hs-to-coq``

``stack setup``

``stack build``
