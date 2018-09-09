#!/usr/bin/env bash

set -ev

eval $(opam config env)

opam update

opam pin add Core disel --yes --verbose
make -j4 -C Examples
