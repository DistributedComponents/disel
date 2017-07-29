set -ev

opam init --yes --no-setup
eval $(opam config env)

opam repo add coq-released https://coq.inria.fr/opam/released

opam pin add coq $COQ_VERSION --yes --verbose

opam pin add Heaps --yes --verbose
opam pin add Core --yes --verbose
make -C Examples
