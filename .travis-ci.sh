set -ev

opam init --yes --no-setup
eval $(opam config env)

opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev

opam pin add coq $COQ_VERSION --kind=version --yes --verbose
opam pin add coq-mathcomp-ssreflect $SSREFLECT_VERSION --kind=version --yes --verbose

opam pin add Heaps --yes --verbose
opam pin add Core --yes --verbose
make -C Examples
