# Disel - Distributed Separation Logic

Implementation and case studies of Disel, a separation-style logic for
compositional verification of distributed systems.

## Building the Project

### Requirements

* Coq 8.6 (available from https://coq.inria.fr/download)
* Mathematical Components 1.6.1 (http://math-comp.github.io/math-comp/)

### Building

If Coq is not installed such that its binaries like `coqc` and
`coq_makefile` are in the `PATH`, then the `COQBIN` environment variable
must be set to point to the directory containing such binaries.  For
example:

```
export COQBIN=/home/user/coq/bin/
```

Next, run `make clean; make` from the root folder. This will build all
the libraries and will check all the proofs.

## Project Structure

* `Heaps` -- A theory of partial finite heaps; 

* `Core` -- Disel implementation, metatheory and inference rules;

* `Examples` -- Case studies implemented in Disel

	- `Calculator` -- the calculator system;

	- `Greeter` -- a toy "Hello World"-like protocol, where
         participants can only exchange greetings with each other;

	- `TwoPhaseCommit` -- Two Phase Commit protocol implementation;

	- `Query` -- querying protocol and its composition with Two Phase
      Commit via hooks;

* `shims` -- DiSeL runtime system
    - Note that in order to run the examples, you need OCaml installed.
      We tested with OCaml version 4.02.3, but others may work as well.

    - Run `make CalculatorMain.d.byte` to build the Calculator
      application using `extraction/calculator` as the build directory.
      (Note that all the proofs will be checked as well.) Then run
      `./scripts/calculator.sh` to execute the system in three processes
      on the local machine.

    - Run `make TPCMain.d.byte` from the root folder to build the
      Two-Phase Commit application. Then run `./scripts/tpc.sh` to
      execute the system in four processes on the local machine.
