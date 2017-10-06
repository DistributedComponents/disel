# Disel - Distributed Separation Logic

Implementation and case studies of Disel, a separation-style logic for
compositional verification of distributed systems.

This code accompanies the paper entitled **Programming and Proving with
Distributed Protocols** by Ilya Sergey, James R. Wilcox and Zachary
Tatlock, conditionally accepted for publication at POPL 2018.

## Building the Project

A VM has been provided for your convenience and is described below. If
you would like to use your own machine, the following dependencies are
necessary.

### Requirements

* Coq 8.6 (available from https://coq.inria.fr/download)
* Mathematical Components 1.6.1 (http://math-comp.github.io/math-comp/)
* OCaml 4.0.1 or later (to compile and run the extracted applications)

If Coq is not installed such that its binaries like `coqc` and
`coq_makefile` are in the `PATH`, then the `COQBIN` environment variable
must be set to point to the directory containing such binaries.  For
example:

```
export COQBIN=/home/user/coq/bin/
```

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

## VM Instructions

Please download [the virtual machine]().

If prompted for login information, both the username and password are
"popl" (without quotes).

For your convenience, all necessary software, including Coq 8.6 and
ssreflect have been installed, and a checkout of Disel is present in
`~/disel`.

We recommend checking the proofs using the provided Makefile and
running the two extracted applications.

Checking the proofs can be accomplished by

    cd ~/disel
    make clean; make -j 4

You may see lots of warnings about notations and "nothing to inject";
these are expected.  Success is indicated by the build terminating
without printing "error".

Extracting and running the example applications is described below.

## Code corresponding to the paper

The following describes how [the paper](homes.cs.washington.edu/~jrw12/disel.pdf)
corresponds to the code:

* The Calculator (Section 2)
    - The directory `Examples/Calculator` contains the relevant files.
    - The protocol is defined in `CalculatorProtocol.v`,
      including the state space, coherence predicate, and four transitions
      described in Figure 2. Note that the coherence predicate is stronger than 
      the one given in the paper: it incorporates Inv_1 from Section 2.3. This is
      discussed further below.
    - The program that implements blocking receive of server requests from
      Section 2.2 is defined in `CalculatorServerLib.v`, 
      as `blocking_receive_req`.
    - The simple server from Section 2.3, as well as the batching and memoizing
      servers from Figure 3 are implemented in 
      `SimpleCalculatorServers.v`. They are all implemented in
      terms of the higher-order `server_loop` function. The invariant Inv1 from 
      Section 2.3 is incorporated into the protocol itself, as part of the coherence
      predicate. 
    - The simple client from Section 2.4 is implemented in 
      `CalculatorClientLib.v`. The invariant Inv2 is proved as
      a separate inductive invariant using the WithInv rule in 
      `CalculatorInvariant.v`. It is used to prove the clients
      satisfy their specifications.
    - The delegating server is in `DelegatingCalculatorServer.v`.
      It again uses the invariant Inv2.
    - A runnable example using extraction to OCaml is given in 
      `SimpleCalculatorApp.v`. It consists of one client and two
      servers, one of which delegates to the other. Instructions for how to run
      the example are given below under "Extracting and Running Disel Programs".
* The Logic and its Soundness (Section 3)
    - The definitions from Figure 6 in Section 3.1 are given in `Core/State.v`
      `Core/Protocols.v`, and `Core/Worlds.v`.
    - The primitives of Disel language is defined in `Core/Actions.v`
      (defines send/receive wrappers as in Definitions 3.2 and 3.3).
	- `Core/Process.v`, `Core/Always.v` and `Core/HoareTriples.v`
      define traces, modal predicates (`always` is the formalization
      of post-safety from Definition 3.6). Definition 3.7 from the
      paper corresponds to `has_spec` from `Core/HoareTriples.v`. The
      Theorem 3.8 follows from the soundness of the shallow embedding
      into Coq: any well-typed program has a specification ascribed to it.
    - Inference rules are represented by lemmas named `*_rule` in
      `Core/InferenceRules.v`. For example, `bind_rule` is an
      implementation of `Bind` from Figure 8. 
* Two-Phase Commit and Querying (Section 4)
    - The relevant directory is `Examples/TwoPhaseCommit`.
    - The protocol as described in Section 4.1 is implemented in `TwoPhaseProtocol.v`.
    - The implementations of the coordinator (described in 4.2) and the participant
      are in `TwoPhaseCoordinator.v` and `TwoPhaseParticipant.v`.
    - The strengthened invariant from 4.3 is stated in `TwoPhaseInductiveInv.v` and
      proved to be preserved by all transitions in `TwoPhaseInductiveProof.v`.
    - A runnable example is in `SimpleTPCApp.v`. Instructions for how to run it
      are given below under "Extracting and Running Disel Programs".
    - The querying protocol from Section 4.4 is implemented in the directory
      `Examples/Querying`.

## Exploring further

We encourage you to explore Disel further by extending one of the
examples or trying your own. For example, you could build an application
that uses the calculator to evaluate arithmetic expressions and prove
its correctness. As a more involved example, you could define a new
protocol for leader election in a ring and prove that at most one node
becomes leader.

## Extracting and Running Disel Programs

As described in Section 5.1, Disel programs can be extracted to OCaml and run.
You can build the two examples as follows.

- Run `make CalculatorMain.d.byte` to build the Calculator
  application using `extraction/calculator` as the build directory.
  (Note that all the proofs will be checked as well.) Then run
  `./scripts/calculator.sh` to execute the system in three processes
  on the local machine.

- Run `make TPCMain.d.byte` from the root folder to build the
  Two-Phase Commit application. Then run `./scripts/tpc.sh` to
  execute the system in four processes on the local machine.

## Proof Size Statistics

Section 5.2 and Table 1 describe the size of our development. Those
obtained by using `coqwc` tool on manually dissected files, according
to our vision of what should count as a program, spec or a proof. 
These numbers might slightly differ from reported in the paper due to
the evolution of the project since the last submission.
