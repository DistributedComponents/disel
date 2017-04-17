From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import pred prelude idynamic ordtype finmap pcm unionmap heap coding domain.
Require Import Freshness State EqTypeX Protocols Worlds NetworkSem Rely.
Require Import Actions.
Require Import SeqLib.
Require Import StatePredicates.
Require Import Actions Injection Process Always HoareTriples InferenceRules.

Require Import LockProtocol.

Module L := LockProtocol.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section LockInductiveInvariant.

Variable (l : Label).
Variable (server : nid) (clients : seq nid).
Hypothesis server_not_client : server \notin clients.

Definition no_active_msg_tokens : Pred soup :=
  [Pred s | valid s /\
            forall m ms, find m s = Some ms -> active ms -> tag (content ms) == L.acquire_tag].

Definition ClientHolds_coh d e c :=
  [/\ L.client_local_coh (L.Held e) (getLocal c d),
     (forall c', c' \in clients -> c' != c -> L.client_local_coh L.NotHeld (getLocal c' d)) &
     no_active_msg_tokens (dsoup d) ].

Definition ServerHolds_coh d :=
  (forall c, c \in clients -> L.client_local_coh L.NotHeld (getLocal c d)) /\
  no_active_msg_tokens (dsoup d).

(*
Definition Granting_coh d :=
  (forall c, c \in clients -> client_local_coh NotHeld (getLocal c d)) /\
*)
End LockInductiveInvariant.