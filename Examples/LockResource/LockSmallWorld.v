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

Module LockSmallWorld.
Section LockSmallWorld.

Variable (l : Label).
Variable (server : nid) (clients : seq nid).
Hypothesis server_not_client : server \notin clients.

Variable this : nid.
Hypothesis this_in_clients : this \in clients.

Lemma this_not_server :
  server != this.
Proof.
  case X: (server == this)=>//.
  move/eqP in X.
  move: (this_in_clients) (server_not_client).
  by rewrite X=>->.
Qed.

Notation protocol := (LockProtocol server_not_client l).

Definition W : world := (l \\-> protocol, Unit).

Lemma W_valid : valid W.
Proof. by apply /andP; split=>//=; rewrite um_validPt. Qed.

Lemma W_complete : hook_complete W.
Proof. by move=>z lc ls t/=; rewrite dom0. Qed.

Lemma W_dom : dom W.1 =i [:: l].
Proof. by move=>z/=; rewrite um_domPt !inE eq_sym. Qed.

Lemma W_l : getProtocol W l = protocol.
Proof. by rewrite /getProtocol/W/= um_findPt. Qed.

Notation assert_local this x d := (getLocal this d = L.st :-> x).

Lemma assert_local_rely A (x : A) s1 s2 :
  network_rely W this s1 s2 ->
  assert_local this x (getStatelet s1 l) ->
  assert_local this x (getStatelet s2 l).
Proof. by move=>Rely12; rewrite (rely_loc' _ Rely12). Qed.

Lemma held_rely e s1 s2 :
  network_rely W this s1 s2 ->
  L.held this e (getStatelet s1 l) ->
  L.held this e (getStatelet s2 l).
Proof. exact: assert_local_rely. Qed.

Lemma not_held_rely s1 s2 :
  network_rely W this s1 s2 ->
  L.not_held this (getStatelet s1 l) ->
  L.not_held this (getStatelet s2 l).
Proof. exact: assert_local_rely. Qed.

End LockSmallWorld.
Module Exports.
Definition held_rely := held_rely.
Definition not_held_rely := not_held_rely.
End Exports.
End LockSmallWorld.

Export LockSmallWorld.Exports.

