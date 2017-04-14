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

Require Import LockProtocol LockSmallWorld.

Module L := LockProtocol.
Module LSW := LockSmallWorld.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section LockPrograms.

Variable (l : Label).
Variable (server : nid) (clients : seq nid).
Hypothesis server_not_client : server \notin clients.

Variable this : nid.
Hypothesis this_in_clients : this \in clients.

Notation this_not_server := (LSW.this_not_server server_not_client this_in_clients).

Notation protocol := (LockProtocol server_not_client l).
Notation W := (@LSW.W l server clients server_not_client).

Program Definition send_acquire_act :=
  act (@send_action_wrapper W protocol this l _
        (L.client_send_acquire_trans server_not_client)
        _
        [::]
        server).
Next Obligation. by rewrite /getProtocol/W/= um_findPt. Qed.
Next Obligation. by rewrite !InE; right; left. Qed.

Definition acquire_perms (p : seq nid -> Prop) d :=
  exists s : L.server_state,
    getLocal server d = L.st :-> s /\
    p (L.outstanding s).

Definition no_pending_acquires :=
  acquire_perms (fun out => this \notin out).

Definition lock_init_state d :=
  [/\ L.not_held this d,
     no_pending_acquires d,
     no_msg_from_to this server (dsoup d) &
     no_msg_from_to server this (dsoup d)].

Definition acquire_sent d :=
  [/\ L.not_held this d,
     msg_spec this server L.acquire_tag [::] (dsoup d),
     no_pending_acquires d &
     no_msg_from_to server this (dsoup d)].

Definition outstanding_acquire :=
  acquire_perms (fun out => count_mem this out = 1).

Definition acquire_pending d :=
  [/\ L.not_held this d,
     no_msg_from_to this server (dsoup d),
     outstanding_acquire d &
     no_msg_from_to server this (dsoup d)].

Definition grant_sent d :=
  [/\ L.not_held this d,
     no_msg_from_to this server (dsoup d),
     no_pending_acquires d &
     exists e, msg_spec server this L.grant_tag [:: e] (dsoup d)].

Definition lock_request_in_flight d :=
  [\/ acquire_sent d,
     acquire_pending d |
     grant_sent d].

Lemma lock_init_state_rely s1 s2 :
  network_rely W this s1 s2 ->
  lock_init_state (getStatelet s1 l) ->
  lock_init_state (getStatelet s2 l).
Admitted.

Lemma lock_request_in_flight_rely s1 s2 :
  network_rely W this s1 s2 ->
  lock_request_in_flight (getStatelet s1 l) ->
  lock_request_in_flight (getStatelet s2 l).
Admitted.

Program Definition send_acquire :
  DHT [this, W]
    (fun i => lock_init_state (getStatelet i l),
     fun r m => lock_request_in_flight (getStatelet m l))
  := Do send_acquire_act.
Next Obligation.
move=>s0/= Init0.
apply: act_rule=>s1 Rely01; split=>/=.
- rewrite /Actions.send_act_safe/=.
  move/rely_coh: (Rely01)=> [_ C1].
  move: (coh_coh l C1); rewrite LSW.W_l/==>Cs1.
  split=>//; [split=>// | | ].
  + rewrite /L.client_send_acquire_prec.
    have HC: L.HClient server clients this server by [].
    exists HC, Cs1.
    rewrite (L.getSt_client_K(m:=L.NotHeld) _ Cs1 _ this_in_clients)//.
    by move: Init0=>[] H; rewrite (not_held_rely Rely01)//.
  + apply/andP; split=>//=; first by rewrite -(cohD C1) LSW.W_dom !inE eqxx.
    by rewrite inE this_in_clients orbC.
  by move=>z lc hk; rewrite find_um_filt eqxx find0E.
move=>m s2 s3 [Safe] Step Rely23 _.
apply /(lock_request_in_flight_rely Rely23).
constructor 1.
move: (lock_init_state_rely Rely01 Init0).
rewrite /lock_init_state/acquire_sent=>-[NH1 NP1 NM1 NM'1].
case: Step=>_/=[h'][h'def]s2def.
have C1 := (rely_coh Rely01).2.
have Cs1 := (coh_coh l C1).
rewrite s2def /getStatelet findU eqxx/= (cohS C1) /= getsE;
  last by rewrite -(cohD C1) LSW.W_dom !inE/= eqxx.
split.
- rewrite /L.not_held/getLocal/= findU eqxx/= (cohVl Cs1).
  by move: h'def; rewrite /L.client_step/L.client_send_step=>-[].
- apply /msg_specE=>//.
  by apply /(cohVs Cs1).
- move: NP1.
  rewrite /no_pending_acquires/acquire_perms.
  by rewrite /getLocal/= findU (negbTE this_not_server).
apply /no_msg_from_toE'=>//.
by apply /(cohVs Cs1).
by rewrite eq_sym; apply/negbTE/this_not_server.
Qed.

End LockPrograms.