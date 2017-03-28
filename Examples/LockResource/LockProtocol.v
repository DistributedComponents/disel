From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
Require Import pred prelude idynamic ordtype finmap pcm unionmap heap coding domain.
Require Import Freshness State EqTypeX Protocols Worlds NetworkSem Rely.
Require Import Actions Injection Process Always HoareTriples InferenceRules.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module LockProtocol.
Section LockProtocol.

Variable server : nid.
Variable clients : seq nid.

Hypothesis Hnin : server \notin clients.
Hypothesis Huniq : uniq clients.

Definition nodes := [:: server] ++ clients.

Notation epoch := nat (only parsing).

Record server_state :=
  ServerState {
      outstanding : seq nid;
      current_epoch : epoch;
      current_holder : option nid
    }.

Inductive client_state :=
| NotHeld
| Held of epoch.

Definition acquire_tag := 0.
Definition grant_tag := 1.
Definition release_tag := 2.

Definition msg_from_server ms e :=
  (tag ms == grant_tag) && (tms_cont ms == [:: e]).

Definition msg_from_client ms :=
  ((tag ms == acquire_tag) || (tag ms == release_tag)) &&
  (tms_cont ms == [::]).

Definition coh_msg pkt e :=
  if from pkt == server
  then to pkt \in clients /\ msg_from_server (content pkt) e
  else if from pkt \in clients
  then to pkt == server /\ msg_from_client (content pkt)
  else False.

Definition st := ptr_nat 1.

Definition client_local_coh (cs : client_state) :=
  [Pred h | valid h /\ h = st :-> cs].

Definition server_local_coh (ss : server_state) :=
  [Pred h | valid h /\ h = st :-> ss].

Definition local_coh (n : nid) :=
  [Pred h |
   if n == server
   then exists ss, server_local_coh ss h
   else if n \in clients
   then exists cs, client_local_coh cs h
   else True].


Definition soup_coh : Pred soup :=
  [Pred s |
    valid s /\
    forall m ms, find m s = Some ms -> active ms -> exists e, coh_msg ms e].

Definition state_coh d :=
  forall n, n \in nodes -> local_coh n (getLocal n d).

Definition lock_coh d :=
  let: dl := dstate d in
  let: ds := dsoup d in
  [/\ soup_coh ds
   , dom dl =i nodes
   , valid dl
   & state_coh d].

Lemma l1 d: lock_coh d -> valid (dstate d).
Proof. by case. Qed.

Lemma l2 d: lock_coh d -> valid (dsoup d).
Proof. by case; case. Qed.

Lemma l3 d: lock_coh d -> dom (dstate d) =i nodes.
Proof. by case. Qed.

Definition LockCoh := CohPred (CohPredMixin l1 l2 l3).

Definition server_send_step (ss : server_state) (to : nid) : server_state :=
  if to \in clients
  then if outstanding ss is _ :: out'
       then ServerState out' (S (current_epoch ss)) (Some to)
       else ss
  else ss.

Definition client_send_step (cs : client_state) : client_state :=
  NotHeld. (* ! *)



Definition server_recv_step (ss : server_state) (from : nid)
           (mtag : nat) (mbody : seq nat) : server_state :=
  if mtag == acquire_tag
  then
    ServerState (rcons (outstanding ss) from) (current_epoch ss) (current_holder ss)
  else (* mtag == release_tag *)
    ServerState (outstanding ss) (current_epoch ss) None.


Definition client_recv_step (cs : client_state) (from : nid)
           (mtag : nat) (mbody : seq nat) : client_state :=
  if mbody is [:: e]
  then Held e
  else NotHeld.


End LockProtocol.
End LockProtocol.


