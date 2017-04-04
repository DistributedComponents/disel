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

Module ResourceProtocol.
Section ResourceProtocol.

Variable server : nid.
Variable clients : seq nid.

Hypothesis Hnin : server \notin clients.
Hypothesis Huniq : uniq clients.

Lemma client_not_server n : n \in clients -> (n == server) = false.
Proof.
  move=>H.
  case E: (n == server)=>//.
  move/eqP in E. subst n.
  move: (Hnin).
  by rewrite H.
Qed.

Definition nodes := [:: server] ++ clients.

Lemma client_nodes n : n \in clients -> n \in nodes.
Proof.
  by rewrite inE orbC/= =>->.
Qed.

Notation epoch := nat (only parsing).
Notation client := nid (only parsing).

Definition value := nat.

Inductive request :=
| Update of client * epoch * value
| Read of client * epoch.

Definition request_eq (r1 r2 : request) : bool :=
  match r1, r2 with
  | Update x1, Update x2 => x1 == x2
  | Read x1, Read x2 => x1 == x2
  | _, _ => false
  end.

Lemma request_eqP : Equality.axiom request_eq.
Proof.
  case=>x[]y; do? [by constructor];
  apply: (iffP eqP); congruence.
Qed.

Canonical request_eqMixin := EqMixin request_eqP.
Canonical request_eqType := Eval hnf in EqType request request_eqMixin.

Record server_state :=
  ServerState {
      current_epoch : epoch;
      current_value : value;
      outstanding : seq request
    }.

Definition update_tag := 0.
Definition update_response_tag := 1.
Definition read_tag := 2.
Definition read_response_tag := 3.

Definition msg_from_client ms :=
  (tag ms == update_tag /\ exists e v, tms_cont ms == [:: e; v]) \/
  (tag ms == read_tag /\ exists e, tms_cont ms = [:: e]).

Definition msg_from_server ms :=
  (tag ms == update_response_tag /\ exists e b, tms_cont ms = [:: e; b]) \/
  (tag ms == read_response_tag /\
     ((exists e v, tms_cont ms = [:: e; v] (* success *)) \/
      (exists e, tms_cont ms = [:: e] (* failure *)))).

Definition coh_msg pkt :=
  if from pkt == server
  then to pkt \in clients /\ msg_from_server (content pkt)
  else if from pkt \in clients
  then to pkt == server /\ msg_from_client (content pkt)
  else False.

Definition st := ptr_nat 1.

Definition client_local_coh :=
  [Pred h | h = Heap.empty].

Definition server_local_coh (ss : server_state) :=
  [Pred h | h = st :-> ss].

Definition local_coh (n : nid) :=
  [Pred h | valid h /\
   if n == server
   then exists ss, server_local_coh ss h
   else n \in clients /\
        client_local_coh h].

Definition soup_coh : Pred soup :=
  [Pred s |
    valid s /\
    forall m ms, find m s = Some ms -> active ms -> coh_msg ms].

Definition state_coh d :=
  forall n, n \in nodes -> local_coh n (getLocal n d).

Definition resource_coh d :=
  let: dl := dstate d in
  let: ds := dsoup d in
  [/\ soup_coh ds
   , dom dl =i nodes
   , valid dl
   & state_coh d].

Lemma l1 d: resource_coh d -> valid (dstate d).
Proof. by case. Qed.

Lemma l2 d: resource_coh d -> valid (dsoup d).
Proof. by case; case. Qed.

Lemma l3 d: resource_coh d -> dom (dstate d) =i nodes.
Proof. by case. Qed.

Definition ResourceCoh := CohPred (CohPredMixin l1 l2 l3).

End ResourceProtocol.
End ResourceProtocol.
