From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import pred prelude idynamic ordtype finmap pcm unionmap heap coding domain.
Require Import Freshness State EqTypeX Protocols Worlds NetworkSem Rely.
Require Import Actions.
Require Import SeqLib.
Require Import NewStatePredicates.
Require Import Actions Injection Process Always HoareTriples InferenceRules.

Require Import LockProtocol ResourceProtocol.

Module L := LockProtocol.
Module R := ResourceProtocol.

Section LockResourceHooked.

Variable (lock_label : Label).
Variable (lock_server : nid) (lock_clients : seq nid).
Hypothesis lock_server_not_client : lock_server \notin lock_clients.

Definition lock_protocol := LockProtocol lock_server_not_client lock_label.

Variable (resource_label : Label).
Variable (resource_server : nid) (resource_clients : seq nid).
Hypothesis resource_server_not_client : resource_server \notin resource_clients.

Definition resource_protocol := ResourceProtocol resource_server_not_client resource_label.

Hypothesis lock_resource_label_neq : lock_label != resource_label.

Lemma lock_resource_plab_neq : plab lock_protocol != plab resource_protocol.
Proof. done. Qed.

Definition resource_hook : hook_type :=
  fun hl hr m to =>
    exists e, hl = L.st :-> L.Held e.

Definition resource_hooks :=
  (1, plab lock_protocol, (plab resource_protocol, R.update_tag)) \\-> resource_hook.

Definition W : world :=
  ((plab lock_protocol \\-> lock_protocol) \+ (plab resource_protocol \\-> resource_protocol),
   resource_hooks).

Lemma W_valid : valid W.
Proof.
apply /andP; split=>/=; last by rewrite um_validPt.
case: validUn=>//; rewrite ?um_validPt// =>l.
rewrite !um_domPt !inE=>/eqP=>Z; subst l=>/eqP=>Z.
by move/negbTE: lock_resource_label_neq; rewrite Z eqxx.
Qed.

Lemma W_complete : hook_complete W.
Proof.
move=>z lc ls t/=; rewrite um_domPt inE=>/eqP[]_<-<-_.
rewrite !domUn !inE/= !um_domPt !inE !eqxx/= orbC.
by case/andP:W_valid=>->_.
Qed.

Lemma W_dom : dom W.1 =i [:: plab lock_protocol; plab resource_protocol].
Proof.
move=>z/=; rewrite domUn !inE/=; case/andP: W_valid=>->/=_. 
by rewrite !um_domPt !inE; rewrite -!(eq_sym z).
Qed.

Lemma eqW : 
  W = (plab lock_protocol \\-> lock_protocol, Unit) \+
      (plab resource_protocol \\-> resource_protocol, Unit) \+
      (Unit, resource_hooks).
Proof. by rewrite /PCM.join/=/W !unitL !unitR. Qed.

Lemma injW : injects (plab lock_protocol \\-> lock_protocol, Unit) W resource_hooks.
Proof.
rewrite eqW.
apply: injectL.
- by rewrite -eqW W_valid.
- by move=>????; rewrite dom0 inE.
- by move=>????; rewrite dom0 inE.
- move=>z lc ls t. rewrite um_domPt inE.
  case/eqP=>_ <- <- _.
  rewrite !domUn !inE !um_domPt !inE !eqxx/=.
  by case/andP:W_valid=>/=->_/=; rewrite orbC.
move=>l; rewrite um_domPt inE=>/eqP=><-.
move=>z lc ls t; rewrite um_domPt inE=>/eqP[]_ _<-_.  
apply/negbT; apply/eqP=>/=Z. move/negbTE: lock_resource_label_neq.
by rewrite Z eqxx.
Qed.

Lemma W_resource_protocol : getProtocol W resource_label = resource_protocol.
Proof.
  rewrite /getProtocol/W/= findUnR; last by case/andP: W_valid.
  by rewrite um_domPt inE eqxx um_findPt.
Qed.

Variable this : nid.
Hypothesis this_in_lock_clients: this \in lock_clients.
Hypothesis this_in_resource_clients: this \in resource_clients.

Notation getSL s := (getStatelet s (plab lock_protocol)).
Notation getLL s := (getLocal this (getSL s)).

Notation getSR s := (getStatelet s (plab resource_protocol)).
Notation getLR s := (getLocal resource_server (getSR s)).

Definition resource_perms d (p : seq R.request -> Prop) :=
  exists s : R.server_state,
    getLocal resource_server d = R.st :-> s /\
    p (R.outstanding s).

Definition no_outstanding_updates d :=
  resource_perms d (fun out => forall n e v, R.Update (n, e, v) \in out -> n != this).

Definition outstanding_update e v d :=
  resource_perms d (fun out => (forall e' v', R.Update (this, e', v') \in out -> e' = e /\ v' = v) /\
                            count_mem (R.Update (this, e, v)) out = 1).

Definition is_update_msg (t : nat) (_ : seq nat) := t == R.update_tag.
Definition is_update_response_msg (t : nat) (_ : seq nat) := t == R.update_response_tag.

Definition resource_init_state s :=
  [/\ no_outstanding_updates (getSR s),
     no_msg_from_to' this resource_server is_update_msg (dsoup (getSR s)) &
     no_msg_from_to' resource_server this is_update_response_msg (dsoup (getSR s))].

Definition lock_held e s :=
  getLL s = L.st :-> L.Held e.

Definition update_just_sent e v d :=
  [/\ msg_spec' this resource_server R.update_tag [:: e; v] (dsoup d),
     no_outstanding_updates d &
     no_msg_from_to' resource_server this is_update_response_msg (dsoup d)].

Definition update_at_server e v d :=
  [/\ no_msg_from_to' this resource_server is_update_msg (dsoup d),
     outstanding_update e v d &
     no_msg_from_to' resource_server this is_update_response_msg (dsoup d)].

Definition update_response_sent e v d :=
  [/\ no_msg_from_to' this resource_server is_update_msg (dsoup d),
     no_outstanding_updates d &
     exists b : nat, msg_spec' this resource_server R.update_response_tag [:: e; v; b] (dsoup d)].

Definition update_in_flight e v d :=
  [\/ update_just_sent e v d,
     update_at_server e v d |
     update_response_sent e v d].
End LockResourceHooked.
