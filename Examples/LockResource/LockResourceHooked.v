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

End LockResourceHooked.
