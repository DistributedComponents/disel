From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import pred prelude idynamic ordtype finmap pcm unionmap heap coding domain.
Require Import Freshness State EqTypeX Protocols Worlds NetworkSem Rely.
Require Import Actions.
Require Import SeqLib.
Require Import QueryProtocol.
Require Import StatePredicates.

Section QueryHooked.

(* Constructing the composite world *)

Variables (lq : Label) (pc : protocol).
Variable Data : Type.
Variable qnodes : seq nat.
Variable serialize : Data -> seq nat.
Variable deserialize : seq nat -> Data.
Hypothesis ds_inverse : left_inverse serialize deserialize.
Definition pq := QueryProtocol qnodes serialize lq.

Variable core_state_to_data : heap -> option Data.

(* The query hook extracts certain data from the the core protocol *)
(* local state if it's present there. *)
Definition query_hook : hook_type :=
  fun hc hq ms to =>
    if core_state_to_data hc is Some d
    then exists rid, ms = rid :: serialize d
    else True.

Definition query_hookz := (1, (plab pc), (plab pq, tresp)) \\-> query_hook.

Definition W : world := ((plab pc \\-> pc) \+ (plab pq \\-> pq), query_hookz).

Hypothesis Lab_neq: lq != (plab pc).
Hypothesis Nodes_eq: forall d, nodes pc d =i qnodes.

Lemma W_valid : valid W.
Proof.
apply/andP; split=>/=; last by rewrite um_validPt.
case: validUn=>//; rewrite ?um_validPt// =>l.
rewrite !um_domPt !inE=>/eqP=>Z; subst l=>/eqP=>Z.
by subst lq; move/negbTE: Lab_neq; rewrite eqxx.
Qed.

Lemma W_complete : hook_complete W.
Proof.
move=>z lc ls t/=; rewrite um_domPt inE=>/eqP[]_<-<-_.
rewrite !domUn !inE/= !um_domPt !inE !eqxx/= orbC.
by case/andP:W_valid=>->_.
Qed.

Lemma W_dom : dom W.1 =i [:: plab pc; lq].
Proof.
move=>z/=; rewrite domUn !inE/=; case/andP: W_valid=>->/=_. 
by rewrite !um_domPt !inE; rewrite -!(eq_sym z).
Qed.

Lemma prEqQ : (getProtocol W lq) = pq.
Proof.
rewrite /getProtocol/W/= findUnR; last by case/andP: W_valid.
by rewrite um_domPt inE eqxx um_findPt.
Qed.

(* Finished constructing the composite world *)

Variable this : nid.
Hypothesis this_in_qnodes: this \in qnodes.

(* Now playing with the stability of the desired invariant *)

(* Core getters *)
Notation getSc s := (getStatelet s (plab pc)).
Notation getLc s := (getLocal this (getSc s)).
Notation getLc' s n := (getLocal n (getSc s)).

(* Query getters *)
Notation getSq s := (getStatelet s (plab pq)).
Notation getLq s := (getLocal this (getSq s)).

(* Query-specific predicate *)
Definition msg_just_sent d (reqs resp : seq (nid * nat)) req_num to :=
  [/\ getLocal this d = qst :-> (reqs, resp),
   no_msg_from_to to this (dsoup d), 
   (to, req_num) \in reqs & 
   msg_spec this to treq ([:: req_num]) (dsoup d)].

Definition msg_received d (reqs resp : seq (nid * nat)) req_num to :=
  [/\ getLocal this d = qst :-> (reqs, resp),
   (to, req_num) \in reqs,
   no_msg_from_to this to (dsoup d), no_msg_from_to to this (dsoup d) &
   exists (reqs' resp' : seq (nid * nat)),
     getLocal to d = qst :-> (reqs', resp') /\ (this, req_num) \in resp'].

Definition msg_responded d (reqs resp : seq (nid * nat)) req_num to data :=
  [/\ getLocal this d = qst :-> (reqs, resp),
   (to, req_num) \in reqs,
   no_msg_from_to this to (dsoup d) &
   msg_spec to this tresp (req_num :: serialize data) (dsoup d)].

(* Stability of the local state of a core protocol *)
Hypothesis core_state_stable : forall s data s' n,
  network_rely W this s s' ->
  n \in qnodes ->
  core_state_to_data (getLc s) = Some data -> 
  core_state_to_data (getLc' s' n) = Some data.           

(* A rely-inductive predicate describing the message story *)
Definition msg_story s req_num to data :=
  core_state_to_data (getLc s) = Some data /\
  let: d := getSq s in
  exists reqs resp,
  [\/ msg_just_sent d reqs resp req_num to,
   msg_received d reqs resp req_num to |
   msg_responded d reqs resp req_num to data].

Lemma msg_story_step req_num to data z s s' :
  z \in qnodes -> this != z ->
  msg_story s req_num to data ->
  network_step W z s s' ->
  msg_story s' req_num to data.
Proof.
move=> Hz N H S; split=>//.
- case: H=>H _; apply: (core_state_stable s data s')=>//.
  by exists 1, z, s'; split=>//=; split=>//; case/step_coh: S. 
(* TODO: figure out how not to consider transitions in othe worlds *)
case: S; [by case=>_<-; case: H|
 move=>l st H1 to'/= msg n H2 H3 C H4 H5 H6->{s'}|
 move=>l rt H1 i from pf H3 C msg H2/=[H4]H5->{s'}];
 rewrite -(cohD C) W_dom !inE in H3;
 case/orP:H3=>/eqP=>Z; subst l;
 try by rewrite /getStatelet findU (negbTE Lab_neq)/=; case: H. 
(* Okay, now let's deal with interesting cases... *)

(* It's a send-transition *)
set d := getStatelet s lq; move: prEqQ st H1 H2 H4 H5 H6.
rewrite /get_st=>-> st H1 H2 H4 H5 H6.
rewrite /getStatelet findU eqxx/= (cohS C)/=.


admit.
(* It's a receive-transition *)
set d := getStatelet s lq.
move: prEqQ (coh_s lq C) rt pf H1 H2 H4 H5.
rewrite /get_rt=>-> Cq rt pf H1 H2 H4 H5.
rewrite /getStatelet findU eqxx/= (cohS C)/=.


(*

TODO:

1. Finish showing that this property is preseverd by the joined rely;
2. Strengthen the disjuncs, so no spurious messages would be sent
(i.e., that the receiver holds no more response requests from us,
perhaps, this should be a separate auxiliary predicate);

3. Make sure that this is the property we actually need in order to
   verify the composite program; that is, write the program code and
   verify it.

*)


End QueryHooked.

