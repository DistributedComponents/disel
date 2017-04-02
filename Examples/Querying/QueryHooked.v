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
Require Import Actions Injection Process Always HoareTriples InferenceRules.

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

(* Describing the response-permissions of our recipient *)
Definition holds_res_perms d n (pp : nat -> Prop) :=
  exists (reqs resp : seq (nid * nat)),
    getLocal n d = qst :-> (reqs, resp) /\
    forall rn, (this, rn) \in resp -> pp rn.

(************************************************)
(*            Query-specific predicate          *)
(************************************************)

(* TODO: define the channel criterion *)
Definition request_msg (t: nat) (_ : seq nat) :=  t == treq.
Definition response_msg (t: nat) (_ : seq nat) := t == tresp.

(* 1. We've just sent our stuff. *)
Definition msg_just_sent d (reqs resp : seq (nid * nat)) req_num to :=
  [/\ getLocal this d = qst :-> (reqs, resp),
   no_msg_from_to' to this response_msg (dsoup d), 
   (to, req_num) \in reqs, 
   msg_spec this to treq ([:: req_num]) (dsoup d) &
   holds_res_perms d to (fun _ => false)].

(* 2. Our request is received but not yet responded. *)
Definition msg_received d (reqs resp : seq (nid * nat)) req_num to :=
  [/\ getLocal this d = qst :-> (reqs, resp),
   (to, req_num) \in reqs,
   no_msg_from_to' this to response_msg (dsoup d),
   no_msg_from_to' to this request_msg (dsoup d) &
   holds_res_perms d to (fun rn => rn == req_num)].

(* 3. Our request is responded. *)
Definition msg_responded d (reqs resp : seq (nid * nat)) req_num to data :=
  [/\ getLocal this d = qst :-> (reqs, resp),
   (to, req_num) \in reqs,
   no_msg_from_to' this to response_msg (dsoup d),
   msg_spec to this tresp (req_num :: serialize data) (dsoup d) &
   holds_res_perms d to (fun _ => false)].

(* 4. Stability of the local state of a core protocol, 
      to be proved separately *)
Hypothesis core_state_stable : forall s data s' n,
  network_rely W this s s' ->
  n \in qnodes ->
  core_state_to_data (getLc' s n) = Some data -> 
  core_state_to_data (getLc' s' n) = Some data.           

(***********************************************************)
(* A rely-inductive predicate describing the message story *)
(***********************************************************)
Definition msg_story s req_num to data reqs resp :=
  core_state_to_data (getLc' s to) = Some data /\
  let: d := getSq s in
  [\/ msg_just_sent d reqs resp req_num to,
   msg_received d reqs resp req_num to |
   msg_responded d reqs resp req_num to data].

Lemma msg_story_step req_num to data reqs resp z s s' :
  this != z ->
  msg_story s req_num to data reqs resp ->
  network_step W z s s' ->
  msg_story s' req_num to data reqs resp.
Proof.
move=> N H S; split=>//.
- case: H=>H _; apply: (core_state_stable s data s')=>//.
  by exists 1, z, s'; split=>//=; split=>//; case/step_coh: S. 
(* TODO: figure out how not to consider transitions in othe worlds *)
(* case: S; [by case=>_<-; case: H| *)
(*  move=>l st H1 to'/= msg n H2 H3 C H4 H5 H6->{s'}| *)
(*  move=>l rt H1 i from pf H3 C msg H2/=[H4]H5->{s'}]; *)
(*  rewrite -(cohD C) W_dom !inE in H3; *)
(*  case/orP:H3=>/eqP=>Z; subst l; *)
(*  try by rewrite /getStatelet findU (negbTE Lab_neq)/=; case: H.  *)
(* Okay, now let's deal with interesting cases... *)

(* It's a send-transition *)
(* set d := getStatelet s lq; move: prEqQ st H1 H2 H4 H5 H6. *)
(* rewrite /get_st=>-> st H1/= H2 H4 H5 H6. *)
(* rewrite /getStatelet findU eqxx/= (cohS C)/=. *)
(* case: H1; [move|case=>//]; move=>Z; subst st. *)
(* - admit. (* Boring transition *) *)
(* - case B: ((z == to) && (to' == this)). *)
(*   case/andP:B=>/eqP Z/eqP Z'; subst z to'. *)
(*   case: H=>G1 G2. *)
(*   case:G2; [by admit | | by admit]. *)

(*   rewrite /all_hooks_fire/query_hookz/query_hook in H5.  *)
  

(* admit. *)
(* admit. *)

(* (* It's a receive-transition *) *)
(* set d := getStatelet s lq. *)
(* move: prEqQ (coh_s lq C) rt pf H1 H2 H4 H5. *)
(* rewrite /get_rt=>-> Cq rt pf H1 H2 H4 H5. *)
(* rewrite /getStatelet findU eqxx/= (cohS C)/=. *)
(* case: H1; [move|case=>//]; move=>Z; subst rt. *)

Admitted.


(* Send-wrapper for requesting data *)

Program Definition send_req rid to :=
  act (@send_action_wrapper W pq this (plab pq) prEqQ
                            (qsend_req qnodes) _ [:: rid] to).
Next Obligation. by rewrite !InE; left. Qed.

Program Definition send_req_act (rid : nat) (to : nid) :
  {rrd : seq (nid * nat) * seq (nid * nat) * Data}, DHT [this, W]
   (fun i =>
      let: (reqs, resp, data) := rrd in 
      [/\ getLq i = qst :-> (reqs, resp),
       no_msg_from_to' to this response_msg (dsoup (getSq i)),
       to \in qnodes,
       rid = fresh_id reqs &
       core_state_to_data (getLc' i to) = Some data],
   fun (r : seq nat) m => 
     let: (reqs, resp, data) := rrd in 
     [/\ getLq m = qst :-> ((to, rid) :: reqs, resp),
     r = [:: rid] &
     msg_story m rid to data ((to, rid) :: reqs) resp])
  := Do (send_req rid to).
Next Obligation.
apply: ghC=>s0[[reqs resp] d]/=[P1]P2 P3 P4 P5 C0.
apply: act_rule=>i1 R0; split=>//=[|r i2 i3[Hs]St R2].
(* Precondition *)
- rewrite /Actions.send_act_safe/=.
  move/rely_coh: (R0)=>[_ C1]; rewrite -(rely_loc' _ R0) in P1.
  move: (coh_coh lq C1); rewrite prEqQ=>Cq1; 
  split=>//;[split=>//| | ].
  + by exists Cq1; rewrite /QueryProtocol.send_req_prec (getStK _ P1)/= P4.
  + by apply/andP; split=>//; rewrite -(cohD C1) W_dom !inE eqxx orbC.
  move=>z lc hk; rewrite find_um_filt eqxx /query_hookz/==>/sym.
  by move/find_some; rewrite um_domPt !inE=>/eqP. 
(* Postcondition *)
have N: network_step W this i1 i2.
- apply: (Actions.send_act_step_sem _ _ St)=>//; first by rewrite prEqQ.
  by rewrite !InE; left.
rewrite (rely_loc' _ R2).
rewrite -(rely_loc' _ R0) in P1.
move/rely_coh: (R0)=>[_]C1; move: (coh_coh lq C1);rewrite prEqQ=>Cq1.
case: St=>->[h]/=[].
rewrite/QueryProtocol.send_step/QueryProtocol.send_step_fun/=.
rewrite (proof_irrelevance (QueryProtocol.send_safe_coh _) Cq1).
rewrite (getStK _ P1); case=>Z Z'; subst h rid.
rewrite Z' locE; last first.
- by apply: cohVl Cq1.
- by apply: cohS C1.
- by rewrite -(cohD C1) W_dom !inE eqxx orbC//.
split=>//; constructor 1.
- suff E: core_state_to_data (getLc' i1 to) = core_state_to_data (getLc' i2 to).
  + move: (core_state_stable _ _ _ _ R0 P3 P5).
    by rewrite E; move/(core_state_stable _ _ _ _ R2 P3).
  case B: (to == this); [move/eqP:B=>Z; subst to | ]; last first.
  + by rewrite /getLocal (step_is_local _ N)=>//; move/negbT: B.
  
    
    Check .
    
    move/(core_state_stable _ _ _ _ R2 P3).
Check  P5

Search _ (getLocal) (getStatelet).
  

(* TODO: finish the proof for this action *)




(*

TODO (in arbitrary order):

0. Refine no_msg_from_to for specific tags, otherwise the invariant 
   doesn't hold.

1. Finish showing that this property is preseverd by the joined rely;

2. Make sure that this is the property we actually need in order to
   verify the composite program; that is, write the program code and
   verify it.

3. Check that core_state_stable indeed holds just like this in 2PC 
   inductive invariant.

4. Define the generic procedure and make sure that the injection rule 
   works as it should with respect to the core protocol!!!

*)


End QueryHooked.

