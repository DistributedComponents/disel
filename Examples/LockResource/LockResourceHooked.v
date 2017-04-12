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

Require Import LockProtocol ResourceProtocol.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

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

Lemma plab_lockE : plab lock_protocol = lock_label.
Proof. done. Qed.

Lemma plab_resourceE : plab resource_protocol = resource_label.
Proof. done. Qed.


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

(* Intermediate Assertions *)

Definition resource_perms d (p : seq R.request -> Prop) :=
  exists s : R.server_state,
    getLocal resource_server d = R.st :-> s /\
    p (R.outstanding s).

Definition resource_value v d :=
  exists s : R.server_state,
    getLocal resource_server d = R.st :-> s /\
    R.current_value s = v.

Definition no_outstanding_updates d :=
  resource_perms d (fun out => forall n e v, R.Update (n, e, v) \in out -> n != this).

Definition outstanding_update e v d :=
  resource_perms d (fun out => (forall e' v', R.Update (this, e', v') \in out -> e' = e /\ v' = v) /\
                            count_mem (R.Update (this, e, v)) out = 1).

Definition is_update_msg (t : nat) (_ : seq nat) := t == R.update_tag.
Definition is_update_response_msg (t : nat) (_ : seq nat) := t == R.update_response_tag.

Definition resource_init_state s :=
  [/\ no_outstanding_updates (getSR s),
     no_msg_from_to this resource_server (dsoup (getSR s)) &
     no_msg_from_to resource_server this (dsoup (getSR s))].

Definition lock_held e s :=
  getLL s = L.st :-> L.Held e.

Definition update_just_sent e v d :=
  [/\ msg_spec this resource_server R.update_tag [:: e; v] (dsoup d),
     no_outstanding_updates d &
     no_msg_from_to resource_server this (dsoup d)].

Definition update_at_server e v d :=
  [/\ no_msg_from_to this resource_server (dsoup d),
     outstanding_update e v d &
     no_msg_from_to resource_server this (dsoup d)].

Definition update_response_sent e v d :=
  [/\ no_msg_from_to this resource_server (dsoup d),
     no_outstanding_updates d,
     exists b : nat, msg_spec resource_server this R.update_response_tag [:: e; v; b] (dsoup d) &
     resource_value v d].

Definition update_in_flight e v d :=
  [\/ update_just_sent e v d,
     update_at_server e v d |
     update_response_sent e v d].

(* Stability Lemmas *)
Lemma resource_init_state_rely s1 s2 :
  network_rely W this s1 s2 ->
  resource_init_state s1 ->
  resource_init_state s2.
Admitted.

Lemma update_in_flight_rely e v s1 s2 :
  network_rely W this s1 s2 ->
  update_in_flight e v (getSR s1) ->
  update_in_flight e v (getSR s2).
Admitted.

Lemma lock_held_rely e s1 s2 :
  network_rely W this s1 s2 ->
  lock_held e s1 ->
  lock_held e s2.
Proof. by move=>Rely12; rewrite /lock_held (rely_loc' _ Rely12). Qed.

Lemma resource_value_rely e v s1 s2 :
  lock_held e s1 ->
  network_rely W this s1 s2 ->
  resource_value v (getSR s1) ->
  resource_value v (getSR s2).
Admitted.

(* Resource Programs *)

Program Definition send_update_act e v :=
  act (@send_action_wrapper W resource_protocol this resource_label W_resource_protocol
        (R.client_send_update_trans resource_server_not_client)
        _
        [:: e; v]
        resource_server).
Next Obligation.
by rewrite !InE; right; right; left.
Qed.

Lemma this_not_resource_server :
  resource_server != this.
Proof.
  case X: (resource_server == this)=>//.
  move/eqP in X.
  move: (this_in_resource_clients) (resource_server_not_client).
  rewrite X=>H. by rewrite H.
Qed.

Program Definition send_update e v :
  DHT [this, W]
    (fun i => resource_init_state i /\ lock_held e i,
     fun r m => update_in_flight e v (getSR m) /\ lock_held e m)
  := Do (send_update_act e v).
Next Obligation.
move=>s0/=[Init0][Held0].
apply: act_rule=>s1 Rely01; split=>//=.
(* precondition: *)
- rewrite /Actions.send_act_safe/=.
  move/rely_coh: (Rely01)=> [_ C1].
  move: (coh_coh resource_label C1); rewrite W_resource_protocol=> Cr1.
  split=>//; [split=>//; try by case: Init0 | | ].
  + by rewrite /R.client_send_update_prec; eexists _, _.
  + apply/andP; split=>//=; first by rewrite -(cohD C1) W_dom !inE eqxx orbC.
    by rewrite inE this_in_resource_clients orbC.
  (* now show hook fires: *)
  move=>z lc hk; rewrite find_um_filt eqxx /resource_hooks /= =>/sym.
  move/um_findPt_inv=>[][]??? _ _; subst z lc hk.
  by rewrite (rely_loc' _ Rely01); exists e.

(* postcondition: *)
move=>m s2 s3 [Safe] Step Rely23 _.
have Held2: lock_held e s2.
- move: Held0.
  rewrite /lock_held -(rely_loc' _ Rely01).
  case: Step=>_ [h'][]_ s2def.
  by rewrite s2def /getStatelet findU/= (negbTE lock_resource_label_neq).
split; last first.
- by move: Held2; rewrite /lock_held (rely_loc' _ Rely23).
apply/(update_in_flight_rely Rely23)=>//.
constructor 1.
move: (resource_init_state_rely Rely01 Init0).
rewrite /update_just_sent/resource_init_state=>-[]Out1 From1 To1.
case: Step=>_[] h' [] _ s2def.
have C1 := (rely_coh Rely01).2.
have CR1 := (coh_coh resource_label C1).
rewrite s2def /getStatelet findU eqxx/= (cohS C1) /= getsE;
    last by rewrite -(cohD C1) W_dom !inE/= eqxx orbC.
split.
- apply /msg_specE=>//.
  by apply /(cohVs CR1).
- move: Out1.
  rewrite /no_outstanding_updates/resource_perms.
  by rewrite /getLocal/= findU (negbTE this_not_resource_server).
apply /no_msg_from_toE'=>//.
by apply /(cohVs CR1).
by rewrite eq_sym; apply/negbTE/this_not_resource_server.
Qed.

Program Definition tryrecv_update_response :=
  act (@tryrecv_action_wrapper W this
      (fun l from tag m => [&& l == resource_label, from == resource_server &
                            tag == R.update_response_tag]) _).
Next Obligation.
case/andP: H=>/eqP->_.
rewrite joinC domUn inE um_domPt inE eqxx andbC/=.
case: validUn=>//=; rewrite ?um_validPt//.
move=>k; rewrite !um_domPt !inE=>/eqP<-/eqP H.
move: (lock_resource_label_neq).
by rewrite H eqxx.
Qed.

Definition recv_update_response_inv e v (_ : unit) : cont (option nat) :=
  fun res s =>
    if res is Some v
    then [/\ resource_init_state s,
            lock_held e s &
            resource_value v (getSR s)]
    else update_in_flight e v (getSR s) /\ lock_held e s.

Lemma recv_update_response_inv_rely e v u r s1 s2 :
  network_rely W this s1 s2 ->
  recv_update_response_inv e v u r s1 ->
  recv_update_response_inv e v u r s2.
Admitted.

(* TODO: move this into Core/Actions.v *)
Lemma tryrecv_act_step_none_equal_state W0 this0 p s1 s2 :
    Actions.tryrecv_act_step W0 this0 p s1 s2 None ->
    s1 = s2.
Proof.
  case=>[C1][[] | [l][m][tms][from][rt][pf][]]; done.
Qed.

Require Import While.

Program Definition recv_update_response_loop e v :
  DHT [this, W]
    (fun i => resource_init_state i /\ lock_held e i,
     fun res m => [/\ resource_init_state m,
                  lock_held e m,
                  resource_value v (getSR m) &
                  if res is Some r then r = v else False]) :=
  Do _ (@while this W _ _ (fun x => if x is Some _ then false else true)
               (recv_update_response_inv e v) _
               (fun _ => Do _ (
                 r <-- tryrecv_update_response ;
                 if r is Some (from, tag, [:: e0; v0; b0]) return _
                 then ret _ _ (Some v0)
                 else ret _ _ None)) None).
Next Obligation. by apply: with_spec x. Qed.
Next Obligation. by eauto using recv_update_response_inv_rely. Qed.
Next Obligation. move=>s0 /=[[]][]. case: H=>[r|_ Inv0]; first done.
apply: step; apply: act_rule=> s1 Rely01/=; split; first by case: (rely_coh Rely01).
move=>y s2 s3 [_]/= Step12 Rely23.
case: y Step12=>[|Step12]; last first.
- apply: ret_rule=>s4 Rely34[][_] [Flight0] Held0.
  move/tryrecv_act_step_none_equal_state in Step12. subst s2.
  split.
  + by eauto using update_in_flight_rely.
  by eauto using lock_held_rely.
move=>[[from]]tag body Step12.
move: Step12=>[C1][[]|[l][m][[t c]][from0][rt][pf][[]]/esym Fm Hrt HT Wf]; first done.
move=>/andP[/eqP ?] /andP[/eqP ?] /eqP HT' /= s2def [? ? ?]. subst l from0 from body tag.
move: (coh_coh resource_label C1).
rewrite W_resource_protocol/==>-[][Vs1]Sp1 _ _ _.
move: (Sp1 _ _ Fm erefl).
rewrite /R.coh_msg/= eqxx/R.msg_from_server HT HT'.
rewrite /eq_op/= => -[] _ [[_][e0][v0][b0] E|[]]; last done.
rewrite E.
apply: ret_rule=>s4 Rely34[][_][Flight0] Held0.
rewrite /recv_update_response_inv.
have: update_in_flight e v (getStatelet s1 resource_label)
  by eauto using update_in_flight_rely.
case; do? by move=>[]_ _ /(_ _ _ _ Fm).
move=>[]NM1 NO1[b]MS1.
move: MS1=>[_] /(_ _ _ _ Fm) /andP[/eqP ? /eqP Ec]. subst t c.
case: Ec=>???. subst e0 v0 b0.
move=>RV1.
have Held1 := lock_held_rely Rely01 Held0.
have Held2 : lock_held e s2 by admit.
have Held3 :=  lock_held_rely Rely23 Held2.
split; first last.
- apply /(resource_value_rely Held3)=>//.
  apply /(resource_value_rely Held2)=>//.
  move: RV1.
  rewrite /resource_value. subst s2.
  rewrite /getStatelet plab_resourceE findU eqxx/= (cohS C1).
  by rewrite /getLocal findU (negbTE this_not_resource_server) /=.
- by exact: lock_held_rely Rely34 Held3.
Admitted.

(* TODO *)

(* Write program to receive update response and prove postcondition that
   guarantees update has occurred. *)

(* That postcondition will require a strengthened joint coherence fact about
   epoch numbers toprove "noninterference", namely that that all update messages
   in the network have strictly smaller epochs than the lock server. *)

(* That postcondition will also require strengthening `update_response_sent` to
   assert that the update actually occurred. *)

(* Prove stability lemmas. *)

(* The stability of (the strengthened) `update_response_sent` will require a
   nontrivial coherence fact about the lock protocol, basically amounting to
   mutual exclusion and stability of the server's state when a client holds the
   lock. *)

End LockResourceHooked.
