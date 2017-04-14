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

Require Import LockProtocol ResourceProtocol LockSmallWorld LockPrograms.

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
  (1, lock_label, (resource_label, R.update_tag)) \\-> resource_hook.

Definition W : world :=
  ((lock_label \\-> lock_protocol) \+ (resource_label \\-> resource_protocol),
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
  W = (lock_label \\-> lock_protocol, Unit) \+
      (resource_label \\-> resource_protocol, Unit) \+
      (Unit, resource_hooks).
Proof. by rewrite /PCM.join/=/W !unitL !unitR. Qed.

Lemma injW : injects (lock_label \\-> lock_protocol, Unit) W resource_hooks.
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

Lemma injWQ : inj_ext injW = (resource_label \\-> resource_protocol, Unit).
Proof.
move: (W_valid)=>V; move: (cohK injW).
rewrite {1}eqW/mkWorld/= -!joinA /PCM.join/= in V.
case/andP: V=>/=V V'.
rewrite {1}eqW/mkWorld/= -!joinA /PCM.join/=; case=>H K.
case: (um_cancel V H)=>_; rewrite !unitR=>_{H}H1.
rewrite [inj_ext _]surjective_pairing -H1{H1}; congr (_, _).
rewrite !unitL joinC/=/resource_hooks/= in V' K.
rewrite -[_ \\-> _]unitR in V'.
have Z:  (1, lock_label, (resource_label, R.update_tag)) \\-> resource_hook \+ Unit =
         (1, lock_label, (resource_label, R.update_tag)) \\-> resource_hook \+ (inj_ext injW).2
  by rewrite unitR.
by case: (um_cancel V' Z).
Qed.

Lemma W_resource_protocol : getProtocol W resource_label = resource_protocol.
Proof.
  rewrite /getProtocol/W/= findUnR; last by case/andP: W_valid.
  by rewrite um_domPt inE eqxx um_findPt.
Qed.

Variable this : nid.
Hypothesis this_in_lock_clients: this \in lock_clients.
Hypothesis this_in_resource_clients: this \in resource_clients.

Notation getSL s := (getStatelet s lock_label).
Notation getLL s := (getLocal this (getSL s)).

Notation getSR s := (getStatelet s resource_label).
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

Definition resource_init_state d :=
  [/\ no_outstanding_updates d,
     no_msg_from_to this resource_server (dsoup d) &
     no_msg_from_to resource_server this (dsoup d)].

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

(* TODO: state all of the following lemmas in the approprate small world. *)

Lemma no_outstanding_updates_rely s1 s2 :
  network_rely W this s1 s2 ->
  no_msg_from_to this resource_server (dsoup (getSR s1)) ->
  no_outstanding_updates (getSR s1) ->
  no_outstanding_updates (getSR s2).
Admitted.

Lemma resource_init_state_rely_small s1 s2 :
  network_rely (resource_label \\-> resource_protocol, Unit) this s1 s2 ->
  resource_init_state (getSR s1) ->
  resource_init_state (getSR s2).
Admitted.

(* TODO: Get this by framing the previous lemma. *)
Lemma resource_init_state_rely s1 s2 :
  network_rely W this s1 s2 ->
  resource_init_state (getSR s1) ->
  resource_init_state (getSR s2).
Admitted.

Lemma update_in_flight_rely e v s1 s2 :
  network_rely W this s1 s2 ->
  L.held this e (getSL s1) ->
  update_in_flight e v (getSR s1) ->
  update_in_flight e v (getSR s2).
Admitted.

Lemma resource_value_rely e v s1 s2 :
  network_rely W this s1 s2 ->
  L.held this e (getSL s1) ->
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
    (fun i => resource_init_state (getSR i) /\ L.held this e (getSL i),
     fun r m => update_in_flight e v (getSR m) /\ L.held this e (getSL m))
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
have Held2: L.held this e (getSL s2).
- move: Held0.
  rewrite /L.held -(rely_loc' _ Rely01).
  case: Step=>_ [h'][]_ s2def.
  by rewrite s2def /getStatelet findU/= (negbTE lock_resource_label_neq).
split; last first.
- by move: Held2; rewrite /L.held (rely_loc' _ Rely23).
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
    if res is Some v0
    then [/\ v0 = v,
            resource_init_state (getSR s),
            L.held this e (getSL s) &
            resource_value v (getSR s)]
    else update_in_flight e v (getSR s) /\ L.held this e (getSL s).

Lemma recv_update_response_inv_lock_held e v u r s :
  recv_update_response_inv e v u r s ->
  L.held this e (getSL s).
Proof. by case: r=>[a|][]. Qed.

Lemma recv_update_response_inv_rely e v u r s1 s2 :
  network_rely W this s1 s2 ->
  recv_update_response_inv e v u r s1 ->
  recv_update_response_inv e v u r s2.
Admitted.

(* TODO: would be nice to get this from SmallWorld.held_rely. *)
Lemma lock_held_rely e s1 s2 :
  network_rely W this s1 s2 ->
  L.held this e (getSL s1) ->
  L.held this e (getSL s2).
Proof. by move=>Rely12; rewrite /L.held (rely_loc' _ Rely12). Qed.

Require Import While.

Definition is_res_v (res : option nat) (v : nat) : bool :=
  res == Some v.

Program Definition recv_update_response_loop e v :
  DHT [this, W]
    (fun i => update_in_flight e v (getSR i) /\ L.held this e (getSL i),
     fun res m => [/\ resource_init_state (getSR m),
                  L.held this e (getSL m),
                  resource_value v (getSR m) &
                  is_res_v res v]) :=
  Do (@while this W _ _ (fun x => if x is Some _ then false else true)
               (recv_update_response_inv e v) _
               (fun _ => Do _ (
                 r <-- tryrecv_update_response ;
                 if r is Some (from, tag, [:: e0; v0; b0]) return _
                 then ret _ _ (Some v0)
                 else ret _ _ None)) None).

Next Obligation. by eauto using recv_update_response_inv_rely. Defined.
Next Obligation.
move=>s0 /=[[]][]. case: H=>[r|_ Inv0]; first done.
apply: step; apply: act_rule=> s1 Rely01/=; split; first by case: (rely_coh Rely01).
move=>y s2 s3 [_]/= Step12 Rely23.
case: y Step12=>[|Step12]; last first.
- apply: ret_rule=>s4 Rely34[][_] [Flight0] Held0.
  move/Actions.tryrecv_act_step_none_equal_state in Step12. subst s2.
  split.
  + eauto 10 using update_in_flight_rely, lock_held_rely.
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
have Rely24 := rely_trans Rely23 Rely34. move =>{s3}{Rely23}{Rely34}.
rewrite /recv_update_response_inv.
have: update_in_flight e v (getStatelet s1 resource_label)
  by eauto using update_in_flight_rely.
case; do? by move=>[]_ _ /(_ _ _ _ Fm).
move=>[]NM1 NO1[b]MS1.
move: (MS1)=>[_] /(_ _ _ _ Fm) /andP[/eqP ? /eqP Ec]. subst t c.
case: Ec=>???. subst e0 v0 b0.
move=>RV1.
have Held1 := lock_held_rely Rely01 Held0.
have Held2 : L.held this e (getSL s2)
  by move: Held1;rewrite s2def/getStatelet findU (negbTE lock_resource_label_neq).
split=>//; first last.
- apply /(resource_value_rely Rely24 Held2)=>//.
  move: RV1.
  rewrite /resource_value. subst s2.
  rewrite /getStatelet findU eqxx/= (cohS C1).
  by rewrite /getLocal findU (negbTE this_not_resource_server) /=.
- by exact: lock_held_rely Rely24 Held2.
apply /(resource_init_state_rely Rely24).
rewrite s2def /getStatelet findU eqxx/= (cohS C1).
split.
- move: NO1.
  rewrite /no_outstanding_updates/resource_perms.
  by rewrite /getLocal/= findU (negbTE this_not_resource_server) /=.
- move: NM1.
  rewrite /no_outstanding_updates/resource_perms.
  by apply/no_msg_from_to_consume.
fold (getStatelet s1 resource_label).
move=>/=.
exact: (msg_spec_consume _ Fm MS1).
Qed.
Next Obligation.
move=>s/=[Init Held].
apply: call_rule'; cbn; first by move=>_; exists tt; split=>//.
move=>r s' /(_ tt (conj Init Held))[].
by case: r=>//=r _[]; split=>//; subst r.
Qed.

Notation lock_quiescent := (lock_quiescent lock_server this).

Program Definition update_rpc e v :
  DHT [this, W]
    (fun i => resource_init_state (getSR i) /\ L.held this e (getSL i),
     fun (res : unit) m =>
       [/\ resource_init_state (getSR m),
          L.held this e (getSL m) &
          resource_value v (getSR m)])
    := Do (send_update e v ;;
           recv_update_response_loop e v ;;
           ret _ _ tt).
Next Obligation.
move=>s0/=[Init0 Held0].
apply: step; apply: call_rule=>// _ s1 [Flight1 Held1] C1.
apply: step; apply: call_rule=>// r s2 [Init2 Held2 Val2 Res] C2.
apply: ret_rule=>s3 Rely23 _.
have Held3 := lock_held_rely Rely23 Held2.
split=>//.
exact: (resource_init_state_rely Rely23).
exact: (resource_value_rely Rely23 Held2).
Qed.

Program Definition lock_and_update (v : nat) :
  DHT [this, W]
    (fun i => [/\ lock_quiescent (getSL i),
              L.not_held this (getSL i) &
              resource_init_state (getSR i)],
     fun (e : nat) m =>
       [/\ resource_init_state (getSR m),
          L.held this e (getSL m) &
          resource_value v (getSR m)])
  := Do (e <-- inject injW (lock_rpc lock_label lock_server_not_client this_in_lock_clients);
         update_rpc e v ;; 
         ret _ _ e).
Next Obligation.
move=>s0/= [LQ0 LNH0 RI0] C0.
apply: step=>//.

move: (C0)=>CD0; rewrite eqW in CD0; move: (coh_hooks CD0)=>{CD0}CD0.
case: (coh_split CD0); try apply: hook_complete0.
move=>l0[r0][Cl0 Cr0] E0.
subst s0; apply: inject_rule=>//.

have ESL0: getSL (l0 \+ r0) = getSL l0
  by rewrite (locProjL CD0 _ Cl0)// gen_domPt inE andbC eqxx.
rewrite ESL0{ESL0} in LQ0 LNH0 *.
apply: call_rule; first done.
move=>e l1[LQ1 LH1] Cl1 r1 C1 Rely_r01.

have ESR0: getSR (l0 \+ r0) = getSR r0
  by rewrite (locProjR CD0 _ Cr0)// gen_domPt inE andbC eqxx.
rewrite ESR0{ESR0} in RI0 *.

move: (C1)=>CD1; rewrite eqW in CD1; move: (coh_hooks CD1)=>{CD1}CD1.
have Cr1 := (cohUnKR CD1 Cl1 (@hook_complete0 _)).

apply: step. apply: call_rule.
- rewrite injWQ in Rely_r01.
  have ESL1: getSL (l1 \+ r1) = getSL l1
    by rewrite (locProjL CD1 _ Cl1)// gen_domPt inE andbC eqxx.
  have ESR1: getSR (l1 \+ r1) = getSR r1
    by rewrite (locProjR CD1 _ Cr1)// gen_domPt inE andbC eqxx.
  rewrite ESL1 ESR1.
  move=> _.
  split=>//.
  by apply /(resource_init_state_rely_small Rely_r01).
move=>_ s2 [Init2 Held2 Val2] C2.
apply: ret_rule=>s3 Rely23 _.
split.
exact: (resource_init_state_rely Rely23).
exact: (lock_held_rely Rely23).
exact: (resource_value_rely Rely23 Held2).
Qed.

(* TODO *)

(* Prove stability lemmas. *)

(* The stability of (the strengthened) `update_response_sent` will require a
   nontrivial coherence fact about the lock protocol, basically amounting to
   mutual exclusion and stability of the server's state when a client holds the
   lock. *)

End LockResourceHooked.
