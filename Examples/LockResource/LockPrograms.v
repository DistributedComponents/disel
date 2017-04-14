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

Definition lock_quiescent d :=
  [/\ no_pending_acquires d,
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

Lemma lock_quiescent_rely s1 s2 :
  network_rely W this s1 s2 ->
  lock_quiescent (getStatelet s1 l) ->
  lock_quiescent (getStatelet s2 l).
Admitted.

Lemma lock_request_in_flight_rely s1 s2 :
  network_rely W this s1 s2 ->
  lock_request_in_flight (getStatelet s1 l) ->
  lock_request_in_flight (getStatelet s2 l).
Admitted.

Program Definition send_acquire :
  DHT [this, W]
    (fun i => lock_quiescent (getStatelet i l) /\ L.not_held this (getStatelet i l),
     fun r m => lock_request_in_flight (getStatelet m l))
  := Do send_acquire_act.
Next Obligation.
move=>s0/= [Qui0 NH0].
apply: act_rule=>s1 Rely01; split=>/=.
- rewrite /Actions.send_act_safe/=.
  move/rely_coh: (Rely01)=> [_ C1].
  move: (coh_coh l C1); rewrite LSW.W_l/==>Cs1.
  split=>//; [split=>// | | ].
  + rewrite /L.client_send_acquire_prec.
    have HC: L.HClient server clients this server by [].
    exists HC, Cs1.
    rewrite (L.getSt_client_K(m:=L.NotHeld) _ Cs1 _ this_in_clients)//.
    by move: Qui0=>[] H; rewrite (not_held_rely Rely01)//.
  + apply/andP; split=>//=; first by rewrite -(cohD C1) LSW.W_dom !inE eqxx.
    by rewrite inE this_in_clients orbC.
  by move=>z lc hk; rewrite find_um_filt eqxx find0E.
move=>m s2 s3 [Safe] Step Rely23 _.
apply /(lock_request_in_flight_rely Rely23).
constructor 1.
move: (lock_quiescent_rely Rely01 Qui0).
rewrite /lock_quiescent/acquire_sent=>-[NP1 NM1 NM'1].
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

Program Definition tryrecv_grant :=
  act (@tryrecv_action_wrapper W this
      (fun l0 from tag m => [&& l0 == l, from == server &
                            tag == L.grant_tag]) _).
Next Obligation.
case/andP: H=>/eqP->_.
by rewrite um_domPt inE eqxx.
Qed.

Definition recv_grant_inv (_ : unit) : cont (option nat) :=
  fun res s =>
    if res is Some e
    then lock_quiescent (getStatelet s l) /\
         L.held this e (getStatelet s l)
    else lock_request_in_flight (getStatelet s l).

Lemma recv_grant_inv_rely u r s1 s2 :
  network_rely W this s1 s2 ->
  recv_grant_inv u r s1 ->
  recv_grant_inv u r s2.
Admitted.

Require Import While.

Program Definition recv_grant_loop :
  DHT [this, W]
    (fun i => lock_request_in_flight (getStatelet i l),
     fun res m => lock_quiescent (getStatelet m l) /\
               if res is Some e
               then L.held this e (getStatelet m l)
               else False) :=
  Do _ (@while this W _ _ (fun x => if x is Some _ return bool then false else true)
               (recv_grant_inv) _
               (fun _ => Do _ (
                 r <-- tryrecv_grant ;
                 if r is Some (from, tag, [:: e]) return _
                 then ret _ _ (Some e)
                 else ret _ _ None)) None).
Next Obligation. by apply: with_spec x. Defined.
Next Obligation. by eauto using recv_grant_inv_rely. Defined.
Next Obligation.
move=>s0 /=[[]][]. case: H=>[r|_ Inv0]; first done.
apply: step; apply: act_rule=> s1 Rely01/=; split; first by case: (rely_coh Rely01).
move=>y s2 s3 [_]/= Step12 Rely23.
case: y Step12=>[|Step12]; last first.
- apply: ret_rule=>s4 Rely34[][_] Flight0/=.
  move/Actions.tryrecv_act_step_none_equal_state in Step12. subst s2.
  eauto using lock_request_in_flight_rely.
move=>[[from]]tag body Step12.
move: Step12=>[C1][[]|[l0][m][[t c]][from0][rt][pf][[]]/esym Fm Hrt HT Wf]; first done.
move=>/andP[/eqP ?] /andP[/eqP ?] /eqP HT' /= s2def [? ? ?]. subst l0 from0 from body tag.
move: (coh_s l C1) rt Hrt HT HT' Wf pf s2def.
rewrite LSW.W_l/=.
move=> Cs1' rt Hrt HT HT' Wf pf s2def.
move: (coh_coh l C1).
have Cs1 := (coh_coh l C1).
rewrite LSW.W_l/==>-[][Vs1]Sp1 _ _ _.
move: (Sp1 _ _ Fm erefl).
rewrite /L.coh_msg/= eqxx/L.msg_from_server HT HT' =>-[e][_]/=/eqP ?. subst c.
apply: ret_rule=>s4 Rely34[][_] Flight0.
have Rely24 := rely_trans Rely23 Rely34. move =>{s3}{Rely23}{Rely34}.
rewrite /recv_grant_inv.
have: lock_request_in_flight (getStatelet s1 l)
  by eauto using lock_request_in_flight_rely.

case; do? by move=>[]_ _ _ /(_ _ _ _ Fm).
move=>[]NH1 NM1 NP1[e0]MS1.
move: (MS1)=>[_] /(_ _ _ _ Fm) /andP[/eqP Et /eqP Ec]. subst t.
case: Ec=>?. subst e0.

move: (Hrt) Et.
rewrite /L.lock_receives !InE.
case; first by move=>->/=.
case; first by move=>->/=.
move=>?. subst rt.
move=>/= _.

split; last first.
- apply /(LSW.held_rely Rely24).
  rewrite s2def/getStatelet findU eqxx/= (cohS C1).
  rewrite /L.held/getLocal/= findU eqxx/= (cohVl Cs1).
  by rewrite /L.rc_step this_in_clients /L.client_recv_step.
apply /(lock_quiescent_rely Rely24).
rewrite s2def /getStatelet findU eqxx/= (cohS C1).
split.
- move: NP1.
  rewrite /no_pending_acquires/acquire_perms.
  by rewrite /getLocal/= findU (negbTE this_not_server) /=.
- exact: (no_msg_from_to_consume _ NM1).
move=>/=.
exact: (msg_spec_consume _ Fm MS1).
Qed.
Next Obligation.
move=>s/= Inv.
apply: call_rule'; cbn; first by move=>_; exists tt.
move=>r s' /(_ tt Inv)[].
by case: r=>//r _[]; split.
Qed.

Program Definition lock_rpc :
  DHT [this, W]
    (fun i => lock_quiescent (getStatelet i l) /\ L.not_held this (getStatelet i l),
     fun (res : nat) m =>
       lock_quiescent (getStatelet m l) /\
       L.held this res (getStatelet m l))
    := Do (send_acquire ;;
           r <-- recv_grant_loop ;
           ret _ _ (if r is Some e then e else 0)).
Next Obligation.
move=>s0/=[Qui0 NH0].
apply: step; apply: call_rule; first done.
move=>_ s1 Flight1 C1.
apply: step; apply: call_rule; first done.
move=>r s2 [Qui2].
case: r; last done.
move=> e Held2 C2.
apply: ret_rule=>s3 Rely23 _.
split.
- exact: (lock_quiescent_rely Rely23).
exact: (held_rely Rely23).
Qed.

End LockPrograms.