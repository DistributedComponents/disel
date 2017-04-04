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

Lemma client_not_server n : n \in clients -> (n == server) = false.
Proof.
  move=>H.
  case E: (n == server)=>//.
  move/eqP in E. subst n.
  move: (Hnin).
  by rewrite H.
Qed.

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
  [Pred h | h = st :-> cs].

Definition server_local_coh (ss : server_state) :=
  [Pred h | h = st :-> ss].

Definition local_coh (n : nid) :=
  [Pred h | valid h /\
   if n == server
   then exists ss, server_local_coh ss h
   else n \in clients /\
        exists cs, client_local_coh cs h].

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

Section GetterLemmas.

Lemma getLocal_coh n d (C : LockCoh d):
  n \in nodes ->
  valid (getLocal n d) /\
  if n == server
  then exists (ss : server_state),
      getLocal n d = st :-> ss
  else (n \in clients) /\
       exists (cs : client_state),
           getLocal n d = st :-> cs.
Proof.
  by case: C=>_ _ _ /(_ n)G; rewrite /local_coh/=.
Qed.

Lemma getLocal_server_st_tp d (C : LockCoh d) s:
  find st (getLocal server d) = Some s ->
  idyn_tp s = server_state.
Proof.
have pf: server \in nodes by rewrite inE eqxx.
move: (getLocal_coh C pf); rewrite eqxx; move =>[V][s']Z; rewrite Z in V *.
by rewrite hfindPt -(hvalidPt _ s') V; case=><-.
Qed.

Lemma getLocal_client_st_tp n d (C : LockCoh d) (H : n \in clients) s:
  find st (getLocal n d) = Some s ->
  idyn_tp s = client_state.
Proof.
have pf: n \in nodes by rewrite inE/= orbC H.
move: (getLocal_coh C pf); rewrite H=>[[V]].
rewrite client_not_server//.
move=>[_][cs] L. rewrite L in V *.
rewrite hfindPt -(hvalidPt _ cs) V.
by case=> <-.
Qed.

Definition getSt_server d (C : LockCoh d) : server_state :=
  match find st (getLocal server d) as f return _ = f -> _ with
    Some v => fun epf => icoerce id (idyn_val v) (getLocal_server_st_tp C epf)
  | _ => fun epf => ServerState [::] 0 None
  end (erefl _).

Lemma getSt_server_K d (C : LockCoh d) m :
  getLocal server d = st :-> m -> getSt_server C = m.
Proof.
move=>E; rewrite /getSt_server/=.
have pf: server \in nodes by rewrite inE eqxx.
have V: valid (getLocal server d) by case: (getLocal_coh C pf).
move: (getLocal_server_st_tp C); rewrite !E=>/= H.
by apply: ieqc.
Qed.

End GetterLemmas.

Section ServerGenericSendTransitions.

Definition HCn this to := (this == server /\ to \in clients).

Variable the_tag : nat.

Variable prec : server_state -> nid -> seq nid -> Prop.

Hypothesis prec_safe :
  forall this to s m,
    HCn this to ->
    prec s to m ->
    coh_msg (Msg (TMsg the_tag m) this to true) (current_epoch s).

Notation coh := LockCoh.

Definition server_send_safe (this n : nid)
           (d : dstatelet) (msg : seq nat) :=
  HCn this n /\
  exists (C : coh d), prec (getSt_server C) n msg.

Lemma server_send_safe_coh this to d m : server_send_safe this to d m -> coh d.
Proof. by case=>_[]. Qed.

Lemma server_send_this_in this to : HCn this to -> this \in nodes.
Proof. by case=>/eqP->; rewrite inE eqxx. Qed.

Lemma server_send_to_in this to : HCn this to -> to \in nodes.
Proof. by case=>_; rewrite /nodes inE/= orbC=>->. Qed.

Lemma server_send_safe_in this to d m : server_send_safe this to d m ->
                                  this \in nodes /\ to \in nodes.
Proof.
by case=>[]=>G _; move/server_send_to_in: (G)->; case: G=>/eqP-> _; rewrite inE eqxx.
Qed.


Definition server_step (this to : nid) (d : dstatelet)
           (msg : seq nat)
           (pf : server_send_safe this to d msg) :=
  let C := server_send_safe_coh pf in
  let s := getSt_server C in
  Some (st :-> server_send_step s to).

Lemma soup_coh_post_msg d m:
    soup_coh (dsoup d) -> (exists e, coh_msg m e) -> soup_coh (post_msg (dsoup d) m).1.
Proof.
move=>[H1 H2][y]Cm; split=>[|i ms/=]; first by rewrite valid_fresh.
rewrite findUnL; last by rewrite valid_fresh.
case: ifP=>E; first by move/H2.
by move/um_findPt_inv=>[Z G]; subst i m; exists y.
Qed.

Lemma coh_dom_upd this d s :
  this \in nodes -> coh d -> dom (upd this s (dstate d)) =i nodes.
Proof.
move=>D C z; rewrite -(cohDom C) domU inE/=.
by case: ifP=>///eqP->{z}; rewrite (cohDom C) D; apply: cohVl C.
Qed.

Lemma server_step_coh : s_step_coh_t coh the_tag server_step.
Proof.
move=>this to d msg pf h[]->{h}.
have C : (coh d) by case: pf=>?[].
have E: this = server by case: pf=>[][]/eqP.
split=>/=.
- apply: soup_coh_post_msg; first by case:(server_send_safe_coh pf).
  case: (pf)=>H[C']P/=.
  eexists.
  by apply: (prec_safe _ P).
- by apply: coh_dom_upd=>//; case: (server_send_safe_in pf).
- by rewrite validU; apply: cohVl C.
move=>n Ni. rewrite /local_coh/=.
rewrite /getLocal/=findU; case: ifP=>B; last by case: C=>_ _ _/(_ n Ni).
move/eqP: B=>Z; subst n this; rewrite eqxx (cohVl C)/=.
split.
by rewrite hvalidPt.
by eexists.
Qed.

Lemma server_step_def this to d msg :
      server_send_safe this to d msg <->
      exists b pf, @server_step this to d msg pf = Some b.
Proof.
split=>[pf/=|]; last by case=>?[].
set b := let C := server_send_safe_coh pf in
         let s := getSt_server C in
         st :-> (server_send_step s to).
by exists b, pf.
Qed.

Definition server_send_trans :=
  SendTrans server_send_safe_coh server_send_safe_in server_step_def server_step_coh.

End ServerGenericSendTransitions.

Section ServerSendTransitions.

Definition server_send_grant_prec (ss : server_state) to m :=
  exists rest e,
    ss = ServerState (to :: rest) e None /\
    m = [:: e].

Program Definition cn_send_prep_trans : send_trans LockCoh :=
  @server_send_trans grant_tag server_send_grant_prec _.
Next Obligation.
case: H=>/eqP->H; rewrite /coh_msg eqxx; split=>//=.
case: H0=>[rest] [e] []-> ->/=. by rewrite /msg_from_server /= eqxx.
Qed.

End ServerSendTransitions.

End LockProtocol.
End LockProtocol.
