From mathcomp.ssreflect 
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
Require Import pred prelude idynamic ordtype finmap pcm unionmap heap coding.
Require Import Freshness State EqTypeX DepMaps Protocols Worlds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* Operational semantics of the network *)

Section NetworkSemantics.

Variable w : world.
Variable this: nid.

Notation gets := (getStatelet).
Notation getp := (@getProtocol w).

(* Getters for transitions *)

Definition get_coh l := @coh (getp l).
Definition get_st l := @snd_trans (getp l).
Definition get_rt l := @rcv_trans (getp l).

Lemma getsE l s : l \in dom s -> find l s = Some (gets s l).
Proof.
move=>D. rewrite /gets; case f: (find l s)=>[v|]=>//.
by move: (find_none f); move/negbTE; rewrite D.
Qed.

Lemma coh_s l s: Coh w s -> coh (getp l) (gets s l).
Proof. by case=>_ _ _ /(_ l). Qed.

Lemma Coh_dom l s : l \in dom s -> Coh w s -> 
                          dom (dstate (gets s l)) =i nodes (getp l) (gets s l).
Proof. by move=>D; case=>W V E /(_ l); apply:cohDom. Qed.

(*  Semantics of the network in the presence of some world *)
(* Defining small-step semantics of the network *)
Inductive network_step (s1 s2 : state) : Prop :=
  (* Do nothing *)
  Idle of s1 \In Coh w /\ s1 = s2

  (* Send message *)
| SendMsg (* Pick a world, send transition and a recipient *)
          l st (_ : st \In @get_st l) to msg b
          (pf: this \in (nodes (getp l) (gets s1 l)))
          (pf' : l \in dom s1) (C: Coh w s1)
          
          (* It's safe to send *)
          (S : send_safe st this to (gets s1 l) msg)
          
          (spf : Some b = send_step S) of
          
          (* Generate the message and the new local state *)
          let: d :=  gets s1 l in

          (* Update the soup and local state *)
          let: f' := upd this b (dstate d) in
          let: s' := (post_msg (dsoup d) (Msg (TMsg (t_snd st) msg)
                                              this to true)).1 in
          s2 = upd l (DStatelet f' s') s1

| ReceiveMsg l rt (_ : rt \In @get_rt l) i from
             (* Pick a world, receive transition and a message *)
             (pf: this \in (nodes (getp l)) (gets s1 l))
             (pf': l \in ddom w) (C: Coh w s1)
             (msg : TaggedMessage)
             (pf': tag msg = t_rcv rt) of
             let: d := (gets s1 l) in
             let: f := dstate d in
             let: s := dsoup d  in

             [/\ find i s = Some (Msg msg from this true),
              msg_wf rt (coh_s l C) this from msg &
              (* The semantics doesn't execute unsafe receive-transitions *)
              let loc' := receive_step rt from msg (coh_s l C) pf in
              let: f' := upd this loc' f in
              let: s'' := consume_msg s i in
              s2 = upd l (DStatelet f' s'') s1].


(* First important result: network stepping preserves overall coherence.

   Intuitively, this follows from the fact that the transitions
   preserve coherence.  *)

Lemma step_coh s1 s2: network_step s1 s2 ->
                      Coh w s1 /\ Coh w s2.
Proof.
case=>[[H1 <-] | l st _ to a loc' pf D C S Spf ->/= |
       l rt _ i from pf D C H1 msg [H3 H4->/=]]//; split=>//.
- case: (C)=>W V E H; split=>//; first by rewrite validU/= V.
  + move=>z; rewrite domU/= !inE V.
    by case b:  (z == l)=>//; move/eqP: b=>?; subst; rewrite E D.
  move=>k; case b: (k == l); rewrite /gets findU b/=; last by apply: H.
  rewrite V/=; move/eqP: b=>Z; subst k=>/=.
  case: st a S Spf => /= t_snd ssafe G1 G2 sstep Y G3 a S Spf.
  have X: exists b pf, sstep this to (gets s1 l) a pf = Some b by exists loc', S.
  move/Y: X=>X; move: (G1 _ _ _ _ X) (G2 _ _ _ _ X)=>{G1 G2}G1 G2; apply: G3. 
  rewrite /gets in Spf; rewrite Spf; move: (coh_s l C)=>G1'.
  by rewrite -(proof_irrelevance S X). 
case: (C)=>W V E H; split=>//; first by rewrite validU/= V.
- move=>z; rewrite domU/= !inE V.
  by case b:  (z == l)=>//; move/eqP: b=>?; subst; rewrite D.
move=>k; case b: (k == l); rewrite /gets findU b/=; last by apply: H.    
move: (coh_s l (And4 W V E H))=>G1.
rewrite V; move/eqP: b=>Z; subst k=>/=; rewrite E in D.
have pf' : this \in dom (dstate (gets s1 l))
  by move: (pf); rewrite -(Coh_dom D C).
case: rt H1 H3 msg H4=>/= r_rcvwf mwf rstep G msg T F M.
rewrite -(proof_irrelevance (H l) (coh_s l C)) in M.
move: (G (gets s1 l) from this i (H l) pf msg pf' T M F); rewrite /gets.
by move: (H l)=>G1'; rewrite -(proof_irrelevance G1 G1'). 
Qed.  

(* Stepping preserves the protocol structure *)
Lemma step_preserves_labels s1 s2 :
  network_step s1 s2 -> dom s1 =i dom s2.
Proof.
by move/step_coh=>[[_ _ E1 _] [_ _ E2 _]]z; rewrite -E1 -E2.
Qed.

(* Stepping only changes the local state of "this" node, 
   in any of the protocols. *)

Lemma step_is_local s1 s2 l: network_step s1 s2 ->
  forall z, z != this ->
  find z (dstate (gets s1 l)) = find z (dstate (gets s2 l)).
Proof.
move=>S z N; case: S; first by case=>_ Z; subst s2.
- move=>k st ? to a b pf D C S Spf Z; subst s2; case B: (l == k); 
          rewrite /gets findU B //= (cohS C)/=.
  by move/negbTE: N; rewrite findU=>->/=; move/eqP: B=>->. 
move=>k rt ? i from H1 H2 C msg T/= [H3 H4]Z; subst s2.
case B: (l == k); rewrite /gets findU B //= (cohS C)/=.  
by move/negbTE: N; rewrite findU=>->/=; move/eqP: B=>->.
Qed.

Lemma stepV1 s1 s2: network_step s1 s2 -> valid s1.
Proof. by case/step_coh=>/cohS. Qed.

Lemma stepV2 s1 s2: network_step s1 s2 -> valid s2.
Proof. by case/step_coh=>_ /cohS. Qed.


(* 
   Network steps do not allocate/deallocate nodes 
   (although this might change soon)
 *)
Lemma step_preserves_node_ids s1 s2 l:
  l \in dom s1 -> network_step s1 s2 ->
  dom (dstate (gets s1 l)) =i dom (dstate (gets s2 l)).
Proof.
move=>D S; case: (S); first by case=>C<-.
- move=> l' st H to msg b H1 H2 C _ _ Z; subst s2.
  rewrite /gets findU; case B: (l == l')=>//=; rewrite (stepV1 S)/==>n.
  move/eqP: B=>B; subst l'; rewrite domU/= !inE; case B: (n == this)=>//.
  move/eqP:B=>B; subst n; rewrite -(Coh_dom D C) in H1; rewrite H1.
  by case: C=>_ _ _/(_ l)/cohVl->. 
move=>l' rt _ m from H1 D' C msg E[F]W/=Z; subst s2.  
rewrite /gets findU; case B: (l == l')=>//=; rewrite (stepV1 S)/==>n.
move/eqP: B=>B; subst l'; rewrite domU/= !inE; case B: (n == this)=>//.
move/eqP:B=>B; subst n; clear S; rewrite -(Coh_dom D C) in H1; rewrite H1.
by case: (C)=>_ _ _/(_ l)/cohVl->. 
Qed.

End NetworkSemantics.



