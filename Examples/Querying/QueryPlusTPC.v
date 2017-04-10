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
Require Import TwoPhaseProtocol TwoPhaseCoordinator TwoPhaseParticipant.
Require TwoPhaseInductiveProof.
Require Import QueryProtocol QueryHooked.

Section QueryPlusTPC.

(* Querying on behalf of the coordinator (it's easier this way, thanks *)
(* to cn_agreement lemma). In order to query on behald of the *)
(* participan, a different invariant-based fact should be proven. *)

(****************************************************************)
(*************         Basic definitions       ******************)
(****************************************************************)

Variables (lc lq : Label).
Variables (cn : nid) (pts : seq nid).
Hypothesis Lab_neq: lq != lc.
Hypothesis Hnin : cn \notin pts.
Hypothesis Puniq : uniq pts.
Hypothesis PtsNonEmpty : pts != [::].

(* Core protocol *)
Definition pc : protocol := TwoPhaseInductiveProof.tpc_with_inv lc [::] Hnin.
Definition Data : Type := (nat * Log).
Definition qnodes := cn :: pts.

(* Serialization of logs *)
Variable serialize : Data -> seq nat.
Variable deserialize : seq nat -> Data.
Hypothesis ds_inverse : left_inverse serialize deserialize.

(* This one is in the init state *)
Definition local_indicator (d : Data) :=
  [Pred h | exists (r : nat) (l : Log), h = st :-> (d.1, CInit) \+ log :-> d.2].

(* Data is just a log *)
Definition core_state_to_data h (d : Data)  :=
  exists T (s : T), h = st :-> (d.1, s) \+ log :-> d.2.

Lemma cn_in_qnodes : cn \in qnodes.
Proof. by rewrite inE eqxx. Qed.

Notation getLc s n := (getLocal n (getStatelet s lc)).
Notation cn_agree := TwoPhaseInductiveInv.cn_log_agreement.

(****************************************************************)
(*************   Necessary properties of TPC   ******************)
(****************************************************************)

Lemma core_state_stable_step z s d s' n :
  cn != z -> network_step (mkWorld pc) z s s' ->
  n \in qnodes ->
  local_indicator d (getLc s cn) ->
  core_state_to_data (getLc s n) d  -> 
  core_state_to_data (getLc s' n) d.
Proof.
move=>N S Qn L H0; case: (step_coh S)=>C1 C2.
have R: network_rely (plab pc \\-> pc, Unit) cn s s' by exists 1, z, s'. 
rewrite -(rely_loc' _ R) in L; case: L=>r[lg]L.
case: C2=>V1 V2 _ D /(_ lc)/=; rewrite prEq=>/=[[C2] Inv].
case/orP: Qn=>[|P]; first by move/eqP=>Z; subst n; exists _, CInit. 
move: (@cn_agree lc cn pts [::] Hnin (getStatelet s' lc) d.1 d.2 n C2 L Inv P)=>H. 
by exists _, PInit.
Qed.

(* Lemma core_data_injective h d d' : *)
(*   valid h -> *)
(*   core_state_to_data h d  ->  *)
(*   core_state_to_data h d' -> *)
(*   d = d'. *)
(* Proof. *)
(* case=>V [T1][t1]E1[T2][t2]E2. *)
(* rewrite E1 in V E2. *)
(* move: (hcancelT V E2).  *)

(***************  Intermediate definitions **********************)

(* Composite world *)
Definition W := QueryHooked.W lq pc Data qnodes serialize core_state_to_data.

Definition cn_request_log :=
  request_data_program _ pc _ _ _ _ ds_inverse _ Lab_neq _ cn_in_qnodes
                       local_indicator core_state_stable_step.

(* Coordinator loop *)
Definition coordinator ds :=
  coordinator_loop_zero lc cn pts [::] Hnin Puniq PtsNonEmpty ds.

(* TODO: finish this *)


(****************************************************************)
(*************   Overall program combining the two  *************)
(****************************************************************)

Program Definition 


(* TODO *)

End QueryPlusTPC.
