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
  [Pred h | h = st :-> (d.1, CInit) \+ log :-> d.2].

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
rewrite -(rely_loc' _ R) in L.
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

Notation loc_qry s := (getLocal cn (getStatelet s lq)).
Notation loc_tpc' s n := (getLocal n (getStatelet s lc)).
Notation loc_tpc s := (loc_tpc' s cn).
Notation qry_init := (query_init_state lq Data qnodes serialize cn).

Lemma loc_imp_core s d n :
  Coh W s -> n \in qnodes -> local_indicator d (loc_tpc s) ->
  core_state_to_data (loc_tpc' s n) d.
Proof.
move=>C Nq E.
case/orP: Nq=>[|P]; first by move/eqP=>z; subst n; exists _, CInit. 
case: (C)=>_ _ _ _/(_ lc); rewrite prEqC//=; case=> C2 Inv.
move: (@cn_agree lc cn pts [::] Hnin (getStatelet s lc) d.1 d.2 n C2 E Inv P)=>->.
by eexists _, _.
Qed.

Lemma find_empty l i : l \notin dom i -> getStatelet i l = empty_dstatelet.
Proof. by rewrite /getStatelet; case: dom_find=>//->. Qed.
       

Definition cn_request_log :=
  request_data_program _ pc _ _ _ _ ds_inverse _ Lab_neq _ cn_in_qnodes
                       local_indicator core_state_stable_step (0, [::]).

(* Coordinator loop *)
Definition coordinator ds :=
  with_inv (TwoPhaseInductiveProof.ii _ _ _)
           (coordinator_loop_zero lc cn pts [::] Hnin Puniq PtsNonEmpty ds).

  
(****************************************************************)
(*************   Overall program combining the two  *************)
(****************************************************************)

(* The following program first initiates a series  of TPC rounds as a *)
(* coordinator, and then, on behalf of the coordinator queries a *)
(* particular pariticipant via the side protocol for querying. The *)
(* goal is to show that the resul obtained from querying is coherent *)
(* with respect to coordinator's state. *)

Program Definition coordinate_and_query (ds : seq data) to :
  {rr : seq (nid * nat) * seq (nid * nat)}, DHT [cn, W]
  (fun i =>
      let: (reqs, resp) := rr in 
     [/\ loc_tpc i = st :-> (0, CInit) \+ log :-> ([::] : seq (bool * data)),
        to \in qnodes,
        loc_qry i = qst :-> (reqs, resp) &
        qry_init to i],
   fun (res : Data) m =>
     let: (reqs, resp) := rr in
     exists (chs : seq bool),
       let: d := (size ds, seq.zip chs ds) in
       [/\ loc_tpc m = st :-> (d.1, CInit) \+ log :-> d.2,
        loc_qry m = qst :-> (reqs, resp),
        qry_init to m &
        res = d]) 
  := Do _ (
      iinject (coordinator ds);;    
      cn_request_log to).

Next Obligation.
by exact : (query_hookz lq pc Data qnodes serialize core_state_to_data).
Defined.

Next Obligation.
exact: (injW lq pc Data qnodes serialize core_state_to_data Lab_neq).
Defined.

Next Obligation.
apply:ghC=>i0[rq rs][P1 P2 P3 P4]C0; apply: step.
(*Preparing to split the state. *)
move: (C0)=>CD0; rewrite /W eqW in CD0; move: (coh_hooks CD0)=>{CD0}CD0.
case: (coh_split CD0 (hook_complete0 _) (hook_complete0 _))=>i1[j1][C1 D1 Z].
subst i0; apply: inject_rule=>//.
have E : loc_tpc (i1 \+ j1) = loc_tpc i1 by rewrite (locProjL CD0 _ C1)// gen_domPt inE andbC eqxx.
rewrite E{E} in P1.
apply: with_inv_rule'. 
apply: call_rule=>//_ i2 [chs]L2 C2 Inv j2 CD2/= R.
(* Massaging the complementary state *)
have E : loc_qry (i1 \+ j1) = loc_qry j1 by rewrite (locProjR CD0 _ D1)// gen_domPt inE andbC eqxx.
rewrite E {E} -(rely_loc' _ R) in P3.
case: (rely_coh R)=>_ D2.
rewrite /W eqW in CD2; move: (coh_hooks CD2)=>{CD2}CD2.
rewrite /mkWorld/= in C2.
have C2': i2 \In Coh (plab pc \\-> pc, Unit).
- split=>//=.
  + by rewrite /valid/= valid_unit um_validPt.
  + by apply: (cohS C2).
  + by apply: hook_complete0.  
  + by move=>z; rewrite -(cohD C2) !um_domPt.
  move=>l; case B: (lc == l).
  + move/eqP:B=>B; subst l; rewrite /getProtocol um_findPt; split=>//.
    by move: (coh_coh lc C2); rewrite /getProtocol um_findPt.
  have X: l \notin dom i2 by rewrite -(cohD C2) um_domPt inE; move/negbT: B.
  rewrite /getProtocol/= (find_empty _ _ X).
  have Y: l \notin dom (lc \\-> pc) by rewrite um_domPt inE; move/negbT: B.
  by case: dom_find Y=>//->_. 
have D2': j2 \In Coh (lq \\-> pq lq Data qnodes serialize, Unit)
    by apply: (cohUnKR CD2 _ (hook_complete0 _)).

rewrite -(locProjL CD2 _ C2') in L2; last by rewrite um_domPt inE eqxx.
rewrite -(locProjR CD2 _ D2') in P3; last by rewrite um_domPt inE eqxx.
clear C2 D2.

(* So what's important is for the precondition ofattachment to be *)
(* independent of the core protocol. *)  
rewrite injWQ in R.
rewrite /query_init_state/= in P4.
rewrite (locProjR CD0 _ D1) in P4; last by rewrite um_domPt inE eqxx.
have Q4: qry_init to j2.
- by apply: (query_init_rely' _ pc _ _ _ _ ds_inverse
                              core_state_to_data Lab_neq cn cn_in_qnodes _ _ _ P4 R).
clear P4.
rewrite /query_init_state/= -(locProjR CD2 _ D2') in Q4; last by rewrite um_domPt inE eqxx.

(* Now ready to use the spec for querying. *)
apply (gh_ex (g:=(rq, rs, (size ds, seq.zip chs ds)))).
apply: call_rule=>//=; last by move=>d m[->->T1 T2->]_; eexists _. 
move=>CD2'; split=>//.
case/orP: P2=>[|P]; first by move/eqP=>Z; subst to; exists _, CInit. 
exists _, PInit; rewrite !(locProjL CD2 _ C2') in L2 *; last by rewrite um_domPt inE eqxx.
move: (coh_coh lc C2'); rewrite prEq; case=>C3 _.
by apply: (@cn_agree lc cn pts [::] Hnin _ _ _ to C3 _ Inv).
Qed.

End QueryPlusTPC.
