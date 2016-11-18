From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
Require Import pred prelude idynamic ordtype finmap pcm unionmap heap coding.
Require Import Freshness State EqTypeX DepMaps Protocols Worlds NetworkSem.
Require Import heaptac stmod stsep stlog stlogR.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* "Atomic" send/receive actions, coherent with the network semantics *)

Definition getLocal (n : nid) (d : dstatelet) : heap :=
  match find n (dstate d) with
  | Some h => h
  | None => Unit
  end.

Module Actions.
Section Actions.

Variable nodes : seq nid.
Variable p : protocol nodes.
Variable I : heap -> heap -> Prop.
Variable precPf : forall d, precise (I d).

(* Print precise. *)

(* An "atmoic" action is parametrized by a return type and a
   sequential specification. The componens are as follows:

  * e      -- the sequential "carrier" of the atomic command
  * a_safe -- safety predicate wrt. the protocol
  * a_step -- the transition predicate

  Axioms:

  * safe_coh  -- safety implies coherence;
  * safe_inv  -- safety + precondition -> invariant;
  * safe_step -- can make an abstract step;
  * step_coh  -- stepping preserves coherence; 
  * step_inv  -- stepping preserves the invariant; 

 *)

Structure action (V : Type) (this : nid)
  := Action
       {
         a_safe : dstatelet -> Prop;
         a_step : dstatelet -> dstatelet -> Prop;
         a_W : Type;
         a_sp : dstatelet -> dstatelet -> spec V;
         a_prog : forall d1 d2, STbin (a_sp d1 d2); 
         
         safe_coh : forall d, a_safe d -> coh p d;
         (* safe_inv : forall d h, a_safe d -> a_sp.1 h -> *)
         (*                        I (getLocal this d) h; *)
         safe_step : forall d, a_safe d -> exists d', a_step d d';
         step_coh  : forall d1 d2, a_step d1 d2 -> coh p d2;
         step_inv  : forall h1 d1 v h2 d2,
             I (getLocal this d1) h1 -> (a_sp d1 d2).2 (Val v) h1 h2 ->
             a_step d1 d2 -> I (getLocal this d2) h2
}.

Notation send_ts := (@snd_trans _ p).
Notation receive_ts := (@rcv_trans _ p).


(* Now let's define wrappers for the three kinds of atomic actions *)

(* A wrapper for the idle action and some heap-manipulating code *)
Section IdleWrapper.

Variable this : nid.
Variable V : Type.
Variable sp : dstatelet -> dstatelet -> spec V.

Definition idle_safe d := coh p d.
Definition idle_step d1 d2 := coh p d1 /\ d2 = d1.

(* This is to be provided by the user *)
(* Variable pf1 : forall d h, coh p d -> sp.1 h -> I (getLocal this d) h. *)

Variable pf2 : forall d h1 h2 v,
    I (getLocal this d) h1 -> (sp d d).2 (Val v) h1 h2 -> I (getLocal this d) h2.

Lemma idle_safe_coh d : idle_safe d -> coh p d.
Proof. done. Qed.

(* Lemma idle_safe_inv d h : idle_safe d -> sp.1 h -> I (getLocal this d) h. *)
(* Proof. by apply: pf1. Qed. *)

Lemma idle_safe_step d: idle_safe d -> exists d', idle_step d d'.
Proof. by move=>H; exists d. Qed. 

Lemma idle_step_coh d1 d2: idle_step d1 d2 -> coh p d2.
Proof. by case=>C->. Qed.

Lemma idle_step_inv h1 d1 v h2 d2 :
  I (getLocal this d1) h1 -> (sp d1 d2).2 (Val v) h1 h2 ->
  idle_step d1 d2 -> I (getLocal this d2) h2.
Proof.
move=>H2 H3 H4; case: H4=>_ Z; subst d2.
by move: (pf2 H2 H3)=>G.
Qed.

Variable e : forall d1 d2, STbin (sp d1 d2).

(* Idle action has the same type as the underlying imperative code *)
Definition idle_act := Action V e idle_safe_coh idle_safe_step
                              idle_step_coh idle_step_inv.

End IdleWrapper.

(* A wrapper for the send-command, where the heap-manipulating code
   _precedes_ the actual send instruction, but the message to be sent
   is given upfront. *)
Section SendWrapper.

Variable this : nid.

(* st is a specific send_transition *)
Variable st : send_trans (coh p).

Definition inv_heap d i := [Pred h : heap | h = i /\ I d h].


(* TODO: redefine this wrapper so it would accommodate a general
   specification *)
(* This is not the spec we need, need to strengthen *)
Definition inv_spec d1 d2 :=
  (fun i => exists h, inv_heap (getLocal this d1) h i,
     fun (y : ans unit) i m => forall d1 h,
         inv_heap (getLocal this d1) h i -> inv_heap (getLocal this d2) h m).

(* Next Obligation. by move=>h2[d [h1]]/=[Z]H V; subst h2; heval. Qed. *)

Variable msg: seq nat.
Variable to: nid.

Definition sact_safe d := send_safe st to d msg.

(* Variable sact_safe_inv : forall d h, *)
(*     sact_safe d -> unit_spec.1 h -> I (getLocal this d) h. *)

Lemma sact_safe_coh d : sact_safe d -> coh p d.
Proof. by move/s_safe_coh. Qed.

Definition sact_step d1 d2 := exists b,
    Some b = send_step st this to d1 msg /\
    let: f' := upd this b (dstate d1) in
    let: tms := TMsg (t_snd st) msg in 
    let: s' := (post_msg (dsoup d1) (Msg tms this to true)).1 in 
    d2 = (DStatelet f' s').

Lemma sact_safe_step d: sact_safe d -> exists d', sact_step d d'.
Proof.
move=>S. move/s_safe_def: (S)=>/(_ this)[b] E.
set d2 := let: f' := upd this b (dstate d) in
          let: tms := TMsg (t_snd st) msg in 
          let: s' := (post_msg (dsoup d) (Msg tms this to true)).1 in 
          (DStatelet f' s').
by exists d2, b.
Qed.

Lemma sact_step_coh d1 d2 : sact_step d1 d2 -> coh p d2.
Proof. by case=>b [E]Z; subst d2; apply: s_step_coh. Qed.

(* Send goes at the end of the atomic section *)
Variable sact_step_inv :
  forall h1 d1 (_ : unit) h2 d2,
  I (getLocal this d1) h1 ->
  (inv_spec d1 d2).2 (Val tt) h1 h2 ->
  sact_step d1 d2 -> I (getLocal this d2) h2.

Variable inv_prog : forall d1 d2, STbin (inv_spec d1 d2).

(* Send action has returns unit type and changes the state
   according to the invariant *)
Definition send_act := Action unit inv_prog sact_safe_coh 
                              sact_safe_step sact_step_coh sact_step_inv.

(* TODO: Think how to strenghen the precondition with an invariant *)

(* TODO: Define the wrapper for the try-receive-transition. How to
   propagate the result of receiving to the subsequent code? *)

End SendWrapper.


Section ReceiveWrapper.

(* TODO: define receive-wrapper *)


End ReceiveWrapper.


End Actions.



End Actions.

