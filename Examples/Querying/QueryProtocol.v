From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import pred prelude idynamic ordtype finmap pcm unionmap heap coding domain.
Require Import Freshness State EqTypeX Protocols Worlds NetworkSem Rely.
Require Import Actions.
Require Import SeqLib.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition left_inverse {A B : Type} (op: A -> B) (inv : B -> A) :=
  forall x, inv (op x) = x.

(* Simple protocol for querying a state *)

Module QueryProtocol.
Section  QueryProtocol.

(* Arbitrary data type *)
Variable Data : Type.
Variable nodes : seq nat.

(* Serialize/decerialize functions *)
Variable serialize : Data -> seq nat.
Variable deserialize : seq nat -> Data.
Hypothesis ds_inverse : left_inverse serialize deserialize.

(* Protocol state *)
Definition st := ptr_nat 1.

(* Pending requests (client-side): node, request id *)
(* Pending responses (server-side): node, response id *)
Definition reqs := seq (nid * nat)%type.
Definition resp := seq (nid * nat)%type.

Definition qstate := (reqs * resp)%type.

(* All responses and requests are unique per-node *)
Definition localCoh (n : nid) : Pred heap :=
  [Pred h | exists (s : qstate), h = st :-> s /\ (uniq s.1 && uniq s.2)].

(* Tags *)
Definition treq : nat := 0.
Definition tresp : nat := 1.
Definition tags := [:: treq; tresp].

Definition cohMsg (ms: msg TaggedMessage) : Prop :=
  let body := content ms in
  (* If a message is a request, it carries a request number *)                                                           
  if tag body == treq then exists req_num, tms_cont body = [:: req_num]
  (* Otherwise it's a response and serialized data *)                                                           
  else exists resp_num sdata, tms_cont body = resp_num :: sdata.

Definition soupCoh : Pred soup :=
  [Pred s | valid s /\ forall m ms, find m s = Some ms -> cohMsg ms].

Definition qcoh d : Prop :=
  let: dl := dstate d in
  let: ds := dsoup d in
  [/\ soupCoh ds, valid dl, dom dl =i nodes &
      forall n, n \in dom dl -> localCoh n (getLocal n d)].

(* Axioms of the coherence predicate *)
Lemma l1 d: qcoh d -> valid (dstate d).
Proof. by case. Qed.

Lemma l2 d: qcoh d -> valid (dsoup d).
Proof. by case; case. Qed.

Lemma l3 d: qcoh d -> dom (dstate d) =i nodes.
Proof. by case. Qed.

(* Wrapping up the coherence predicate *)
Definition QCoh := CohPred (CohPredMixin l1 l2 l3).

(*********************************************************************)
(**********                Coherence lemmas                  *********)
(*********************************************************************)

Lemma consume_coh d m : QCoh d -> soupCoh (consume_msg (dsoup d) m).
Proof.
move=>C; split=>[|m' msg]; first by apply: consume_valid; rewrite (cohVs C).
case X: (m == m');[move/eqP: X=><-{m'}|].
- case/(find_mark (cohVs C))=>tms[E]->{msg}.
  by case:(C); case=>_/(_ m tms E).
rewrite eq_sym in X.
rewrite (mark_other (cohVs C) X)=>E.
by case:(C); case=>_; move/(_ m' msg E).
Qed.

Lemma trans_updDom this d s :
  this \in nodes -> QCoh d -> dom (upd this s (dstate d)) =i nodes.
Proof.
move=>D C z; rewrite -(cohDom C) domU inE/=.
by case: ifP=>///eqP->{z}; rewrite (cohDom C) D; apply: cohVl C.
Qed.

(****************************************************)
(********* Getter lemmas for local state ************)
(****************************************************)

Lemma cohSt n d (C : QCoh d) s:
  find st (getLocal n d) = Some s ->
  idyn_tp s = qstate.
Proof.
case: (C)=>_ _ D G; case H: (n \in nodes); rewrite -D in H.
- by move:(G _ H); case=>s'[]->_; rewrite hfindPt//=; case=><-.
by rewrite /getLocal; case: dom_find H=>//->; rewrite find0E.
Qed.

Definition getSt n d (C : QCoh d) : qstate :=
  match find st (getLocal n d) as f return _ = f -> _ with
    Some v => fun epf => icoerce id (idyn_val v) (cohSt C epf)
  | _ => fun epf => ([::], [::])
  end (erefl _).

Lemma getStK n d (C : QCoh d)  s :
  getLocal n d = st :-> s -> getSt n C = s.
Proof.
by move=>E; rewrite /getSt/=; move: (cohSt C); rewrite !E/==>H; apply: ieqc.
Qed.

Lemma getStE n i j C C' (pf : n \in nodes) :
  getLocal n j = getLocal n i ->
  @getSt n j C' = @getSt n i C.
Proof.
case: {-1}(C)=>_ _ D G; rewrite -D in pf; move:(G _ pf).
by move=>[s][E]_; rewrite (getStK C E) E; move/(getStK C' )->.
Qed.

Lemma getStE' n i j C C' (pf : n \in nodes) :
  @getSt n j C' = @getSt n i C ->
  getLocal n j = getLocal n i.
Proof.
case: {-1}(C)=>_ _ D G; rewrite -D in pf; move:(G _ pf).
move=>[s][E]_; rewrite (getStK C E) E=>H.
case: {-1}(C')=>_ _ D'/(_ n)=>G'; rewrite D' in G'; rewrite D in pf.
by move/G': pf=>[s'][E']_; rewrite (getStK C' E') in H; subst s'. 
Qed.

(****************************************************)

Notation coh := QCoh.

(*
TODOs:

- Define send/receive transfer functions for qstate;
- Prove inductive invariants of the protocol wrt. messages (linearity);

*)

End QueryProtocol.
End QueryProtocol.
