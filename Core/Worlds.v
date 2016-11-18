From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
Require Import pred prelude idynamic ordtype finmap pcm unionmap heap coding.
Require Import Freshness State EqTypeX DepMaps Protocols.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module WorldGetters.
Section WorldGetters.

(* It's okay to have duplicating nodes in this list *)

(* World is a dependent partial map of protocols *)

Definition world := depmap plab.
Variable w : world.

Variables (p : protocol) (st: send_trans (Protocols.coh p)).

(* The function is, in fact, partially defined and returns Empty
   Protocol for a non-present label. *)
Definition getProtocol i : protocol:=
  match find i (dmap w) with
  | Some p => p
  | None => EmptyProt i 
  end.

End WorldGetters.
End WorldGetters.


Export WorldGetters.

(* Defining coherence of a state with respect to the world *)

Module Worlds.

Module Core.
Section Core.

(* The following definition ties together worlds and states *)

Definition Coh (w : world) : Pred state := fun s =>
  [/\ valid w, valid s, ddom w =i dom s &
      forall l, coh (getProtocol w l) (getStatelet s l)].

Lemma cohW w s : Coh w s -> valid w.
Proof. by case. Qed.


Lemma cohS w s : Coh w s -> valid s.
Proof. by case. Qed.

Lemma cohD w s : Coh w s -> ddom w =i dom s.
Proof. by case. Qed.

Lemma coh_coh w s l : Coh w s -> coh (getProtocol w l) (getStatelet s l).
Proof. by case. Qed.

(* Now we need to establish a bunch of natural properties with respect
   to coherence of worlds and states. *)

Lemma unit_coh w s :
  Coh w s -> w = Unit <-> s = Unit.
Proof.
case=>V V' E H; split=>Z; [subst w|subst s]; rewrite /ddom dom0 in E; last first.
- by move/(dom0E V): E; move/dep_unit.
have E': dom s =i pred0 by move=>z; move: (E z)=>->.
by move/(dom0E V') : E'.
Qed.

Lemma Coh0 (w : world) (s : state) :
  w = Unit -> s = Unit -> Coh w s.
Proof.
move=>->->{w s}; split=>//=[|l]; first by rewrite /ddom !dom0.
by rewrite /getProtocol /getStatelet !find0E. 
Qed.

(* Lemma CohUnL (w1 w2 : world) (s1 s2 : state) : *)
(*   Coh (w1 \+ w2) (s1 \+ s2) -> Coh w1 s1. *)
(* Proof. *)
(* case=>W V D H; split. *)
(* - by move/validL: W. *)
(* - by move/validL: V. *)

Lemma CohUn (w1 w2 : world) (s1 s2 : state) :
  Coh w1 s1 -> Coh w2 s2 ->
  valid (w1 \+ w2) -> Coh (w1 \+ w2) (s1 \+ s2).
Proof.
move=>C1 C2 V.
case: (C1)=>_ G1 J1 H1; case: (C2)=>_ G2 J2 H2.
have X: valid (s1 \+ s2).
- case: validUn=>//; [by rewrite G1|by rewrite G2|move=>l; rewrite -J1 -J2=>D1 D2].
  rewrite /valid/=/DepMaps.valid/= in V.
  by case: validUn V=>//=V1 V2; move/(_ _ D1); rewrite D2.
have Y: ddom (w1 \+ w2) =i dom (s1 \+ s2).
- move=>z; rewrite !domUn !inE/=.
  by rewrite /valid/=/DepMaps.valid/= in V; rewrite V X/= J1 J2.  
split=>// l; rewrite /getProtocol /getStatelet.
case: (dom_find l (s1 \+ s2))=>[|v]Z.
- move/find_none: (Z); rewrite -Y.
  by case: dom_find=>//->_; rewrite Z.
move/find_some: (Z)=>D; rewrite Z; rewrite -Y in D=> E.
case: dom_find D=>// p Z' _ _; rewrite Z'.
rewrite findUnL // in Z; rewrite findUnL // J1 in Z'.
by case: ifP Z Z'=>_ F1 F2; [move: (H1 l)|move: (H2 l)];
   rewrite /getProtocol /getStatelet F1 F2.
Qed.


(* Coherence is trivially precise wrt. statelets *)
Lemma coh_prec W: precise (Coh W).
Proof.
move=>s1 s2 t1 t2 V E C1 C2.
case: (C1)(C2)=>H1 G1 D1 _ [H2 G2 D2 _].
by apply: (@dom_prec _ _ _  s1 s2 t1 t2)=>//z; rewrite -D1 -D2.
Qed.

Lemma locE i n k x y :
  k \in dom i -> valid i -> valid (dstate (getStatelet i k)) ->
  getLocal n (getStatelet (upd k
       {| dstate := upd n x (dstate (getStatelet i k));
          dsoup := y |} i) k) = x.
Proof.
move=>D V; rewrite /getStatelet; case:dom_find (D) =>//d->_ _.
by rewrite findU eqxx/= V /getLocal/= findU eqxx/==>->.
Qed.

Lemma locE' d n x y :
  valid (dstate d) ->
  getLocal n {| dstate := upd n x (dstate d);
                dsoup := y |} = x.
Proof.
by move=>V; rewrite /getLocal findU eqxx/= V. Qed.

Lemma locU n n' x st s :
  n != n' ->
  valid st ->
  getLocal n {| dstate := upd n' x st; dsoup := s |} =
  getLocal n {| dstate := st; dsoup := s |}.
Proof.
  move=> /negbTE N V.
  by rewrite /getLocal findU/= N.
Qed.

Section MakeWorld.

Variable p : protocol.
Notation l := (plab p).

Program Definition mkWorld := @DepMap _ plab (l \\-> p) _.
Next Obligation.
by apply/allP=>z; rewrite um_keysPt inE=>/eqP Z; subst z; rewrite gen_findPt/=.
Qed.

Lemma prEq : (getProtocol mkWorld l) = p.
Proof. by rewrite /getProtocol um_findPt. Qed.

                            
(*

Here's an incomplete list of procedures and facts, which might be
useful eventually:

- Define getters for particular transitions of worlds;

 *)

End MakeWorld.

(* TODO: try_recv should be restricted by a set of labels and a set of
   protocols *)
End Core.
End Core.

End Worlds.

Export Worlds.Core.
