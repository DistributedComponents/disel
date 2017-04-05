From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
Require Import pred prelude idynamic ordtype finmap pcm unionmap heap coding.
Require Import Freshness.
Require Import State.
Require Import EqTypeX.
Require Import DepMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NewSoupPredicates.

(*****************************************************)
(*        More elaborated message predicates         *)
(*****************************************************)


Definition msg_in_soup' from to (cond : nat -> seq nat -> bool) (d : soup) :=
    exists! i, exists t c,
        find i d = Some (Msg (TMsg t c) from to true) /\ cond t c.

Definition msg_spec' from to tg cnt :=
  msg_in_soup' from to (fun x y => (x == tg) && (y == cnt)).

Definition no_msg_from_to' from to
           (criterion : nat -> seq nat -> bool) (d : soup) :=
  forall i t c,
    find i d = Some (Msg (TMsg t c) from to true) ->
    ~~criterion t c.

Lemma no_msg_from_to_consume' from to cond s i:
  valid s ->
  no_msg_from_to' from to cond s ->
  no_msg_from_to' from to cond (consume_msg s i).
Proof.
move=>V H m t c .
rewrite /consume_msg; case: (find i s); last by move=>F; apply: (H m t c F).
move=>ms; case B: (m == i).
- by move/eqP: B=>B; subst m; rewrite findU eqxx/= V.
by rewrite findU B/==>/(H m t c).
Qed.

(* Lemma msg_spec_consume' s from to tg cnt cond i : *)
(*   valid s ->  *)
(*   find i s = Some {| content := TMsg tg cnt; *)
(*                      from := from; to := to; active := true |} -> *)
(*   msg_in_soup from to cond s -> *)
(*   no_msg_from_to' from to cond (consume_msg s i). *)
(* Proof. *)
(* move=>V E[][j][[t][c]]F H1 H2.  *)
(* move=>m t' c'; rewrite /consume_msg; move: (find_some E). *)
(* case: dom_find=>// msg->_ _; case B: (m == i). *)
(* - by move/eqP: B=>B; subst m; rewrite findU eqxx/= V. *)
(* have X: j = i by apply: (H1 i); exists tg, cnt. *)
(* subst j; rewrite findU B/=. case: b=>// E' _. *)
(* suff X: i = m by subst i; rewrite eqxx in B. *)
(* by apply: (H1 m); exists t', c'.  *)
(* Qed. *)

End NewSoupPredicates.