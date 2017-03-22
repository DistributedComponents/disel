From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
Require Import pred prelude idynamic ordtype finmap pcm unionmap heap coding domain.
Require Import Freshness State EqTypeX Protocols Worlds NetworkSem Rely.
Require Import Actions.
Require Import SeqLib.
Require Import QueryProtocol.

Section QueryHookedRely.

Variables (lc lq : Label) (pc : protocol).

(*

TODO:

0. Add necessary exports in QueryProtocol
1. Formulate the property over the combined worlds of a core protocol
   pc and a query protocol pq.
2. Show that this property is preseverd by the joined rely.

*)


End QueryHookedRely.

