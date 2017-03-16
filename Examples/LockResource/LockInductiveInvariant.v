(* Eventually, we will want to prove an inductive invariant showing mutual exclusion. Here's a (commented-out) start to it. *)

(*
Inductive global_state :=
| ClientHolds of nid
| ServerHolds
| Granting of nid
| Releasing of nid.

Definition no_active_msg_tokens : Pred soup :=
  [Pred s | valid s /\
            forall m ms, find m s = Some ms -> active ms -> tag (content ms) == acquire_tag].

Definition ClientHolds_coh d e c :=
  [/\ client_local_coh (Held e) (getLocal c d)
   , (forall c', c' \in clients -> c' != c -> client_local_coh NotHeld (getLocal c' d))
   & no_active_msg_tokens (dsoup d) ].

Definition ServerHolds_coh d :=
  (forall c, c \in clients -> client_local_coh NotHeld (getLocal c d)) /\
  no_active_msg_tokens (dsoup d).

Definition Granting_coh d :=
  (forall c, c \in clients -> client_local_coh NotHeld (getLocal c d)) /\
*)