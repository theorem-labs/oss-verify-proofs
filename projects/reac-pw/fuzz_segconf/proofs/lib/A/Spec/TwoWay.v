(* Ported by RtStr from cold/c-asan-rt-fmio-n affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Spec/TwoWay.v, unchanged. *)
From Stdlib Require Import ZArith Arith List Lia Bool.
Import ListNotations.
Open Scope nat_scope.

Definition at_ (x : list Z) (i : nat) : Z := nth i x 0%Z.

Inductive msuf_run (gt : Z -> Z -> bool) (x : list Z) : nat -> nat -> nat -> nat -> nat -> nat -> Prop :=
| msr_stop : forall c jp k p,
    length x <= jp + k -> msuf_run gt x c jp k p c p
| msr_eq_p : forall c jp k p c' p',
    jp + k < length x -> at_ x (c + k - 1) = at_ x (jp + k) -> k = p ->
    msuf_run gt x c (jp + p) 1 p c' p' -> msuf_run gt x c jp k p c' p'
| msr_eq_k : forall c jp k p c' p',
    jp + k < length x -> at_ x (c + k - 1) = at_ x (jp + k) -> k <> p ->
    msuf_run gt x c jp (k + 1) p c' p' -> msuf_run gt x c jp k p c' p'
| msr_gt : forall c jp k p c' p',
    jp + k < length x -> at_ x (c + k - 1) <> at_ x (jp + k) -> gt (at_ x (c + k - 1)) (at_ x (jp + k)) = true ->
    msuf_run gt x c (jp + k) 1 (jp + k + 1 - c) c' p' -> msuf_run gt x c jp k p c' p'
| msr_lt : forall c jp k p c' p',
    jp + k < length x -> at_ x (c + k - 1) <> at_ x (jp + k) -> gt (at_ x (c + k - 1)) (at_ x (jp + k)) = false ->
    msuf_run gt x (jp + 1) (jp + 1) 1 1 c' p' -> msuf_run gt x c jp k p c' p'.

Fixpoint lexlt (gt : Z -> Z -> bool) (a b : list Z) : Prop :=
  match a, b with
  | [], [] => False
  | [], _ :: _ => True
  | _ :: _, [] => False
  | u :: a', v :: b' => (u <> v /\ gt v u = true) \/ (u = v /\ lexlt gt a' b')
  end.

Definition is_maxsuf (gt : Z -> Z -> bool) (x : list Z) (c : nat) : Prop :=
  c < length x /\ forall i, i < length x -> i <> c -> lexlt gt (skipn i x) (skipn c x).

Definition is_period (w : list Z) (p : nat) : Prop :=
  1 <= p /\ forall j, j + p < length w -> at_ w j = at_ w (j + p).

Definition smallest_period (w : list Z) (p : nat) : Prop :=
  is_period w p /\ p <= length w /\ forall q, is_period w q -> q <= length w -> p <= q.

Definition LR (x : list Z) (c d : nat) : Prop :=
  forall j, c <= j < c + d -> d <= j -> j < length x -> at_ x j = at_ x (j - d).

Definition tw_cut (c1 p1 c2 p2 : nat) : nat * nat := if c1 <? c2 then (c2, p2) else (c1, p1).

Definition TW_CRIT (x : list Z) (c p : nat) : Prop :=
  c < length x /\ 1 <= p /\ c + p <= length x /\
  ((forall j, j < c -> at_ x j = at_ x (j + p)) ->
     (forall j, j + p < length x -> at_ x j = at_ x (j + p)) /\ c <= p /\
     (forall d, 1 <= d < p -> ~ LR x c d)) /\
  (~ (forall j, j < c -> at_ x j = at_ x (j + p)) ->
     1 <= c /\ forall d, 1 <= d <= Nat.max (c - 1) (length x - c) -> ~ LR x c d).

Definition MAXSUF_OK : Prop :=
  forall (gt : Z -> Z -> bool) (x : list Z) c p,
    (forall a b, gt a b = true -> gt b a = false) ->
    (forall a b, a <> b -> gt a b = true \/ gt b a = true) ->
    (forall a b d, gt a b = true -> gt b d = true -> gt a d = true) ->
    1 <= length x ->
    msuf_run gt x 0 0 1 1 c p ->
    is_maxsuf gt x c /\ smallest_period (skipn c x) p.

Definition CRIT_OK : Prop :=
  forall (x : list Z) c1 p1 c2 p2,
    1 <= length x ->
    is_maxsuf Z.gtb x c1 -> smallest_period (skipn c1 x) p1 ->
    is_maxsuf Z.ltb x c2 -> smallest_period (skipn c2 x) p2 ->
    TW_CRIT x (fst (tw_cut c1 p1 c2 p2)) (snd (tw_cut c1 p1 c2 p2)).
