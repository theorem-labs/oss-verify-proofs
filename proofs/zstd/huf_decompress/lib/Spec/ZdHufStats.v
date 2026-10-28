(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition hw_cells (w : Z) : Z := if w =? 0 then 0 else 2^(w - 1).
Fixpoint hw_total (ws : list Z) : Z := match ws with [] => 0 | w :: t => hw_cells w + hw_total t end.
(* [comment removed for export] *)
Definition hcount (ws : list Z) (w : Z) : Z := Z.of_nat (count_occ Z.eq_dec ws w).

Definition huf_stats_ok (ws rank : list Z) (tl : Z) : Prop :=
  1 <= tl <= 12 /\ 2 <= Zlength ws <= 256 /\ Forall (fun w => 0 <= w <= tl) ws /\ Zlength rank = 13 /\
  (forall w, 0 <= w <= 12 -> Znth w rank = hcount ws w) /\ hw_total ws = 2^tl.

Lemma hw_cells_nonneg w : 0 <= hw_cells w.
Proof. unfold hw_cells. destruct (w =? 0); [lia|]. apply Z.pow_nonneg. lia. Qed.
Lemma hw_total_nonneg ws : 0 <= hw_total ws.
Proof. induction ws as [|w t IH]; cbn [hw_total]; [lia|]. pose proof (hw_cells_nonneg w). lia. Qed.
Lemma hw_total_app a b : hw_total (a ++ b) = hw_total a + hw_total b.
Proof. induction a as [|w t IH]; cbn [hw_total app]; [lia|]. rewrite IH. lia. Qed.
Lemma hcount_app a b w : hcount (a ++ b) w = hcount a w + hcount b w.
Proof. unfold hcount. rewrite count_occ_app. lia. Qed.
Lemma hcount_nonneg ws w : 0 <= hcount ws w.
Proof. unfold hcount. lia. Qed.

(* [comment removed for export] *)
Definition rank_inv (ws rank : list Z) : Prop :=
  Zlength rank = 13 /\ forall w, 0 <= w <= 12 -> Znth w rank = hcount ws w.

Lemma hcount_nil w : hcount [] w = 0.
Proof. reflexivity. Qed.
Lemma hcount_one v w : hcount [v] w = if Z.eq_dec v w then 1 else 0.
Proof. unfold hcount. cbn [count_occ]. destruct (Z.eq_dec v w); reflexivity. Qed.

Lemma rank_inv_nil : rank_inv [] (repeat 0 13).
Proof.
  split; [reflexivity|]. intros w Hw. rewrite hcount_nil.
  assert (C : w = 0 \/ w = 1 \/ w = 2 \/ w = 3 \/ w = 4 \/ w = 5 \/ w = 6 \/ w = 7 \/ w = 8 \/ w = 9 \/ w = 10 \/ w = 11 \/ w = 12) by lia.
  repeat (destruct C as [->|C]; [reflexivity|]). subst w. reflexivity.
Qed.

Lemma rank_inv_step ws rank w : rank_inv ws rank -> 0 <= w <= 12 ->
  rank_inv (ws ++ [w]) (Zupd w (Znth w rank + 1) rank).
Proof.
  intros (L & H) Hw. split.
  - unfold Zlength in *. rewrite Zupd_length. exact L.
  - intros v Hv. rewrite hcount_app, hcount_one. destruct (Z.eq_dec w v) as [->|NE].
    + rewrite Znth_Zupd_same by lia. rewrite H by lia. reflexivity.
    + rewrite Znth_Zupd_other by lia. rewrite H by lia. lia.
Qed.

Lemma hw_cells_le_total ws w : In w ws -> hw_cells w <= hw_total ws.
Proof.
  induction ws as [|a t IH]; intros HI; [destruct HI|]. cbn [hw_total].
  pose proof (hw_cells_nonneg a). pose proof (hw_total_nonneg t).
  destruct HI as [->|HI]; [lia|]. specialize (IH HI). lia.
Qed.

Lemma hw_cells_bound w : 0 <= w <= 12 -> hw_cells w <= 2048.
Proof.
  intros Hw. unfold hw_cells. destruct (w =? 0); [lia|]. change 2048 with (2^11). apply Z.pow_le_mono_r; lia.
Qed.

Lemma hw_total_bound ws : Forall (fun w => 0 <= w <= 12) ws -> hw_total ws <= 2048 * Zlength ws.
Proof.
  induction 1 as [|w t Hw _ IH]; [cbn; lia|]. cbn [hw_total]. pose proof (hw_cells_bound w Hw).
  unfold Zlength in *. cbn [length]. lia.
Qed.

(* [comment removed for export] *)
Lemma hw_cells_lt_pow w tl : 0 <= w -> 0 <= tl -> hw_cells w < 2^tl -> w <= tl.
Proof.
  intros Hw Htl H. unfold hw_cells in H. destruct (Z.eqb_spec w 0) as [->|NZ]; [lia|].
  destruct (Z.le_gt_cases w tl) as [LE|GT]; [exact LE|]. exfalso.
  assert (2^tl <= 2^(w - 1)) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma huf_stats_final ws0 rank wt tl lw :
  Forall (fun w => 0 <= w <= 12) ws0 -> 1 <= Zlength ws0 <= 255 -> rank_inv ws0 rank -> hw_total ws0 = wt ->
  1 <= tl <= 12 -> 1 <= wt < 2^tl -> 1 <= lw -> 2^(lw - 1) = 2^tl - wt ->
  huf_stats_ok (ws0 ++ [lw]) (Zupd lw (Znth lw rank + 1) rank) tl.
Proof.
  intros FA LEN RI WT TL LT LW REST.
  assert (LWT : lw <= tl).
  { destruct (Z.le_gt_cases lw tl) as [LE|GT]; [exact LE|]. exfalso.
    assert (2^tl <= 2^(lw - 1)) by (apply Z.pow_le_mono_r; lia). lia. }
  split; [exact TL|]. split; [unfold Zlength in *; rewrite length_app; cbn [length]; lia|].
  split.
  { apply Forall_app. split.
    - rewrite Forall_forall in *. intros w HI. specialize (FA w HI). split; [lia|].
      apply hw_cells_lt_pow; [lia | lia |]. pose proof (hw_cells_le_total ws0 w HI). lia.
    - constructor; [lia | constructor]. }
  destruct (rank_inv_step ws0 rank lw RI ltac:(lia)) as (RL & RC).
  split; [exact RL|]. split; [exact RC|].
  rewrite hw_total_app. cbn [hw_total]. unfold hw_cells at 1. destruct (Z.eqb_spec lw 0) as [->|_]; [lia|]. lia.
Qed.
