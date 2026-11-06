(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import AllocSure AllocCredit.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition RK_kern (h : Z) : Z := h + 2.
Definition RB_kern (h w : Z) : Z :=
  alloc_margin 24 + alloc_margin (h * 8) + (h * alloc_cost (w * 4) + alloc_margin (w * 4) + ROOM_CREDMAX).

Lemma RB_kern_nonneg : forall h w, 0 <= h -> 0 <= w -> 0 <= RB_kern h w.
Proof.
  intros h w Hh Hw. unfold RB_kern, ROOM_CREDMAX.
  pose proof (alloc_margin_ge 24 ltac:(lia)). pose proof (alloc_margin_ge (h * 8) ltac:(lia)). pose proof (alloc_margin_ge (w * 4) ltac:(lia)).
  pose proof (alloc_cost_ge (w * 4)) as [Hc _]. nia.
Qed.

(* [comment removed for export] *)
Lemma RB_kern_bound : forall h w, 1 <= h <= 20000 -> 1 <= w <= 20000 -> w * h <= 2 ^ 26 -> RB_kern h w <= 2 ^ 29 + 2 ^ 28.
Proof.
  intros h w Hh Hw Hwh. unfold RB_kern, ROOM_CREDMAX.
  rewrite (alloc_margin_small 24) by lia.
  pose proof (alloc_margin_big (h * 8) ltac:(lia)). pose proof (alloc_margin_big (w * 4) ltac:(lia)).
  pose proof (alloc_cost_sum (w * 4) h ltac:(lia) ltac:(lia)). nia.
Qed.

(* [comment removed for export] *)
Definition RK_kfp (d h : Z) : Z := if d =? 8 then RK_kern h else 0.
Definition RB_kfp (d h w : Z) : Z := if d =? 8 then RB_kern h w else 0.

Lemma RK_kfp_8 : forall h, RK_kfp 8 h = RK_kern h. Proof. reflexivity. Qed.
Lemma RB_kfp_8 : forall h w, RB_kfp 8 h w = RB_kern h w. Proof. reflexivity. Qed.

Lemma kfp_cost_bound : forall d h w, 1 <= h <= 20000 -> 1 <= w <= 20000 -> (d = 8 -> w * h <= 2 ^ 26) ->
  0 <= RK_kfp d h <= 20002 /\ 0 <= RB_kfp d h w <= 2 ^ 29 + 2 ^ 28.
Proof.
  intros d h w Hh Hw Hwh. unfold RK_kfp, RB_kfp. destruct (Z.eqb_spec d 8) as [E|NE]; [| lia].
  pose proof (RB_kern_nonneg h w ltac:(lia) ltac:(lia)). pose proof (RB_kern_bound h w Hh Hw (Hwh E)). unfold RK_kern. lia.
Qed.

(* [comment removed for export] *)
Definition RK_c2d (sy : Z) : Z := sy + 1.
Definition RB_c2d (sy sx : Z) : Z := alloc_margin (sy * 8) + (sy * alloc_cost (sx * 4) + alloc_margin (sx * 4) + ROOM_CREDMAX).

Lemma RK_kern_c2d : forall h, RK_kern h = 1 + RK_c2d h.
Proof. intros h. unfold RK_kern, RK_c2d. lia. Qed.
Lemma RB_kern_c2d : forall h w, RB_kern h w = alloc_margin 24 + RB_c2d h w.
Proof. intros h w. unfold RB_kern, RB_c2d. lia. Qed.
Lemma RB_c2d_nonneg : forall sy sx, 0 <= sy -> 0 <= sx -> 0 <= RB_c2d sy sx.
Proof.
  intros sy sx Hy Hx. unfold RB_c2d, ROOM_CREDMAX.
  pose proof (alloc_margin_ge (sy * 8) ltac:(lia)). pose proof (alloc_margin_ge (sx * 4) ltac:(lia)).
  pose proof (alloc_cost_ge (sx * 4)) as [Hc _]. nia.
Qed.
