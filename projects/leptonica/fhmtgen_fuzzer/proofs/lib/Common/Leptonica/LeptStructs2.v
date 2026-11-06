(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec CatExec StepTac StoreOk MemSplit RefMemcpyLib.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptStructs.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma zbv8_mod : forall x y, x mod 256 = y mod 256 -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof.
  intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. exact H.
Qed.

Lemma le8_split : forall a b, 0 <= a < 2^32 -> 0 <= b < 2^32 ->
  Z_to_le_bytes 8 (a + 2^32 * b) = Z_to_le_bytes 4 a ++ Z_to_le_bytes 4 b.
Proof.
  intros a b Ha Hb. cbn [Z_to_le_bytes app].
  rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ].
  rewrite !Z.shiftr_div_pow2 by lia.
  repeat (f_equal; [apply zbv8_mod; Z.div_mod_to_equations; lia|]).
  f_equal. apply zbv8_mod. Z.div_mod_to_equations. lia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithSegs.
Context {fx : FPState}.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition c_dna (v : cmapv) : Z := c_d v + 2^32 * c_nalloc v.

Lemma c_dna_range : forall v, cmap_wf v -> 0 <= c_dna v < 2^64.
Proof. intros v [_ Hd Hn _ _]. unfold c_dna. lia. Qed.

Lemma CMAP_rd_dna : forall m c v, CMAPat m c v ->
  rdn segs m (Z_to_bv 64 (c + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (c_dna v))).
Proof.
  intros m c v HP. pose proof HP as (Hp & Hn & WF & HB). pose proof (c_dna_range v WF) as R.
  rewrite w2b_Z by lia. unfold c_dna. destruct WF as [_ Hd Hna _ _]. rewrite le8_split by lia.
  pose proof (bytes_at_field segs m c (cmap_bytes v) 8%nat 8%nat ltac:(lia) ltac:(rewrite cmap_bytes_len; cbn; lia) ltac:(rewrite cmap_bytes_len; cbn; lia) HB) as H.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H. exact H.
Qed.

Lemma CMAP_wr_dna : forall m c v d na, CMAPat m c v -> 0 <= d < 2 ^ 31 -> 0 <= na < 2 ^ 31 ->
  CMAPat (wbytes m (Z_to_bv 64 (c + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (d + 2^32 * na)))) c (cset_nalloc (cset_d v d) na).
Proof.
  intros m c v d na HP Hd Hna. destruct HP as (Hp & Hn & WF & HB).
  split; [lia|]. split; [lia|]. split; [destruct WF; constructor; cbn; lia|].
  rewrite w2b_Z by lia. rewrite le8_split by lia.
  pose proof (bytes_at_wbytes_in m c (cmap_bytes v) 8%nat (Z_to_le_bytes 4 d ++ Z_to_le_bytes 4 na) HB ltac:(lia) ltac:(rewrite cmap_bytes_len; cbn; lia)
                ltac:(rewrite cmap_bytes_len; cbn; lia)) as H.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H. exact H.
Qed.

End WithSegs.
