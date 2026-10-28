(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame ZdHufFse ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkMem ZdSeqBuildW ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_hft_kit.
Import ListNotations.
Open Scope Z_scope.

Lemma sk_bytes_sub : forall segs m A (bs : list byte) k n,
  bytes_at segs m A bs -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length bs) ->
  bytes_at segs m (A + k) (firstn n (skipn (Z.to_nat k) bs)).
Proof.
  intros segs m A bs k n H Hk Hn.
  rewrite <- (firstn_skipn (Z.to_nat k) bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length_le in H by lia. replace (A + Z.of_nat (Z.to_nat k)) with (A + k) in H by lia.
  rewrite <- (firstn_skipn n (skipn (Z.to_nat k) bs)) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma sk_firstn4 : forall (tb : list Z) k, 0 <= k -> k + 4 <= Z.of_nat (length tb) ->
  firstn 4 (skipn (Z.to_nat k) tb) = [Znth k tb; Znth (k + 1) tb; Znth (k + 2) tb; Znth (k + 3) tb].
Proof.
  intros tb k Hk Hl. unfold Znth.
  replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
  replace (Z.to_nat (k + 2)) with (S (S (Z.to_nat k))) by lia.
  replace (Z.to_nat (k + 3)) with (S (S (S (Z.to_nat k)))) by lia.
  assert (LT : (Z.to_nat k + 3 < length tb)%nat) by lia.
  revert LT. generalize (Z.to_nat k). clear. intros j. revert tb. induction j as [|j IH]; intros tb LT.
  - destruct tb as [|a [|b [|c [|d t]]]]; cbn [length] in LT; try lia. reflexivity.
  - destruct tb as [|a t]; cbn [length] in LT; [lia|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma sk_zle2 : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> zle2 (a + 256 * b) = [a; b].
Proof.
  intros a b Ha Hb. unfold zle2. f_equal; [|f_equal].
  - symmetry. apply Z.mod_unique with (q := b); lia.
  - replace ((a + 256 * b) / 256) with b by (apply Z.div_unique with (r := a); lia). apply Z.mod_small. lia.
Qed.

Lemma sk_cell2_ro : forall segs m A (tb : list Z) k,
  bytes_at segs m A (map (Z_to_bv 8) tb) -> Forall (fun v => 0 <= v < 256) tb -> 0 <= k -> k + 4 <= Z.of_nat (length tb) ->
  ro_cells segs m (A + k) [C2 (Z_to_bv 64 (Znth k tb + 256 * Znth (k + 1) tb)); C2 (Z_to_bv 64 (Znth (k + 2) tb + 256 * Znth (k + 3) tb))].
Proof.
  intros segs m A tb k H HB Hk Hl.
  pose proof (sk_bytes_sub segs m A _ k 4 H Hk ltac:(rewrite length_map; lia)) as S.
  rewrite skipn_map, firstn_map, (sk_firstn4 tb k Hk Hl) in S.
  split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  rewrite (le2_Z _ _ eq_refl), (le2_Z (Znth (k + 2) tb + 256 * Znth (k + 3) tb) _ eq_refl).
  assert (BR : forall i, 0 <= i < Z.of_nat (length tb) -> 0 <= Znth i tb < 256) by (intros i Hi; apply (Forall_Znth (fun v => 0 <= v < 256) tb i HB Hi)).
  rewrite (sk_zle2 (Znth k tb) (Znth (k + 1) tb)) by (apply BR; lia).
  rewrite (sk_zle2 (Znth (k + 2) tb) (Znth (k + 3) tb)) by (apply BR; lia). exact S.
Qed.

Lemma sk_mask_ro : forall m tl, mem_inv usegs m -> 0 <= tl <= 31 ->
  ro_cells usegs m (FBITMASK + 4 * tl) [C4 (Z_to_bv 64 (2^tl - 1))].
Proof.
  intros m tl MI H. split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  pose proof (sk_bytes_sub usegs m FBITMASK fbitmask_bytes (4 * tl) 4 (fbitmask_at m MI) ltac:(lia) ltac:(change (length fbitmask_bytes) with 128%nat; lia)) as S.
  replace (le4 (Z_to_bv 64 (2^tl - 1))) with (firstn 4 (skipn (Z.to_nat (4 * tl)) fbitmask_bytes)); [exact S|].
  assert (C : exists k : nat, (k <= 31)%nat /\ tl = Z.of_nat k) by (exists (Z.to_nat tl); lia).
  destruct C as (k & Hk & ->). do 32 (destruct k as [|k]; [apply fbytes_eq_unsigned; vm_compute; reflexivity|]). lia.
Qed.

Lemma sk_hdr_ro : forall segs m DT (v : word), bytes_at segs m DT (le2 v) -> ro_cells segs m DT [C2 v].
Proof.
  intros segs m DT v H. split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H.
Qed.

Lemma sk_fast_bits : forall x nb, 0 <= x < 2^64 -> 1 <= nb <= 63 -> 0 <= x / 2 ^ (((-1 * nb) mod 2^64) mod 64) < 2^nb.
Proof.
  intros x nb Hx Hn.
  replace ((-1 * nb) mod 2^64) with (2^64 - nb) by (apply Z.mod_unique with (q := -1); lia).
  replace ((2^64 - nb) mod 64) with (64 - nb) by (apply Z.mod_unique with (q := 2^58 - 1); lia).
  split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]|].
  apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|]. rewrite <- Z.pow_add_r by lia. replace (64 - nb + nb) with 64 by lia. lia.
Qed.

Lemma sk_land_mask : forall x nb, 0 <= nb <= 62 -> 0 <= Z.land x ((2^nb + -1) mod 2^64) < 2^nb.
Proof.
  intros x nb Hn. assert (P : 0 < 2^nb) by (apply Z.pow_pos_nonneg; lia).
  assert (Q : 2^nb <= 2^62) by (apply Z.pow_le_mono_r; lia).
  rewrite Z.mod_small by lia. replace (2^nb + -1) with (Z.ones nb) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia. apply Z.mod_pos_bound. exact P.
Qed.

Lemma sk_cb16 : forall segs m A j, rw_cells segs m A [CB 16 j] -> exists w0 w1, rw_cells segs m A [C8 w0; C8 w1].
Proof.
  intros segs m A j H.
  apply (rw_cells_split_CB segs _ _ [] 16 _ [] [8; 8]%nat) in H; [| reflexivity]. cbn [mk_CB_cells app] in H.
  lazymatch type of H with rw_cells _ _ _ (CB 8 ?j0 :: ?post) => destruct (cb8_as_c8 segs _ _ [] j0 post H) as [w0 H1] end. cbn [app] in H1.
  lazymatch type of H1 with rw_cells _ _ _ (?c0 :: CB 8 ?j1 :: ?post) => destruct (cb8_as_c8 segs _ _ [c0] j1 post H1) as [w1 H2] end. cbn [app] in H2.
  exists w0, w1. exact H2.
Qed.
