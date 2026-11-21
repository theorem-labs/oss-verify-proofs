(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Step Arr Image.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.cks Require Import CkTables.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CkB Require Import CkBImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ACRCTAB   : Z := 0x20fe0.
Definition ABRAID    : Z := 0x214e0.
Definition AX2N      : Z := 0x228e0.
Definition AADLMAGIC : Z := 0x10310.

Definition zw (l : list Z) : list word := map (Z_to_bv 64) l.
Lemma zw_length : forall l, length (zw l) = length l.
Proof. intros. unfold zw. apply length_map. Qed.

Lemma zw_nth : forall l i, (i < length l)%nat -> nth_error (zw l) i = Some (Z_to_bv 64 (nth i l 0)).
Proof.
  intros l i Hi. unfold zw. rewrite nth_error_map.
  rewrite (nth_error_nth' l 0 Hi). reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma u32ro_read : forall m A ws (i : Z) w a,
  bytes_at segs m A (u32s ws) -> nth_error ws (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (A + 4 * i) ->
  ov_read_bytes segs m a 4 = Some (le4 w).
Proof.
  intros m A ws i w a Hb Hn Hi ->.
  destruct (u32s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (4 * i)%Z with (Z.of_nat (4 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read segs m A (u32s ws) (4 * Z.to_nat i) 4 Hb).
  2:{ rewrite Eu, !length_app, length_le4, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le4; lia).
  rewrite length_le4, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Lemma zw_read : forall m A l (i : Z) a,
  bytes_at segs m A (u32s (zw l)) -> 0 <= i < Z.of_nat (length l) -> a = wa (A + 4 * i) ->
  ov_read_bytes segs m a 4 = Some (le4 (Z_to_bv 64 (nth (Z.to_nat i) l 0))).
Proof.
  intros m A l i a Hb Hi Ha.
  apply (u32ro_read m A (zw l) i (Z_to_bv 64 (nth (Z.to_nat i) l 0)) a Hb); [apply zw_nth; lia | lia | exact Ha].
Qed.
End WithSegs.


Lemma crc_table_bytesA : forall m, mem_inv asegs m -> bytes_at asegs m ACRCTAB (u32s (zw crc_table)).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | unfold ACRCTAB; lia | rewrite u32s_length, zw_length; unfold ACRCTAB; cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma braid_table_bytesA_0 : forall m, mem_inv asegs m -> bytes_at asegs m ABRAID (u32s (zw crc_braid_table_0)).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | unfold ABRAID; lia | rewrite u32s_length, zw_length; unfold ABRAID; cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
Lemma braid_table_bytesA_1 : forall m, mem_inv asegs m -> bytes_at asegs m (ABRAID + 1024) (u32s (zw crc_braid_table_1)).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | unfold ABRAID; lia | rewrite u32s_length, zw_length; unfold ABRAID; cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
Lemma braid_table_bytesA_2 : forall m, mem_inv asegs m -> bytes_at asegs m (ABRAID + 2048) (u32s (zw crc_braid_table_2)).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | unfold ABRAID; lia | rewrite u32s_length, zw_length; unfold ABRAID; cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
Lemma braid_table_bytesA_3 : forall m, mem_inv asegs m -> bytes_at asegs m (ABRAID + 3072) (u32s (zw crc_braid_table_3)).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | unfold ABRAID; lia | rewrite u32s_length, zw_length; unfold ABRAID; cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma x2n_table_bytesA : forall m, mem_inv asegs m -> bytes_at asegs m AX2N (u32s (zw x2n_table)).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | unfold AX2N; lia | rewrite u32s_length, zw_length; unfold AX2N; cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma adl_magic_bytesA : forall m, mem_inv asegs m -> bytes_at asegs m AADLMAGIC (le8 (Z_to_bv 64 AMAGIC)).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | unfold AADLMAGIC; lia | unfold AADLMAGIC; cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.


Lemma ctab_read : forall m i a, mem_inv asegs m -> 0 <= i < 256 -> a = wa (ACRCTAB + 4 * i) ->
  ov_read_bytes asegs m a 4 = Some (le4 (Z_to_bv 64 (ctab i))).
Proof.
  intros m i a MI Hi Ha. unfold ctab.
  apply (zw_read asegs m ACRCTAB crc_table i a (crc_table_bytesA m MI)); [rewrite crc_table_length; lia | exact Ha].
Qed.

Lemma btab_read : forall m k i a, mem_inv asegs m -> 0 <= k < 4 -> 0 <= i < 256 -> a = wa (ABRAID + 1024 * k + 4 * i) ->
  ov_read_bytes asegs m a 4 = Some (le4 (Z_to_bv 64 (btab k i))).
Proof.
  intros m k i a MI Hk Hi Ha. unfold btab.
  assert (K : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
  destruct K as [-> | [-> | [-> | ->]]]; cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add nth crc_braid_table].
  - apply (zw_read asegs m ABRAID crc_braid_table_0 i a (braid_table_bytesA_0 m MI)); [change (length crc_braid_table_0) with 256%nat; lia|].
    rewrite Ha. apply f_equal. lia.
  - apply (zw_read asegs m (ABRAID + 1024) crc_braid_table_1 i a (braid_table_bytesA_1 m MI)); [change (length crc_braid_table_1) with 256%nat; lia|].
    rewrite Ha. apply f_equal. lia.
  - apply (zw_read asegs m (ABRAID + 2048) crc_braid_table_2 i a (braid_table_bytesA_2 m MI)); [change (length crc_braid_table_2) with 256%nat; lia|].
    rewrite Ha. apply f_equal. lia.
  - apply (zw_read asegs m (ABRAID + 3072) crc_braid_table_3 i a (braid_table_bytesA_3 m MI)); [change (length crc_braid_table_3) with 256%nat; lia|].
    rewrite Ha. apply f_equal. lia.
Qed.

Lemma x2n_read : forall m i a, mem_inv asegs m -> 0 <= i < 32 -> a = wa (AX2N + 4 * i) ->
  ov_read_bytes asegs m a 4 = Some (le4 (Z_to_bv 64 (x2n i))).
Proof.
  intros m i a MI Hi Ha. unfold x2n.
  apply (zw_read asegs m AX2N x2n_table i a (x2n_table_bytesA m MI)); [rewrite x2n_table_length; lia | exact Ha].
Qed.

Lemma adl_magic_read : forall m a, mem_inv asegs m -> a = wa AADLMAGIC ->
  ov_read_bytes asegs m a 8 = Some (le8 (Z_to_bv 64 AMAGIC)).
Proof.
  intros m a MI ->. pose proof (adl_magic_bytesA m MI) as B.
  pose proof (bytes_at_ov_read asegs m AADLMAGIC _ 0 8 B ltac:(cbn; lia)) as R.
  rewrite Z.add_0_r in R. exact R.
Qed.

Lemma forallb_u32_nth : forall (l : list Z) i,
  forallb (fun z => (0 <=? z) && (z <? 2^32)) l = true -> 0 <= nth i l 0 < 2^32.
Proof.
  intros l i C. destruct (Nat.lt_ge_cases i (length l)) as [L|L].
  - rewrite forallb_forall in C. specialize (C _ (nth_In l 0 L)).
    apply andb_prop in C as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. lia.
  - rewrite nth_overflow by exact L. lia.
Qed.

Lemma ctab_range : forall i, 0 <= ctab i < 2^32.
Proof. intros i. unfold ctab. apply forallb_u32_nth. vm_compute. reflexivity. Qed.

Lemma x2n_range : forall i, 0 <= x2n i < 2^32.
Proof. intros i. unfold x2n. apply forallb_u32_nth. vm_compute. reflexivity. Qed.

Lemma btab_range : forall k i, 0 <= btab k i < 2^32.
Proof.
  intros k i. unfold btab.
  assert (C : forallb (fun l => forallb (fun z => (0 <=? z) && (z <? 2^32)) l) crc_braid_table = true) by (vm_compute; reflexivity).
  destruct (Nat.lt_ge_cases (Z.to_nat k) (length crc_braid_table)) as [Lk|Lk].
  - rewrite forallb_forall in C. apply forallb_u32_nth. apply C. apply nth_In. exact Lk.
  - rewrite (nth_overflow crc_braid_table [] Lk). destruct (Z.to_nat i); cbn; lia.
Qed.
