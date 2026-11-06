(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec StoreOk LibDefs.
From Stdlib Require Import Zify.
Unset Nia Cache.  (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Lemma u_small' : forall z, 0 <= z < 2^64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 64) with (2^64)%Z. lia.
Qed.

Section Generic.
  Variable segs : list Segment.
  (* [comment removed for export] *)
  Hypothesis Hseg : forall x, 0x10000 <= x -> x + 1 <= 0x12000 ->
      exists seg, find_segment segs x 1 = Some seg /\ seg_writable seg = false.

  Lemma rodata_not_writable : forall mem (x : word),
      0x10000 <= bv_unsigned x -> bv_unsigned x + 1 <= 0x12000 ->
      mem x = None -> wview segs mem x = None.
  Proof.
    intros mem x H1 H2 Hn. unfold wview. rewrite Hn.
    destruct (Hseg (bv_unsigned x) H1 H2) as (seg & -> & Hw). rewrite Hw. reflexivity.
  Qed.

  Theorem writable_rodata_apart : forall mem lo n rlo rhi,
      0x10000 <= rlo -> rlo < rhi -> rhi <= 0x12000 ->
      writable segs mem lo n -> rodata_clear mem rlo rhi ->
      lo + n <= rlo \/ rhi <= lo.
  Proof.
    intros mem lo n rlo rhi Hr1 Hr2 Hr3 (Hlo & Hn & Hhi & Hst) Hro.
    assert (CONTRA : forall x, lo <= x < lo + n -> rlo <= x < rhi -> False).
    { intros x Hx Hrx.
      pose proof (store_ok_all segs mem (Z.to_nat n) (Z_to_bv 64 lo)) as A.
      rewrite u_small' in A by lia. rewrite Z2Nat.id in A by lia.
      specialize (A Hhi Hst (Z_to_bv 64 x)). rewrite u_small' in A by lia.
      apply (A Hx). apply rodata_not_writable; rewrite ?u_small' by lia; try lia.
      apply Hro. lia. }
    destruct (Z_lt_le_dec lo rlo) as [L|L].
    - left. destruct (Z_lt_le_dec rlo (lo + n)) as [L2|L2]; [|lia].
      exfalso. apply (CONTRA rlo); lia.
    - right. destruct (Z_lt_le_dec lo rhi) as [L2|L2]; [|lia].
      exfalso. apply (CONTRA lo); lia.
  Qed.
End Generic.

Lemma seg0_S1 : forall x, 0x10000 <= x -> x + 1 <= 0x12000 ->
  exists seg, find_segment Plain.M.loaded_segments x 1 = Some seg /\ seg_writable seg = false.
Proof.
  intros x H1 H2. exists Plain_segment_000.
  change Plain.M.loaded_segments with
    [Plain_segment_000; Plain_segment_001; Plain_segment_002; Plain_segment_003].
  cbn [find_segment].
  replace (Z.of_N (seg_base Plain_segment_000)) with 0x10000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Plain_segment_000)) with 0x2000 by (vm_compute; reflexivity).
  replace (0x10000 <=? x) with true by (symmetry; apply Z.leb_le; lia).
  replace (x + 1 <=? 0x10000 + 0x2000) with true by (symmetry; apply Z.leb_le; lia).
  cbn [andb]. split; [reflexivity|]. vm_compute. reflexivity.
Qed.

Lemma seg0_Ub : forall x, 0x10000 <= x -> x + 1 <= 0x12000 ->
  exists seg, find_segment Ubsan.M.loaded_segments x 1 = Some seg /\ seg_writable seg = false.
Proof.
  intros x H1 H2. exists Ubsan_segment_000.
  change Ubsan.M.loaded_segments with
    [Ubsan_segment_000; Ubsan_segment_001;
     Ubsan_segment_002; Ubsan_segment_003].
  cbn [find_segment].
  replace (Z.of_N (seg_base Ubsan_segment_000)) with 0x10000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Ubsan_segment_000)) with 0x2000 by (vm_compute; reflexivity).
  replace (0x10000 <=? x) with true by (symmetry; apply Z.leb_le; lia).
  replace (x + 1 <=? 0x10000 + 0x2000) with true by (symmetry; apply Z.leb_le; lia).
  cbn [andb]. split; [reflexivity|]. vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem writable_rodata_apart_S1 : forall mem lo n rlo rhi,
    0x10000 <= rlo -> rlo < rhi -> rhi <= 0x12000 ->
    writable Plain.M.loaded_segments mem lo n -> rodata_clear mem rlo rhi ->
    lo + n <= rlo \/ rhi <= lo.
Proof. exact (writable_rodata_apart _ seg0_S1). Qed.

Theorem writable_rodata_apart_Ub : forall mem lo n rlo rhi,
    0x10000 <= rlo -> rlo < rhi -> rhi <= 0x12000 ->
    writable Ubsan.M.loaded_segments mem lo n -> rodata_clear mem rlo rhi ->
    lo + n <= rlo \/ rhi <= lo.
Proof. exact (writable_rodata_apart _ seg0_Ub). Qed.
