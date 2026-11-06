(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanHexScan OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBss OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBssB1 OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBssB2. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanHexScan OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBss OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBssB1 OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBssB2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition BSS_LO_B : Z := 0x10ab00.
Definition BSS_HI_B : Z := 0x663000.
Lemma both_bss_scan : zscanN AsanUbsan_seg_bytes_003 64 0x3b00 (0x55c000 - 0x3b00) = true.
Proof.   (* [comment removed for export] *)
  apply (zscanN_split _ 63 0x3b00%N (0x55c000 - 0x3b00)%N 2802304%N); [lia | reflexivity | exact both_bss_scan1 | exact both_bss_scan2].
Qed.
Lemma both_len3 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_003) / 2) = 0x55c000%N.
Proof. vm_compute. reflexivity. Qed.

Lemma both_bss_zero : forall x : word,
  BSS_LO_B <= bv_unsigned x < BSS_HI_B -> seg_rom BSEGS x = Some (Z_to_bv 8 0).
Proof.
  intros x [Hlo Hhi]. unfold BSS_LO_B, BSS_HI_B in *. unfold seg_rom, memory_read.
  replace (find_segment BSEGS (bv_unsigned x) (Z.of_N 1)) with (Some AsanUbsan_segment_003).
  2:{ unfold BSEGS, AsanUbsan_loaded_segments.
      cbn [find_segment AsanUbsan_segment_000 AsanUbsan_segment_001
           AsanUbsan_segment_002 AsanUbsan_segment_003 seg_base seg_size].
      replace (bv_unsigned x + Z.of_N 1 <=? Z.of_N 65536 + Z.of_N 241664) with false by (symmetry; apply Z.leb_gt; lia).
      replace (bv_unsigned x + Z.of_N 1 <=? Z.of_N 307200 + Z.of_N 749568) with false by (symmetry; apply Z.leb_gt; lia).
      replace (bv_unsigned x + Z.of_N 1 <=? Z.of_N 1056768 + Z.of_N 20480) with false by (symmetry; apply Z.leb_gt; lia).
      rewrite !andb_false_r.
      replace (Z.of_N 1077248 <=? bv_unsigned x) with true by (symmetry; apply Z.leb_le; lia).
      replace (bv_unsigned x + Z.of_N 1 <=? Z.of_N 1077248 + Z.of_N 5619712) with true by (symmetry; apply Z.leb_le; lia).
      reflexivity. }
  cbn [seg_readable seg_perms AsanUbsan_segment_003 string_has Ascii.eqb seg_bytes seg_base N.to_nat Pos.to_nat Pos.iter_op segment_read_bytes orb].
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes segment_byte_at].
  replace (Z.to_N (bv_unsigned x - Z.of_N 1077248) <? Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_003) / 2))%N
    with true by (symmetry; apply N.ltb_lt; rewrite both_len3; lia).
  pose proof (zscanN_sound _ _ _ _ both_bss_scan (Z.to_N (bv_unsigned x - Z.of_N 1077248) - 0x3b00)%N ltac:(lia)) as Z0.
  replace (0x3b00 + (Z.to_N (bv_unsigned x - Z.of_N 1077248) - 0x3b00))%N with (Z.to_N (bv_unsigned x - Z.of_N 1077248)) in Z0 by lia.
  rewrite Z0. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma both_bss_rdn_zero : forall M n a,
  BSS_LO_B <= a -> a + Z.of_nat n <= BSS_HI_B ->
  (forall i, a <= i < a + Z.of_nat n -> M (Z_to_bv 64 i) = None) ->
  rdn BSEGS M (Z_to_bv 64 a) n = Some (repeat (Z_to_bv 8 0) n).
Proof.
  intros M n. induction n as [|n IH]; intros a Hlo Hhi HN.
  - cbn. reflexivity.
  - cbn [rdn repeat]. rewrite (HN a) by lia.
    rewrite both_bss_zero by (unfold BSS_LO_B, BSS_HI_B in *; rewrite u64_lit by lia; lia).
    unfold BSS_LO_B, BSS_HI_B in *.
    rewrite w_succ' by lia. rewrite (IH (a + 1)); [reflexivity | lia | lia | intros i Hi; apply HN; lia].
Qed.
