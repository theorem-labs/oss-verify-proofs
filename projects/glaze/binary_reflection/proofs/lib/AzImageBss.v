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
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanHexScan OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanHexScan OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Export AzZScan.   (* [comment removed for export] *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AzImageBss1 AzImageBss2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition BSS_LO : Z := 0x103ea0.
Definition BSS_HI : Z := 0x65d000.
Lemma asan_bss_scan : zscanN Asan_seg_bytes_003 64 0x2ea0 (0x55c000 - 0x2ea0) = true.
Proof.   (* [comment removed for export] *)
  apply (zscanN_split _ 63 0x2ea0%N (0x55c000 - 0x2ea0)%N 2803888%N); [lia | reflexivity | exact asan_bss_scan1 | exact asan_bss_scan2].
Qed.
Lemma asan_len3 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_003) / 2) = 0x55c000%N.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_bss_zero : forall x : word,
  BSS_LO <= bv_unsigned x < BSS_HI -> seg_rom ASEGS x = Some (Z_to_bv 8 0).
Proof.
  intros x [Hlo Hhi]. unfold BSS_LO, BSS_HI in *. unfold seg_rom, memory_read.
  replace (find_segment ASEGS (bv_unsigned x) (Z.of_N 1)) with (Some Asan_segment_003).
  2:{ unfold ASEGS, Asan_loaded_segments.
      cbn [find_segment Asan_segment_000 Asan_segment_001
           Asan_segment_002 Asan_segment_003 seg_base seg_size].
      replace (bv_unsigned x + Z.of_N 1 <=? Z.of_N 65536 + Z.of_N 237568) with false by (symmetry; apply Z.leb_gt; lia).
      replace (bv_unsigned x + Z.of_N 1 <=? Z.of_N 303104 + Z.of_N 724992) with false by (symmetry; apply Z.leb_gt; lia).
      replace (bv_unsigned x + Z.of_N 1 <=? Z.of_N 1028096 + Z.of_N 24576) with false by (symmetry; apply Z.leb_gt; lia).
      rewrite !andb_false_r.
      replace (Z.of_N 1052672 <=? bv_unsigned x) with true by (symmetry; apply Z.leb_le; lia).
      replace (bv_unsigned x + Z.of_N 1 <=? Z.of_N 1052672 + Z.of_N 5619712) with true by (symmetry; apply Z.leb_le; lia).
      reflexivity. }
  cbn [seg_readable seg_perms Asan_segment_003 string_has Ascii.eqb seg_bytes seg_base N.to_nat Pos.to_nat Pos.iter_op segment_read_bytes orb].
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes segment_byte_at].
  replace (Z.to_N (bv_unsigned x - Z.of_N 1052672) <? Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_003) / 2))%N
    with true by (symmetry; apply N.ltb_lt; rewrite asan_len3; lia).
  pose proof (zscanN_sound _ _ _ _ asan_bss_scan (Z.to_N (bv_unsigned x - Z.of_N 1052672) - 0x2ea0)%N ltac:(lia)) as Z0.
  replace (0x2ea0 + (Z.to_N (bv_unsigned x - Z.of_N 1052672) - 0x2ea0))%N with (Z.to_N (bv_unsigned x - Z.of_N 1052672)) in Z0 by lia.
  rewrite Z0. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma w_succ' : forall a, 0 <= a -> a + 1 < 2 ^ 64 -> (Z_to_bv 64 a + 1)%bv = Z_to_bv 64 (a + 1).
Proof.
  intros a H0 H1. apply bv_eq. rewrite bv_add_unsigned, !u64_lit by lia.
  change (bv_unsigned (1 : bv 64)) with 1. unfold bv_wrap. apply Z.mod_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
Lemma bss_rdn_zero : forall M n a,
  BSS_LO <= a -> a + Z.of_nat n <= BSS_HI ->
  (forall i, a <= i < a + Z.of_nat n -> M (Z_to_bv 64 i) = None) ->
  rdn ASEGS M (Z_to_bv 64 a) n = Some (repeat (Z_to_bv 8 0) n).
Proof.
  intros M n. induction n as [|n IH]; intros a Hlo Hhi HN.
  - cbn. reflexivity.
  - cbn [rdn repeat]. rewrite (HN a) by lia.
    rewrite asan_bss_zero by (unfold BSS_LO, BSS_HI in *; rewrite u64_lit by lia; lia).
    unfold BSS_LO, BSS_HI in *.
    rewrite w_succ' by lia. rewrite (IH (a + 1)); [reflexivity | lia | lia | intros i Hi; apply HN; lia].
Qed.
