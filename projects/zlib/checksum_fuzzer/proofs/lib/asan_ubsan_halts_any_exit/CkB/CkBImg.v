(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import PropExec MState Mem Image.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.World Require Export Tgt_checksum_fuzzer_both.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import ExecF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition asegs : list Segment := Tgt_checksum_fuzzer_both.M.loaded_segments.
Definition a_init_pc : N := Tgt_checksum_fuzzer_both.M.init_pc.
Definition a_phdrs : PhdrInfo := Tgt_checksum_fuzzer_both.M.phdrs.

Definition a_ro_lo   : Z := 0x10000.   Definition a_ro_hi   : Z := 0x31000.
Definition a_text_lo : Z := 0x31000.   Definition a_text_hi : Z := 0x99000.
Definition a_rw1_lo  : Z := 0x99000.   Definition a_rw1_hi  : Z := 0x9b000.
Definition a_rw2_lo  : Z := 0x9b000.   Definition a_rw2_hi  : Z := 0x5f7000.
Definition AIMG_TOP : Z := 0x5f7000.

Definition asan_reserved : list (Z * Z) :=
  [(0x10000, 0x21000); (0x31000, 0x68000); (0x99000, 0x2000); (0x9b000, 0x55c000)].

Lemma reservedZ_asan : reservedZ asegs = asan_reserved.
Proof. vm_compute. reflexivity. Qed.

Lemma segments_reserved_asan :
  segments_reserved asegs =
  [(Z_to_bv 64 0x10000, Z_to_bv 64 0x21000); (Z_to_bv 64 0x31000, Z_to_bv 64 0x68000);
   (Z_to_bv 64 0x99000, Z_to_bv 64 0x2000); (Z_to_bv 64 0x9b000, Z_to_bv 64 0x55c000)].
Proof. vm_compute. reflexivity. Qed.

Lemma reserved_top_asan : reserved_top (segments_reserved asegs) = 0x5f7000.
Proof. vm_compute. reflexivity. Qed.

Lemma a_seg_flags :
  map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_readable s, seg_writable s, seg_executable s)) asegs
  = [(0x10000, 0x21000, true, false, false); (0x31000, 0x68000, true, false, true);
     (0x99000, 0x2000, true, true, false); (0x9b000, 0x55c000, true, true, false)].
Proof. vm_compute. reflexivity. Qed.

Lemma a_find_segment_1 : forall z, 0 <= z ->
  find_segment asegs z 1 =
    if (0x10000 <=? z) && (z + 1 <=? 0x31000) then Some Tgt_checksum_fuzzer_both_segment_000
    else if (0x31000 <=? z) && (z + 1 <=? 0x99000) then Some Tgt_checksum_fuzzer_both_segment_001
    else if (0x99000 <=? z) && (z + 1 <=? 0x9b000) then Some Tgt_checksum_fuzzer_both_segment_002
    else if (0x9b000 <=? z) && (z + 1 <=? 0x5f7000) then Some Tgt_checksum_fuzzer_both_segment_003
    else None.
Proof. intros z Hz. reflexivity. Qed.

Lemma a_ro_addr : forall a : word,
  ro_addr asegs a = ((0x10000 <=? bv_unsigned a) && (bv_unsigned a <? 0x99000))%bool.
Proof.
  intros a. unfold ro_addr. rewrite a_find_segment_1 by (pose proof (bv_unsigned_in_range 64 a); lia).
  pose proof (bv_unsigned_in_range 64 a) as R.
  destruct (Z.leb_spec0 0x10000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x31000);
  destruct (Z.leb_spec0 0x31000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x99000);
  destruct (Z.leb_spec0 0x99000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x9b000);
  destruct (Z.leb_spec0 0x9b000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x5f7000);
  destruct (Z.ltb_spec0 (bv_unsigned a) 0x99000); cbn; try reflexivity; lia.
Qed.


Lemma ref_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x5f7000 <= z) ->
  find_segment asegs z n = None.
Proof.
  intros z n Hn Hz. unfold asegs, Tgt_checksum_fuzzer_both.M.loaded_segments, Tgt_checksum_fuzzer_both_loaded_segments. cbn [find_segment].
  replace (Z.of_N (seg_base Tgt_checksum_fuzzer_both_segment_000)) with 0x10000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Tgt_checksum_fuzzer_both_segment_000)) with 0x21000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Tgt_checksum_fuzzer_both_segment_001)) with 0x31000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Tgt_checksum_fuzzer_both_segment_001)) with 0x68000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Tgt_checksum_fuzzer_both_segment_002)) with 0x99000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Tgt_checksum_fuzzer_both_segment_002)) with 0x2000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Tgt_checksum_fuzzer_both_segment_003)) with 0x9b000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Tgt_checksum_fuzzer_both_segment_003)) with 0x55c000 by (vm_compute; reflexivity).
  destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x21000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0x31000 z); destruct (Z.leb_spec0 (z + n) (0x31000 + 0x68000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0x99000 z); destruct (Z.leb_spec0 (z + n) (0x99000 + 0x2000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0x9b000 z); destruct (Z.leb_spec0 (z + n) (0x9b000 + 0x55c000)); cbn [andb]; try lia; reflexivity.
Qed.

Lemma ref_ro_addr_false : forall x : word,
  (bv_unsigned x + 1 <= 0x10000 \/ 0x5f7000 <= bv_unsigned x)%Z -> ro_addr asegs x = false.
Proof. intros x Hx. unfold ro_addr. rewrite ref_find_segment_none by lia. reflexivity. Qed.

Lemma ref_memory_read_none : forall (x : word) n,
  (1 <= Z.of_N n)%Z -> (bv_unsigned x + Z.of_N n <= 0x10000 \/ 0x5f7000 <= bv_unsigned x)%Z -> memory_read asegs x n = None.
Proof. intros x n Hn Hx. unfold memory_read. rewrite ref_find_segment_none by lia. reflexivity. Qed.

Lemma ref_wview_overlay : forall m (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x5f7000 <= bv_unsigned x)%Z -> wview asegs m x = m x.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [reflexivity|]. rewrite ref_find_segment_none by lia. reflexivity.
Qed.

Lemma ref_seg_rom_none : forall (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x5f7000 <= bv_unsigned x)%Z -> seg_rom asegs x = None.
Proof. intros x Hx. unfold seg_rom. rewrite ref_memory_read_none by (cbn; lia). reflexivity. Qed.

Lemma ref_mrd_overlay : forall m (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x5f7000 <= bv_unsigned x)%Z -> mrd asegs m x = m x.
Proof. intros m x Hx. unfold mrd. destruct (m x); [reflexivity|]. apply ref_seg_rom_none. exact Hx. Qed.

Notation rng_aimg RNG := (rng RNG 0x10000 0x5e7000).

Definition ACK_FUZZ      : Z := 0x8049c.
Definition ACK_CRC32Z    : Z := 0x80890.
Definition ACK_CRC32     : Z := 0x81ac4.
Definition ACK_COMBINE   : Z := 0x81c48.
Definition ACK_GEN       : Z := 0x81ad0.
Definition ACK_OP        : Z := 0x81bd4.
Definition ACK_ADLER32Z  : Z := 0x81da4.
Definition ACK_ADLER32   : Z := 0x828a8.
Definition ACK_ADLCOMB   : Z := 0x828b4.
Definition ACK_REPORT_LOAD1 : Z := 0x58700.
Definition ACK_REPORT_LOAD4 : Z := 0x58840.
Definition ACK_ASSERT_FAIL  : Z := 0x891e0.
