(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import PropExec MState Mem Image.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.World Require Export Src_zlib_zlib_uncompress_fuzzer_repro.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition psegs : list Segment := Src_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments.
Definition p_init_pc : N := Src_zlib_zlib_uncompress_fuzzer_repro.M.init_pc.
Definition p_phdrs : PhdrInfo := Src_zlib_zlib_uncompress_fuzzer_repro.M.phdrs.

Definition p_ro_lo   : Z := 0x10000.  Definition p_ro_hi   : Z := 0x14000.
Definition p_text_lo : Z := 0x14000.  Definition p_text_hi : Z := 0x21000.
Definition p_rw1_lo  : Z := 0x21000.  Definition p_rw1_hi  : Z := 0x22000.
Definition p_rw2_lo  : Z := 0x22000.  Definition p_rw2_hi  : Z := 0x94000.

Definition plain_reserved : list (Z * Z) :=
  [(0x10000, 0x4000); (0x14000, 0xd000); (0x21000, 0x1000); (0x22000, 0x72000)].

Lemma reservedZ_plain : reservedZ psegs = plain_reserved.
Proof. vm_compute. reflexivity. Qed.

Lemma segments_reserved_plain :
  segments_reserved psegs =
  [(Z_to_bv 64 0x10000, Z_to_bv 64 0x4000); (Z_to_bv 64 0x14000, Z_to_bv 64 0xd000);
   (Z_to_bv 64 0x21000, Z_to_bv 64 0x1000); (Z_to_bv 64 0x22000, Z_to_bv 64 0x72000)].
Proof. vm_compute. reflexivity. Qed.

Lemma reserved_top_plain : reserved_top (segments_reserved psegs) = 0x94000.
Proof. vm_compute. reflexivity. Qed.

Lemma p_seg_flags :
  map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_readable s, seg_writable s, seg_executable s)) psegs
  = [(0x10000, 0x4000, true, false, false); (0x14000, 0xd000, true, false, true);
     (0x21000, 0x1000, true, true, false); (0x22000, 0x72000, true, true, false)].
Proof. vm_compute. reflexivity. Qed.

Lemma p_find_segment_1 : forall z, 0 <= z ->
  find_segment psegs z 1 =
    if (0x10000 <=? z) && (z + 1 <=? 0x14000) then Some Src_zlib_zlib_uncompress_fuzzer_repro_segment_000
    else if (0x14000 <=? z) && (z + 1 <=? 0x21000) then Some Src_zlib_zlib_uncompress_fuzzer_repro_segment_001
    else if (0x21000 <=? z) && (z + 1 <=? 0x22000) then Some Src_zlib_zlib_uncompress_fuzzer_repro_segment_002
    else if (0x22000 <=? z) && (z + 1 <=? 0x94000) then Some Src_zlib_zlib_uncompress_fuzzer_repro_segment_003
    else None.
Proof. intros z Hz. reflexivity. Qed.

Lemma p_ro_addr : forall a : word,
  ro_addr psegs a = ((0x10000 <=? bv_unsigned a) && (bv_unsigned a <? 0x21000))%bool.
Proof.
  intros a. unfold ro_addr. rewrite p_find_segment_1 by (pose proof (bv_unsigned_in_range 64 a); lia).
  pose proof (bv_unsigned_in_range 64 a) as R.
  destruct (Z.leb_spec0 0x10000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x14000);
  destruct (Z.leb_spec0 0x14000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x21000);
  destruct (Z.leb_spec0 0x21000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x22000);
  destruct (Z.leb_spec0 0x22000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x94000);
  destruct (Z.ltb_spec0 (bv_unsigned a) 0x21000); cbn; try reflexivity; lia.
Qed.


Lemma ref_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x94000 <= z) ->
  find_segment psegs z n = None.
Proof.
  intros z n Hn Hz. unfold psegs, Src_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments, Src_zlib_zlib_uncompress_fuzzer_repro_loaded_segments. cbn [find_segment].
  replace (Z.of_N (seg_base Src_zlib_zlib_uncompress_fuzzer_repro_segment_000)) with 0x10000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Src_zlib_zlib_uncompress_fuzzer_repro_segment_000)) with 0x4000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Src_zlib_zlib_uncompress_fuzzer_repro_segment_001)) with 0x14000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Src_zlib_zlib_uncompress_fuzzer_repro_segment_001)) with 0xd000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Src_zlib_zlib_uncompress_fuzzer_repro_segment_002)) with 0x21000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Src_zlib_zlib_uncompress_fuzzer_repro_segment_002)) with 0x1000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Src_zlib_zlib_uncompress_fuzzer_repro_segment_003)) with 0x22000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Src_zlib_zlib_uncompress_fuzzer_repro_segment_003)) with 0x72000 by (vm_compute; reflexivity).
  destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x4000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0x14000 z); destruct (Z.leb_spec0 (z + n) (0x14000 + 0xd000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0x21000 z); destruct (Z.leb_spec0 (z + n) (0x21000 + 0x1000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0x22000 z); destruct (Z.leb_spec0 (z + n) (0x22000 + 0x72000)); cbn [andb]; try lia; reflexivity.
Qed.

Lemma ref_ro_addr_false : forall x : word,
  (bv_unsigned x + 1 <= 0x10000 \/ 0x94000 <= bv_unsigned x)%Z -> ro_addr psegs x = false.
Proof. intros x Hx. unfold ro_addr. rewrite ref_find_segment_none by lia. reflexivity. Qed.

Lemma ref_memory_read_none : forall (x : word) n,
  (1 <= Z.of_N n)%Z -> (bv_unsigned x + Z.of_N n <= 0x10000 \/ 0x94000 <= bv_unsigned x)%Z -> memory_read psegs x n = None.
Proof. intros x n Hn Hx. unfold memory_read. rewrite ref_find_segment_none by lia. reflexivity. Qed.

Lemma ref_wview_overlay : forall m (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x94000 <= bv_unsigned x)%Z -> wview psegs m x = m x.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [reflexivity|]. rewrite ref_find_segment_none by lia. reflexivity.
Qed.

Lemma ref_seg_rom_none : forall (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x94000 <= bv_unsigned x)%Z -> seg_rom psegs x = None.
Proof. intros x Hx. unfold seg_rom. rewrite ref_memory_read_none by (cbn; lia). reflexivity. Qed.

Lemma ref_mrd_overlay : forall m (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x94000 <= bv_unsigned x)%Z -> mrd psegs m x = m x.
Proof. intros m x Hx. unfold mrd. destruct (m x); [reflexivity|]. apply ref_seg_rom_none. exact Hx. Qed.

Definition RPAGE_SIZE : Z := 0x93218.
Definition PREAD_STAGE : Z := 0x22e59.
Definition RAUXV_CELL : Z := 0x931f0.
Definition rmmap_entry : Z := 0x1ac70.
Definition rmunmap_entry : Z := 0x1ada4.
Definition rmprotect_entry : Z := 0x1ad5c.
