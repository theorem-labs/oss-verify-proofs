(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Image.
From OSSVerify.zstd.zstd_frame_info.images Require Export Plain.
Import ListNotations.
Open Scope Z_scope.

Definition psegs : list Segment := Plain.M.loaded_segments.
Definition p_init_pc : N := Plain.M.init_pc.
Definition p_phdrs : PhdrInfo := Plain.M.phdrs.

(* [comment removed for export] *)
Definition p_ro_lo   : Z := 0x10000.  Definition p_ro_hi   : Z := 0x12000.
Definition p_text_lo : Z := 0x12000.  Definition p_text_hi : Z := 0x1c000.
Definition p_rw1_lo  : Z := 0x1c000.  Definition p_rw1_hi  : Z := 0x1d000.
Definition p_rw2_lo  : Z := 0x1d000.  Definition p_rw2_hi  : Z := 0x4f000.

(* [comment removed for export] *)
Definition plain_reserved : list (Z * Z) :=
  [(0x10000, 0x2000); (0x12000, 0xa000); (0x1c000, 0x1000); (0x1d000, 0x32000)].

Lemma reservedZ_plain : reservedZ psegs = plain_reserved.
Proof. vm_compute. reflexivity. Qed.

Lemma segments_reserved_plain :
  segments_reserved psegs =
  [(Z_to_bv 64 0x10000, Z_to_bv 64 0x2000); (Z_to_bv 64 0x12000, Z_to_bv 64 0xa000);
   (Z_to_bv 64 0x1c000, Z_to_bv 64 0x1000); (Z_to_bv 64 0x1d000, Z_to_bv 64 0x32000)].
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma reserved_top_plain : reserved_top (segments_reserved psegs) = 0x4f000.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma p_seg_flags :
  map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_readable s, seg_writable s, seg_executable s)) psegs
  = [(0x10000, 0x2000, true, false, false); (0x12000, 0xa000, true, false, true);
     (0x1c000, 0x1000, true, true, false); (0x1d000, 0x32000, true, true, false)].
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma p_find_segment_1 : forall z, 0 <= z ->
  find_segment psegs z 1 =
    if (0x10000 <=? z) && (z + 1 <=? 0x12000) then Some Plain_segment_000
    else if (0x12000 <=? z) && (z + 1 <=? 0x1c000) then Some Plain_segment_001
    else if (0x1c000 <=? z) && (z + 1 <=? 0x1d000) then Some Plain_segment_002
    else if (0x1d000 <=? z) && (z + 1 <=? 0x4f000) then Some Plain_segment_003
    else None.
Proof. intros z Hz. reflexivity. Qed.

(* [comment removed for export] *)
Lemma p_ro_addr : forall a : word,
  ro_addr psegs a = ((0x10000 <=? bv_unsigned a) && (bv_unsigned a <? 0x1c000))%bool.
Proof.
  intros a. unfold ro_addr. rewrite p_find_segment_1 by (pose proof (bv_unsigned_in_range 64 a); lia).
  pose proof (bv_unsigned_in_range 64 a) as R.
  destruct (Z.leb_spec0 0x10000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x12000);
  destruct (Z.leb_spec0 0x12000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x1c000);
  destruct (Z.leb_spec0 0x1c000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x1d000);
  destruct (Z.leb_spec0 0x1d000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x4f000);
  destruct (Z.ltb_spec0 (bv_unsigned a) 0x1c000); cbn; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ref_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x4f000 <= z) ->
  find_segment psegs z n = None.
Proof.
  intros z n Hn Hz. unfold psegs, Plain.M.loaded_segments, Plain_loaded_segments. cbn [find_segment].
  replace (Z.of_N (seg_base Plain_segment_000)) with 0x10000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Plain_segment_000)) with 0x2000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Plain_segment_001)) with 0x12000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Plain_segment_001)) with 0xa000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Plain_segment_002)) with 0x1c000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Plain_segment_002)) with 0x1000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Plain_segment_003)) with 0x1d000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Plain_segment_003)) with 0x32000 by (vm_compute; reflexivity).
  Local Ltac2 Set LiaHints.tbl := fun () => "00@0>27422229304.1227422229433.1227422261439.1234226853944.1034226853944.8 34226854073.6 34226854073.8 34226854202.6 34226854847.1034226886841.1034226886970.8 34233186150.6 64619634699.1264619635342.6 64619635469.8 64619635596.1000000900F00P00Y00f01001901:01G01Q01[01\01n02:02L02^S2Hn1l2l2S2Hz2n02n32n4S2Hz2n02n3S2Hn1l2l1S2Hz2n02n12n2S2Hz2n02n1S2Hn1l2l0FS2Hz2n02n22n3S2Hz2n02n2S2Hz2n02n1FS2Hn2Hz2n02l31l2l2S2Hn2Hz1l2l0S2Hn2Hz2n02l11l2l0S2Hn2Hz2n02l21l2l1".
destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x2000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0x12000 z); destruct (Z.leb_spec0 (z + n) (0x12000 + 0xa000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0x1c000 z); destruct (Z.leb_spec0 (z + n) (0x1c000 + 0x1000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0x1d000 z); destruct (Z.leb_spec0 (z + n) (0x1d000 + 0x32000)); cbn [andb]; try lia; reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma ref_ro_addr_false : forall x : word,
  (bv_unsigned x + 1 <= 0x10000 \/ 0x4f000 <= bv_unsigned x)%Z -> ro_addr psegs x = false.
Proof. intros x Hx. unfold ro_addr. rewrite ref_find_segment_none by lia. reflexivity. Qed.

Lemma ref_memory_read_none : forall (x : word) n,
  (1 <= Z.of_N n)%Z -> (bv_unsigned x + Z.of_N n <= 0x10000 \/ 0x4f000 <= bv_unsigned x)%Z -> memory_read psegs x n = None.
Proof. intros x n Hn Hx. unfold memory_read. rewrite ref_find_segment_none by lia. reflexivity. Qed.

Lemma ref_wview_overlay : forall m (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x4f000 <= bv_unsigned x)%Z -> wview psegs m x = m x.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [reflexivity|]. rewrite ref_find_segment_none by lia. reflexivity.
Qed.

Lemma ref_seg_rom_none : forall (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x4f000 <= bv_unsigned x)%Z -> seg_rom psegs x = None.
Proof. intros x Hx. unfold seg_rom. rewrite ref_memory_read_none by (cbn; lia). reflexivity. Qed.

Lemma ref_mrd_overlay : forall m (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x4f000 <= bv_unsigned x)%Z -> mrd psegs m x = m x.
Proof. intros m x Hx. unfold mrd. destruct (m x); [reflexivity|]. apply ref_seg_rom_none. exact Hx. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RPAGE_SIZE : Z := 0x4e0f8.    (* [comment removed for export] *)
Definition PREAD_STAGE : Z := 0x1dd39.   (* [comment removed for export] *)
Definition RAUXV_CELL : Z := 0x4e0d0.    (* [comment removed for export] *)
Definition rmmap_entry : Z := 0x15b54.
Definition rmunmap_entry : Z := 0x15c88.
Definition rmprotect_entry : Z := 0x15c40.
