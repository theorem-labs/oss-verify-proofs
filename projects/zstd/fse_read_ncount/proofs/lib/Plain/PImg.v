(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Image.
From OSSVerify.zstd.fse_read_ncount.images Require Export Plain.
Import ListNotations.
Open Scope Z_scope.
Definition psegs : list Segment := Plain.M.loaded_segments.
Definition p_init_pc : N := Plain.M.init_pc.
Definition p_phdrs : PhdrInfo := Plain.M.phdrs.
Lemma segments_reserved_plain :
segments_reserved psegs =
[(Z_to_bv 64 0x10000, Z_to_bv 64 0x2000); (Z_to_bv 64 0x12000, Z_to_bv 64 0xb000);
(Z_to_bv 64 0x1d000, Z_to_bv 64 0x1000); (Z_to_bv 64 0x1e000, Z_to_bv 64 0x32000)].
Proof. vm_compute. reflexivity. Qed.
Lemma reserved_top_plain : reserved_top (segments_reserved psegs) = 0x50000.
Proof. vm_compute. reflexivity. Qed.
Lemma ref_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x50000 <= z) ->
find_segment psegs z n = None.
Proof.
intros z n Hn Hz. unfold psegs, Plain.M.loaded_segments, Plain_loaded_segments. cbn [find_segment].
replace (Z.of_N (seg_base Plain_segment_000)) with 0x10000 by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Plain_segment_000)) with 0x2000 by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Plain_segment_001)) with 0x12000 by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Plain_segment_001)) with 0xb000 by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Plain_segment_002)) with 0x1d000 by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Plain_segment_002)) with 0x1000 by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Plain_segment_003)) with 0x1e000 by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Plain_segment_003)) with 0x32000 by (vm_compute; reflexivity).
Local Ltac2 Set LiaHints.tbl := fun () => "00@0>27422229304.1227422229433.1227422261439.1234226853944.1034226853944.8 34226854073.6 34226854073.8 34226854202.6 34226854847.1034226886841.1034226886970.8 34233186150.6 64619634699.1264619635342.6 64619635469.8 64619635596.1000000900H00U00^00m01701@01A01P01]01i01j02902E02T02cS2Hn1l2l2S2Hz2n02n31l2n4S2Hn2Hz2l12l2S2Hn1l2l1S2Hz2n02n11l2n2S2Hz2n02n1S2Hn1l2l0FS2Hz2n02n21l2n3S2Hn2Hz2l02l1S2Hn2Hz1l2l0FS2Hn2Hz2l22l31lS2Hn2Hz1l2l0S2Hn2Hz2l02l11lS2Hn2Hz2l12l21l".
destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x2000)); cbn [andb]; try lia;
destruct (Z.leb_spec0 0x12000 z); destruct (Z.leb_spec0 (z + n) (0x12000 + 0xb000)); cbn [andb]; try lia;
destruct (Z.leb_spec0 0x1d000 z); destruct (Z.leb_spec0 (z + n) (0x1d000 + 0x1000)); cbn [andb]; try lia;
destruct (Z.leb_spec0 0x1e000 z); destruct (Z.leb_spec0 (z + n) (0x1e000 + 0x32000)); cbn [andb]; try lia; reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma ref_ro_addr_false : forall x : word,
(bv_unsigned x + 1 <= 0x10000 \/ 0x50000 <= bv_unsigned x)%Z -> ro_addr psegs x = false.
Proof. intros x Hx. unfold ro_addr. Local Ltac2 Set LiaHints.tbl := fun () => "0020=43608362722.254494461928.2000001005SS2Hx".
rewrite ref_find_segment_none by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma ref_memory_read_none : forall (x : word) n,
(1 <= Z.of_N n)%Z -> (bv_unsigned x + Z.of_N n <= 0x10000 \/ 0x50000 <= bv_unsigned x)%Z -> memory_read psegs x n = None.
Proof. intros x n Hn Hx. unfold memory_read. Local Ltac2 Set LiaHints.tbl := fun () => "0020=38070919460.444896374254.4000004008S2HnS2Hx".
rewrite ref_find_segment_none by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma ref_wview_overlay : forall m (x : word),
(bv_unsigned x + 1 <= 0x10000 \/ 0x50000 <= bv_unsigned x)%Z -> wview psegs m x = m x.
Proof.
intros m x Hx. unfold wview. destruct (m x); [reflexivity|]. Local Ltac2 Set LiaHints.tbl := fun () => "0020=43608362722.354494461928.3000001005SS2Hx".
rewrite ref_find_segment_none by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma ref_seg_rom_none : forall (x : word),
(bv_unsigned x + 1 <= 0x10000 \/ 0x50000 <= bv_unsigned x)%Z -> seg_rom psegs x = None.
Proof. intros x Hx. unfold seg_rom. Local Ltac2 Set LiaHints.tbl := fun () => "0020=43608362722.254494461928.2000001005SS2Hx".
rewrite ref_memory_read_none by (cbn; lia). reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma ref_mrd_overlay : forall m (x : word),
(bv_unsigned x + 1 <= 0x10000 \/ 0x50000 <= bv_unsigned x)%Z -> mrd psegs m x = m x.
Proof. intros m x Hx. unfold mrd. destruct (m x); [reflexivity|]. apply ref_seg_rom_none. exact Hx. Qed.
Definition RPAGE_SIZE : Z := 0x4ef00.
Definition PREAD_STAGE : Z := 0x1eb39.
Definition RAUXV_CELL : Z := 0x4eed8.
Definition rmmap_entry : Z := 0x1687c.
Definition rmunmap_entry : Z := 0x169b0.
Definition rmprotect_entry : Z := 0x16968.
