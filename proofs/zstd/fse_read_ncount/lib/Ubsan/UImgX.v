(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Image.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Export UImg.
Import ListNotations.
Open Scope Z_scope.
Lemma ref_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x50000 <= z) ->
find_segment usegs z n = None.
Proof.
intros z n Hn Hz. unfold usegs, Ubsan.M.loaded_segments, Ubsan_loaded_segments. cbn [find_segment].
replace (Z.of_N (seg_base Ubsan_segment_000)) with 0x10000 by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Ubsan_segment_000)) with 0x2000 by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Ubsan_segment_001)) with 0x12000 by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Ubsan_segment_001)) with 0xb000 by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Ubsan_segment_002)) with 0x1d000 by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Ubsan_segment_002)) with 0x1000 by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Ubsan_segment_003)) with 0x1e000 by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Ubsan_segment_003)) with 0x32000 by (vm_compute; reflexivity).
destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x2000)); cbn [andb]; try lia;
destruct (Z.leb_spec0 0x12000 z); destruct (Z.leb_spec0 (z + n) (0x12000 + 0xb000)); cbn [andb]; try lia;
destruct (Z.leb_spec0 0x1d000 z); destruct (Z.leb_spec0 (z + n) (0x1d000 + 0x1000)); cbn [andb]; try lia;
destruct (Z.leb_spec0 0x1e000 z); destruct (Z.leb_spec0 (z + n) (0x1e000 + 0x32000)); cbn [andb]; try lia; reflexivity.
Qed.
Lemma ref_ro_addr_false : forall x : word,
(bv_unsigned x + 1 <= 0x10000 \/ 0x50000 <= bv_unsigned x)%Z -> ro_addr usegs x = false.
Proof. intros x Hx. unfold ro_addr. rewrite ref_find_segment_none by lia. reflexivity. Qed.
Lemma ref_memory_read_none : forall (x : word) n,
(1 <= Z.of_N n)%Z -> (bv_unsigned x + Z.of_N n <= 0x10000 \/ 0x50000 <= bv_unsigned x)%Z -> memory_read usegs x n = None.
Proof. intros x n Hn Hx. unfold memory_read. rewrite ref_find_segment_none by lia. reflexivity. Qed.
Lemma ref_wview_overlay : forall m (x : word),
(bv_unsigned x + 1 <= 0x10000 \/ 0x50000 <= bv_unsigned x)%Z -> wview usegs m x = m x.
Proof.
intros m x Hx. unfold wview. destruct (m x); [reflexivity|].
rewrite ref_find_segment_none by lia. reflexivity.
Qed.
Lemma ref_seg_rom_none : forall (x : word),
(bv_unsigned x + 1 <= 0x10000 \/ 0x50000 <= bv_unsigned x)%Z -> seg_rom usegs x = None.
Proof. intros x Hx. unfold seg_rom. rewrite ref_memory_read_none by (cbn; lia). reflexivity. Qed.
Lemma ref_mrd_overlay : forall m (x : word),
(bv_unsigned x + 1 <= 0x10000 \/ 0x50000 <= bv_unsigned x)%Z -> mrd usegs m x = m x.
Proof. intros m x Hx. unfold mrd. destruct (m x); [reflexivity|]. apply ref_seg_rom_none. exact Hx. Qed.
Definition RPAGE_SIZE : Z := 0x4f1f0.
Definition UREAD_STAGE : Z := 0x1ee29.
Definition RAUXV_CELL : Z := 0x4f1c8.
Definition rmmap_entry : Z := 0x16b64.
Definition rmunmap_entry : Z := 0x16c98.
Definition rmprotect_entry : Z := 0x16c50.
