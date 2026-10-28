(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export UEQM.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Definition RIMG_LO : Z := 0x10000.
Definition RIMG_HI : Z := 0x99000.
Definition RDATA_LO : Z := 0x62000.

Definition RCTX : Z := 0x97f80.
Definition RMLOCK : Z := 0x97f78.
Definition RLIBC : Z := 0x97e90.
Definition RNEED_LOCKS : Z := 0x97e93.
Definition RPAGE_SIZE : Z := 0x97ec0.
Definition RAUXV_CELL : Z := 0x97e98.
Definition RSIZE_CLASSES : Z := 0x16540.
Definition RDEBRUIJN : Z := 0x16520.
Definition RSMALL_CNT : Z := 0x165a0.
Definition RMED_CNT : Z := 0x165bb.
Definition RGOT_SSP : Z := 0x659d0.
Definition RSSP_GUARD : Z := 0x97e70.
Definition RATP : Z := 0x77c00.
Definition RERRNO : Z := 0x77b5c.

Definition rerrno_loc_entry : Z := 0x50b60.
Definition rsysret_entry : Z := 0x5102c.
Definition rcalloc_entry : Z := 0x51f7c.
Definition rfree_sym : Z := 0x520b4.
Definition rmalloc_sym : Z := 0x521f4.
Definition rfree_entry : Z := 0x524d8.
Definition rget_meta_entry : Z := 0x526a4.
Definition rnontrivial_free_entry : Z := 0x527b4.
Definition ralloc_meta_entry : Z := 0x52b8c.
Definition rmalloc_entry : Z := 0x52e64.
Definition ralloc_slot_entry : Z := 0x531d4.
Definition renframe_entry : Z := 0x53a78.
Definition ris_allzero_entry : Z := 0x53bc8.
Definition rrealloc_entry : Z := 0x53d44.
Definition rvm_wait_entry : Z := 0x54208.
Definition rmmap_entry : Z := 0x5420c.
Definition rmprotect_entry : Z := 0x542f8.
Definition rmremap_entry : Z := 0x54340.
Definition rmunmap_entry : Z := 0x54414.
Definition rlock_entry : Z := 0x60550.
Definition runlock_entry : Z := 0x607d8.

Definition ref_reserved : list (Z * Z) := [(0x10000, 0x10000); (0x20000, 0x42000); (0x62000, 0x4000); (0x66000, 0x33000)].

Lemma ref_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x99000 <= z) ->
find_segment rsegs z n = None.
Proof.
intros z n Hn Hz. unfold rsegs, Ubsan.M.loaded_segments, Ubsan.Ubsan_loaded_segments. cbn [find_segment].
replace (Z.of_N (seg_base Ubsan.Ubsan_segment_000)) with 0x10000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Ubsan.Ubsan_segment_000)) with 0x10000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Ubsan.Ubsan_segment_001)) with 0x20000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Ubsan.Ubsan_segment_001)) with 0x42000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Ubsan.Ubsan_segment_002)) with 0x62000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Ubsan.Ubsan_segment_002)) with 0x4000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Ubsan.Ubsan_segment_003)) with 0x66000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Ubsan.Ubsan_segment_003)) with 0x33000%Z by (vm_compute; reflexivity).
destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x10000)); cbn [andb]; try lia.
all: destruct (Z.leb_spec0 0x20000 z); destruct (Z.leb_spec0 (z + n) (0x20000 + 0x42000)); cbn [andb]; try lia.
all: destruct (Z.leb_spec0 0x62000 z); destruct (Z.leb_spec0 (z + n) (0x62000 + 0x4000)); cbn [andb]; try lia.
all: destruct (Z.leb_spec0 0x66000 z); destruct (Z.leb_spec0 (z + n) (0x66000 + 0x33000)); cbn [andb]; try lia.
all: reflexivity.
Qed.

Lemma ref_ro_addr_false : forall x : word,
(bv_unsigned x + 1 <= 0x10000 \/ 0x99000 <= bv_unsigned x)%Z -> ro_addr rsegs x = false.
Proof. intros x Hx. unfold ro_addr. rewrite ref_find_segment_none by lia. reflexivity. Qed.

Lemma ref_memory_read_none : forall (x : word) n,
(1 <= Z.of_N n)%Z -> (bv_unsigned x + Z.of_N n <= 0x10000 \/ 0x99000 <= bv_unsigned x)%Z -> memory_read rsegs x n = None.
Proof. intros x n Hn Hx. unfold memory_read. rewrite ref_find_segment_none by lia. reflexivity. Qed.

Lemma ref_wview_overlay : forall m (x : word),
(bv_unsigned x + 1 <= 0x10000 \/ 0x99000 <= bv_unsigned x)%Z -> wview rsegs m x = m x.
Proof.
intros m x Hx. unfold wview. destruct (m x); [reflexivity|]. rewrite ref_find_segment_none by lia. reflexivity.
Qed.

Lemma ref_seg_rom_none : forall (x : word),
(bv_unsigned x + 1 <= 0x10000 \/ 0x99000 <= bv_unsigned x)%Z -> seg_rom rsegs x = None.
Proof. intros x Hx. unfold seg_rom. rewrite ref_memory_read_none by (cbn; lia). reflexivity. Qed.

Lemma ref_mrd_overlay : forall m (x : word),
(bv_unsigned x + 1 <= 0x10000 \/ 0x99000 <= bv_unsigned x)%Z -> mrd rsegs m x = m x.
Proof. intros m x Hx. unfold mrd. destruct (m x); [reflexivity|]. apply ref_seg_rom_none. exact Hx. Qed.
