(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export QEQM.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Definition RIMG_LO : Z := 0x10000.
Definition RIMG_HI : Z := 0x97000.
Definition RDATA_LO : Z := 0x60000.

Definition RCTX : Z := 0x961f0.
Definition RMLOCK : Z := 0x961e8.
Definition RLIBC : Z := 0x96100.
Definition RNEED_LOCKS : Z := 0x96103.
Definition RPAGE_SIZE : Z := 0x96130.
Definition RAUXV_CELL : Z := 0x96108.
Definition RSIZE_CLASSES : Z := 0x16518.
Definition RDEBRUIJN : Z := 0x164f8.
Definition RSMALL_CNT : Z := 0x16578.
Definition RMED_CNT : Z := 0x16593.
Definition RGOT_SSP : Z := 0x63e88.
Definition RSSP_GUARD : Z := 0x960e0.
Definition RATP : Z := 0x75e70.
Definition RERRNO : Z := 0x75dcc.

Definition rerrno_loc_entry : Z := 0x4edd8.
Definition rsysret_entry : Z := 0x4f2a4.
Definition rcalloc_entry : Z := 0x501f4.
Definition rfree_sym : Z := 0x5032c.
Definition rmalloc_sym : Z := 0x5046c.
Definition rfree_entry : Z := 0x50750.
Definition rget_meta_entry : Z := 0x5091c.
Definition rnontrivial_free_entry : Z := 0x50a2c.
Definition ralloc_meta_entry : Z := 0x50e04.
Definition rmalloc_entry : Z := 0x510dc.
Definition ralloc_slot_entry : Z := 0x5144c.
Definition renframe_entry : Z := 0x51cf0.
Definition ris_allzero_entry : Z := 0x51e40.
Definition rrealloc_entry : Z := 0x51fbc.
Definition rvm_wait_entry : Z := 0x52480.
Definition rmmap_entry : Z := 0x52484.
Definition rmprotect_entry : Z := 0x52570.
Definition rmremap_entry : Z := 0x525b8.
Definition rmunmap_entry : Z := 0x5268c.
Definition rlock_entry : Z := 0x5e7c8.
Definition runlock_entry : Z := 0x5ea50.

Definition ref_reserved : list (Z * Z) := [(0x10000, 0x10000); (0x20000, 0x40000); (0x60000, 0x4000); (0x64000, 0x33000)].

Lemma ref_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x97000 <= z) ->
find_segment rsegs z n = None.
Proof.
intros z n Hn Hz. unfold rsegs, Plain.M.loaded_segments, Plain.Plain_loaded_segments. cbn [find_segment].
replace (Z.of_N (seg_base Plain.Plain_segment_000)) with 0x10000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Plain.Plain_segment_000)) with 0x10000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Plain.Plain_segment_001)) with 0x20000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Plain.Plain_segment_001)) with 0x40000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Plain.Plain_segment_002)) with 0x60000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Plain.Plain_segment_002)) with 0x4000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Plain.Plain_segment_003)) with 0x64000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Plain.Plain_segment_003)) with 0x33000%Z by (vm_compute; reflexivity).
destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x10000)); cbn [andb]; try lia.
all: destruct (Z.leb_spec0 0x20000 z); destruct (Z.leb_spec0 (z + n) (0x20000 + 0x40000)); cbn [andb]; try lia.
all: destruct (Z.leb_spec0 0x60000 z); destruct (Z.leb_spec0 (z + n) (0x60000 + 0x4000)); cbn [andb]; try lia.
all: destruct (Z.leb_spec0 0x64000 z); destruct (Z.leb_spec0 (z + n) (0x64000 + 0x33000)); cbn [andb]; try lia.
all: reflexivity.
Qed.

Lemma ref_ro_addr_false : forall x : word,
(bv_unsigned x + 1 <= 0x10000 \/ 0x97000 <= bv_unsigned x)%Z -> ro_addr rsegs x = false.
Proof. intros x Hx. unfold ro_addr. rewrite ref_find_segment_none by lia. reflexivity. Qed.

Lemma ref_memory_read_none : forall (x : word) n,
(1 <= Z.of_N n)%Z -> (bv_unsigned x + Z.of_N n <= 0x10000 \/ 0x97000 <= bv_unsigned x)%Z -> memory_read rsegs x n = None.
Proof. intros x n Hn Hx. unfold memory_read. rewrite ref_find_segment_none by lia. reflexivity. Qed.

Lemma ref_wview_overlay : forall m (x : word),
(bv_unsigned x + 1 <= 0x10000 \/ 0x97000 <= bv_unsigned x)%Z -> wview rsegs m x = m x.
Proof.
intros m x Hx. unfold wview. destruct (m x); [reflexivity|]. rewrite ref_find_segment_none by lia. reflexivity.
Qed.

Lemma ref_seg_rom_none : forall (x : word),
(bv_unsigned x + 1 <= 0x10000 \/ 0x97000 <= bv_unsigned x)%Z -> seg_rom rsegs x = None.
Proof. intros x Hx. unfold seg_rom. rewrite ref_memory_read_none by (cbn; lia). reflexivity. Qed.

Lemma ref_mrd_overlay : forall m (x : word),
(bv_unsigned x + 1 <= 0x10000 \/ 0x97000 <= bv_unsigned x)%Z -> mrd rsegs m x = m x.
Proof. intros m x Hx. unfold mrd. destruct (m x); [reflexivity|]. apply ref_seg_rom_none. exact Hx. Qed.
