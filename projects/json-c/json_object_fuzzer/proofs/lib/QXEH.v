(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export QBpX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Definition RIMG_LO : Z := 0x10000.
Definition RIMG_HI : Z := 0x647000.
Definition RDATA_LO : Z := 0xe4000.
Definition RCTX : Z := 0x6458a8.
Definition RMLOCK : Z := 0x6458a0.
Definition RLIBC : Z := 0x6457b0.
Definition RNEED_LOCKS : Z := 0x6457b3.
Definition RPAGE_SIZE : Z := 0x6457e0.
Definition RAUXV_CELL : Z := 0x6457b8.
Definition RSIZE_CLASSES : Z := 0x26fa8.
Definition RDEBRUIJN : Z := 0x26f88.
Definition RSMALL_CNT : Z := 0x27008.
Definition RMED_CNT : Z := 0x27023.
Definition RGOT_SSP : Z := 0xe8f90.
Definition RSSP_GUARD : Z := 0x645560.
Definition RVMLOCK : Z := 0x646db8.
Definition RATP : Z := 0x625520.
Definition RERRNO : Z := 0x62547c.

Definition rerrno_loc_entry : Z := 0xcea68.
Definition rsysret_entry : Z := 0xcf0cc.
Definition rcalloc_entry : Z := 0xd022c.
Definition rfree_sym : Z := 0xd0368.
Definition rmalloc_sym : Z := 0xd0364.
Definition rfree_entry : Z := 0xd0368.
Definition rget_meta_entry : Z := 0xd0534.
Definition rnontrivial_free_entry : Z := 0xd0644.
Definition ralloc_meta_entry : Z := 0xd0a1c.
Definition rmalloc_entry : Z := 0xd0cf4.
Definition ralloc_slot_entry : Z := 0xd1064.
Definition renframe_entry : Z := 0xd1908.
Definition ris_allzero_entry : Z := 0xd1a58.
Definition rrealloc_entry : Z := 0x1d888.
Definition rvm_wait_entry : Z := 0xe0e94.
Definition rmmap_entry : Z := 0xd4134.
Definition rmprotect_entry : Z := 0xd4220.
Definition rmremap_entry : Z := 0xd4268.
Definition rmunmap_entry : Z := 0xd433c.
Definition rlock_entry : Z := 0xdeb00.
Definition runlock_entry : Z := 0xded88.

Definition ref_reserved : list (Z * Z) := [(0x10000, 0x2e000); (0x3e000, 0xa6000); (0xe4000, 0x6000); (0xea000, 0x55d000)].

Lemma ref_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x647000 <= z) ->
find_segment usegs z n = None.
Proof.
intros z n Hn Hz. unfold usegs, AsanUbsan.M.loaded_segments, AsanUbsan.AsanUbsan_loaded_segments. cbn [find_segment].
replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_000)) with 0x10000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_000)) with 0x2e000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_001)) with 0x3e000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_001)) with 0xa6000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_002)) with 0xe4000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_002)) with 0x6000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_003)) with 0xea000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_003)) with 0x55d000%Z by (vm_compute; reflexivity).
destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x2e000)); cbn [andb]; try lia.
all: destruct (Z.leb_spec0 0x3e000 z); destruct (Z.leb_spec0 (z + n) (0x3e000 + 0xa6000)); cbn [andb]; try lia.
all: destruct (Z.leb_spec0 0xe4000 z); destruct (Z.leb_spec0 (z + n) (0xe4000 + 0x6000)); cbn [andb]; try lia.
all: destruct (Z.leb_spec0 0xea000 z); destruct (Z.leb_spec0 (z + n) (0xea000 + 0x55d000)); cbn [andb]; try lia.
all: reflexivity.
Qed.

Lemma ref_ro_addr_false : forall x : word,
(bv_unsigned x + 1 <= 0x10000 \/ 0x647000 <= bv_unsigned x)%Z -> ro_addr usegs x = false.
Proof. intros x Hx. unfold ro_addr. rewrite ref_find_segment_none by lia. reflexivity. Qed.

Lemma ref_memory_read_none : forall (x : word) n,
(1 <= Z.of_N n)%Z -> (bv_unsigned x + Z.of_N n <= 0x10000 \/ 0x647000 <= bv_unsigned x)%Z -> memory_read usegs x n = None.
Proof. intros x n Hn Hx. unfold memory_read. rewrite ref_find_segment_none by lia. reflexivity. Qed.

Lemma ref_wview_overlay : forall m (x : word),
(bv_unsigned x + 1 <= 0x10000 \/ 0x647000 <= bv_unsigned x)%Z -> wview usegs m x = m x.
Proof.
intros m x Hx. unfold wview. destruct (m x); [reflexivity|]. rewrite ref_find_segment_none by lia. reflexivity.
Qed.

Lemma ref_seg_rom_none : forall (x : word),
(bv_unsigned x + 1 <= 0x10000 \/ 0x647000 <= bv_unsigned x)%Z -> seg_rom usegs x = None.
Proof. intros x Hx. unfold seg_rom. rewrite ref_memory_read_none by (cbn; lia). reflexivity. Qed.

Lemma ref_mrd_overlay : forall m (x : word),
(bv_unsigned x + 1 <= 0x10000 \/ 0x647000 <= bv_unsigned x)%Z -> mrd usegs m x = m x.
Proof. intros m x Hx. unfold mrd. destruct (m x); [reflexivity|]. apply ref_seg_rom_none. exact Hx. Qed.
