(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvG1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export QvG1.
Import ListNotations.
Open Scope Z_scope.

Lemma a_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x645000 <= z) ->
find_segment asegs z n = None.
Proof.
intros z n Hn Hz. unfold asegs, Asan.M.loaded_segments, Asan.Asan_loaded_segments. cbn [find_segment].
replace (Z.of_N (seg_base Asan.Asan_segment_000)) with 0x10000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Asan.Asan_segment_000)) with 0x2d000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Asan.Asan_segment_001)) with 0x3d000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Asan.Asan_segment_001)) with 0xa5000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Asan.Asan_segment_002)) with 0x0e2000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Asan.Asan_segment_002)) with 0x5000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Asan.Asan_segment_003)) with 0x0e7000%Z by (vm_compute; reflexivity).
replace (Z.of_N (seg_size Asan.Asan_segment_003)) with 0x55e000%Z by (vm_compute; reflexivity).
destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x2d000)); cbn [andb]; try lia.
all: destruct (Z.leb_spec0 0x3d000 z); destruct (Z.leb_spec0 (z + n) (0x3d000 + 0xa5000)); cbn [andb]; try lia.
all: destruct (Z.leb_spec0 0x0e2000 z); destruct (Z.leb_spec0 (z + n) (0x0e2000 + 0x5000)); cbn [andb]; try lia.
all: destruct (Z.leb_spec0 0x0e7000 z); destruct (Z.leb_spec0 (z + n) (0x0e7000 + 0x55e000)); cbn [andb]; try lia.
all: reflexivity.
Qed.

Lemma a_ro_addr_false : forall x : word,
(bv_unsigned x + 1 <= 0x10000 \/ 0x645000 <= bv_unsigned x)%Z -> ro_addr asegs x = false.
Proof. intros x Hx. unfold ro_addr. rewrite a_find_segment_none by lia. reflexivity. Qed.

Lemma a_memory_read_none : forall (x : word) n,
(1 <= Z.of_N n)%Z -> (bv_unsigned x + Z.of_N n <= 0x10000 \/ 0x645000 <= bv_unsigned x)%Z -> memory_read asegs x n = None.
Proof. intros x n Hn Hx. unfold memory_read. rewrite a_find_segment_none by lia. reflexivity. Qed.

Lemma a_wview_overlay : forall m (x : word),
(bv_unsigned x + 1 <= 0x10000 \/ 0x645000 <= bv_unsigned x)%Z -> wview asegs m x = m x.
Proof.
intros m x Hx. unfold wview. destruct (m x); [reflexivity|]. rewrite a_find_segment_none by lia. reflexivity.
Qed.

Lemma a_seg_rom_none : forall (x : word),
(bv_unsigned x + 1 <= 0x10000 \/ 0x645000 <= bv_unsigned x)%Z -> seg_rom asegs x = None.
Proof. intros x Hx. unfold seg_rom. rewrite a_memory_read_none by (cbn; lia). reflexivity. Qed.

Lemma a_mrd_overlay : forall m (x : word),
(bv_unsigned x + 1 <= 0x10000 \/ 0x645000 <= bv_unsigned x)%Z -> mrd asegs m x = m x.
Proof. intros m x Hx. unfold mrd. destruct (m x); [reflexivity|]. apply a_seg_rom_none. exact Hx. Qed.

