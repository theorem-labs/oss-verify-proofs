(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Image.
From OSSVerify.zstd.fse_read_ncount.images Require Export AsanUbsan.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Ltac zify_pre_extra ::= atop_facts.
Import ListNotations.
Open Scope Z_scope.
Definition bsegs : list Segment := AsanUbsan.M.loaded_segments.
Definition b_init_pc : N := AsanUbsan.M.init_pc.
Definition b_phdrs : PhdrInfo := AsanUbsan.M.phdrs.
Lemma a_find_segment_1 : forall z, 0 <= z ->
find_segment bsegs z 1 =
if (0x10000 <=? z) && (z + 1 <=? 0x31000) then Some AsanUbsan_segment_000
else if (0x31000 <=? z) && (z + 1 <=? 0x99000) then Some AsanUbsan_segment_001
else if (0x99000 <=? z) && (z + 1 <=? 0x9b000) then Some AsanUbsan_segment_002
else if (0x9b000 <=? z) && (z + 1 <=? 0x5f7000) then Some AsanUbsan_segment_003
else None.
Proof. intros z Hz. reflexivity. Qed.
Lemma a_ro_addr : forall a : word,
ro_addr bsegs a = ((0x10000 <=? bv_unsigned a) && (bv_unsigned a <? 0x99000))%bool.
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
find_segment bsegs z n = None.
Proof.
intros z n Hn Hz. unfold bsegs, AsanUbsan.M.loaded_segments, AsanUbsan_loaded_segments. cbn [find_segment].
replace (Z.of_N (seg_base AsanUbsan_segment_000)) with 0x10000 by (vm_compute; reflexivity).
replace (Z.of_N (seg_size AsanUbsan_segment_000)) with 0x21000 by (vm_compute; reflexivity).
replace (Z.of_N (seg_base AsanUbsan_segment_001)) with 0x31000 by (vm_compute; reflexivity).
replace (Z.of_N (seg_size AsanUbsan_segment_001)) with 0x68000 by (vm_compute; reflexivity).
replace (Z.of_N (seg_base AsanUbsan_segment_002)) with 0x99000 by (vm_compute; reflexivity).
replace (Z.of_N (seg_size AsanUbsan_segment_002)) with 0x2000 by (vm_compute; reflexivity).
replace (Z.of_N (seg_base AsanUbsan_segment_003)) with 0x9b000 by (vm_compute; reflexivity).
replace (Z.of_N (seg_size AsanUbsan_segment_003)) with 0x55c000 by (vm_compute; reflexivity).
Local Ltac2 Set LiaHints.tbl := fun () => "00@0>27422229304.1227422229433.1227422261439.1234226853944.1034226853944.8 34226854073.6 34226854073.8 34226854202.6 34226854847.1034226886841.1034226886970.8 34233186150.6 64619634699.1264619635342.6 64619635469.8 64619635596.1000000900F00P00Y00f01001901:01G01Q01[01\01n02:02L02^S2Hn1l2l2S2Hz2n02n32n4S2Hz2n02n3S2Hn1l2l1S2Hz2n02n12n2S2Hz2n02n1S2Hn1l2l0FS2Hz2n02n22n3S2Hz2n02n2S2Hz2n02n1FS2Hn2Hz2n02l31l2l2S2Hn2Hz1l2l0S2Hn2Hz2n02l11l2l0S2Hn2Hz2n02l21l2l1".
destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x21000)); cbn [andb]; try lia;
destruct (Z.leb_spec0 0x31000 z); destruct (Z.leb_spec0 (z + n) (0x31000 + 0x68000)); cbn [andb]; try lia;
destruct (Z.leb_spec0 0x99000 z); destruct (Z.leb_spec0 (z + n) (0x99000 + 0x2000)); cbn [andb]; try lia;
destruct (Z.leb_spec0 0x9b000 z); destruct (Z.leb_spec0 (z + n) (0x9b000 + 0x55c000)); cbn [andb]; try lia; reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma ref_ro_addr_false : forall x : word,
(bv_unsigned x + 1 <= 0x10000 \/ 0x5f7000 <= bv_unsigned x)%Z -> ro_addr bsegs x = false.
Proof. intros x Hx. unfold ro_addr. rewrite ref_find_segment_none by lia. reflexivity. Qed.
Lemma ref_memory_read_none : forall (x : word) n,
(1 <= Z.of_N n)%Z -> (bv_unsigned x + Z.of_N n <= 0x10000 \/ 0x5f7000 <= bv_unsigned x)%Z -> memory_read bsegs x n = None.
Proof. intros x n Hn Hx. unfold memory_read. rewrite ref_find_segment_none by lia. reflexivity. Qed.
Lemma ref_wview_overlay : forall m (x : word),
(bv_unsigned x + 1 <= 0x10000 \/ 0x5f7000 <= bv_unsigned x)%Z -> wview bsegs m x = m x.
Proof.
intros m x Hx. unfold wview. destruct (m x); [reflexivity|]. rewrite ref_find_segment_none by lia. reflexivity.
Qed.
Lemma ref_seg_rom_none : forall (x : word),
(bv_unsigned x + 1 <= 0x10000 \/ 0x5f7000 <= bv_unsigned x)%Z -> seg_rom bsegs x = None.
Proof. intros x Hx. unfold seg_rom. rewrite ref_memory_read_none by (cbn; lia). reflexivity. Qed.
Lemma ref_mrd_overlay : forall m (x : word),
(bv_unsigned x + 1 <= 0x10000 \/ 0x5f7000 <= bv_unsigned x)%Z -> mrd bsegs m x = m x.
Proof. intros m x Hx. unfold mrd. destruct (m x); [reflexivity|]. apply ref_seg_rom_none. exact Hx. Qed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF.
Notation rng_aimg RNG := (rng RNG 0x10000 0x5e7000).
