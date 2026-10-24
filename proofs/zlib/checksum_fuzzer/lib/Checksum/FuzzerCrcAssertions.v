(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(** All actual CRC combine and operator agreement assertions. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import Tac Bytes.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import Img0 CrcLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require TacDiet2.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.transport_chunks segs m a bs ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Tac.footprint_after_store segs m a bs ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.mem_after_store ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Tac.transport_after_call segs m m' MU WM ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.addr_eq_tac ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.ZBridge.word_eq_tac ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.ZBridge.mlia ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require StepFast.
#[local] Ltac2 Set OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.step_core segs R F pc fc rv m ro ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.zstep ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Destzna.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Tac.destruct_exs PO ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Destzna.dk_exs PO.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Tac.destruct_ands PO ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require WeqGuard TacDiet2.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.WeqGuard.weq_guard; OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Stor0fe.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.mem_after_store ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Dieta54.
Local Ltac lia ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Dieta54.dlia.
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import
  CrcModel CrcByteStep CrcTables CrcLoads CrcLinearBasis.

From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import
  CrcBodyEntry CrcWordBody CrcTailReturn CrcFrame CrcPrologue CrcSeed.
Local Opaque csteps raw_crc raw_byte.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import Crc32 CrcGen CrcOp CrcChunkLaw CrcGenModel CrcSeed.
Local Opaque crc_model combine_op_model combine_gen_model.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import CrcCombine.
Theorem fuzzer_crc_assertions : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (c n : Z) (m : word -> option byte) (Q : machine_state -> Prop),
  s0 = Z_to_bv 64 n -> s3 = Z_to_bv 64 n ->
  bytes_at rsegs m X2N_TAB x2n_bytes -> (0 <= n <= 1048576)%Z -> (0 <= c < 2^32)%Z ->
  (forall h5 h6 h7 h11 h12 h13 h14 h15 h16 h17 h22 h23 h24 h25 h28 h29 h30 h31 combined, evt rsegs Q (MS (mkR (Z_to_bv 64 0x143dc) sp gp tp h5 h6 h7 s0 s1 (Z_to_bv 64 combined) h11 h12 h13 h14 h15 h16 h17 s2 s3 s4 s5 h22 h23 h24 h25 (Z_to_bv 64 4294967295) s11 h28 h29 h30 h31) F (Z_to_bv 64 0x143e0) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 0) (Z_to_bv 64 c) s8 s9 (Z_to_bv 64 4294967295) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14354) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s9 s11 t3 t4 t5 t6 F fc c n m Q DS0 DS3 TABLE HN HC CONT. subst s0 s3.
  remember (combine_gen_model n) as op eqn:DOP.
  remember (combine_op_model c c op) as combined eqn:DCOM.
  assert (HOP : (0 < op < 2^32)%Z) by (rewrite DOP;apply combine_gen_model_positive).
  assert (HCOM : (0 <= combined < 2^32)%Z) by (rewrite DCOM;apply combine_op_model_range;exact HC).
  assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit;lia).
  assert (UC : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit;lia).
  assert (UOP : bv_unsigned (Z_to_bv 64 op) = op) by (apply unsigned_lit;lia).
  assert (LC : Z.land c 4294967295 = c).
  { change (Z.land c (Z.ones 32) = c). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
  assert (LOP : Z.land op 4294967295 = op).
  { change (Z.land op (Z.ones 32) = op). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
  idtac "CRC ASSERT call 1". do 6 zstep.
  try rewrite LC. try rewrite LOP.
  eapply evt_cut.
  - apply crc32_combine_spec; [exact TABLE|rewrite ?LC,?UC;lia|rewrite ?LC,?UC;lia|rewrite UN;lia].
  - { intros final HP. unfold crc_return_post in HP.
    destruct HP as (g0_5 & g0_6 & g0_7 & g0_11 & g0_12 & g0_13 & g0_14 & g0_15 & g0_16 & g0_17 & g0_28 & g0_29 & g0_30 & g0_31 & HS & MU & WM). subst final. clear MU WM.
    rewrite ?LC,?LOP,?UC,?UN,?UOP.
    rewrite <- DOP, <- DCOM.
    replace (ret_pc (Z_to_bv 64 0x1436c)) with (Z_to_bv 64 0x1436c) by (apply bv_eq;vm_compute;reflexivity).
  idtac "CRC ASSERT call 2". do 5 zstep.
  try rewrite LC. try rewrite LOP.
  eapply evt_cut.
  - apply crc32_combine_spec; [exact TABLE|rewrite ?LC,?UC;lia|rewrite ?LC,?UC;lia|rewrite UN;lia].
  - { intros final HP. unfold crc_return_post in HP.
    destruct HP as (g1_5 & g1_6 & g1_7 & g1_11 & g1_12 & g1_13 & g1_14 & g1_15 & g1_16 & g1_17 & g1_28 & g1_29 & g1_30 & g1_31 & HS & MU & WM). subst final. clear MU WM.
    rewrite ?LC,?LOP,?UC,?UN,?UOP.
    rewrite <- DOP, <- DCOM.
    replace (ret_pc (Z_to_bv 64 0x14380)) with (Z_to_bv 64 0x14380) by (apply bv_eq;vm_compute;reflexivity).
  zstep. if_cases K2; zify_cond K2; try (exfalso;lia).
  idtac "CRC ASSERT call 3". do 2 zstep.
  try rewrite LC. try rewrite LOP.
  eapply evt_cut.
  - apply crc32_combine_gen_table_spec; [exact TABLE|rewrite UN;lia].
  - { intros final HP. unfold crc_return_post in HP.
    destruct HP as (g2_5 & g2_6 & g2_7 & g2_11 & g2_12 & g2_13 & g2_14 & g2_15 & g2_16 & g2_17 & g2_28 & g2_29 & g2_30 & g2_31 & HS & MU & WM). subst final. clear MU WM.
    rewrite ?LC,?LOP,?UC,?UN,?UOP.
    rewrite <- DOP.
    replace (ret_pc (Z_to_bv 64 0x1438c)) with (Z_to_bv 64 0x1438c) by (apply bv_eq;vm_compute;reflexivity).
  idtac "CRC ASSERT call 4". do 5 zstep.
  try rewrite LC. try rewrite LOP.
  eapply evt_cut.
  - apply crc32_combine_op_any_memory_spec; rewrite ?LC,?LOP,?UC,?UOP;lia.
  - { intros final HP. unfold crc_return_post in HP.
    destruct HP as (g3_5 & g3_6 & g3_7 & g3_11 & g3_12 & g3_13 & g3_14 & g3_15 & g3_16 & g3_17 & g3_28 & g3_29 & g3_30 & g3_31 & HS & MU & WM). subst final. clear MU WM.
    rewrite ?LC,?LOP,?UC,?UN,?UOP.
    rewrite <- DCOM.
    replace (ret_pc (Z_to_bv 64 0x143a0)) with (Z_to_bv 64 0x143a0) by (apply bv_eq;vm_compute;reflexivity).
  idtac "CRC ASSERT call 5". do 5 zstep.
  try rewrite LC. try rewrite LOP.
  eapply evt_cut.
  - apply crc32_combine_op_any_memory_spec; rewrite ?LC,?LOP,?UC,?UOP;lia.
  - { intros final HP. unfold crc_return_post in HP.
    destruct HP as (g4_5 & g4_6 & g4_7 & g4_11 & g4_12 & g4_13 & g4_14 & g4_15 & g4_16 & g4_17 & g4_28 & g4_29 & g4_30 & g4_31 & HS & MU & WM). subst final. clear MU WM.
    rewrite ?LC,?LOP,?UC,?UN,?UOP.
    rewrite <- DCOM.
    replace (ret_pc (Z_to_bv 64 0x143b4)) with (Z_to_bv 64 0x143b4) by (apply bv_eq;vm_compute;reflexivity).
  zstep. if_cases K5; zify_cond K5; try (exfalso;lia).
  idtac "CRC ASSERT call 6". do 4 zstep.
  try rewrite LC. try rewrite LOP.
  eapply evt_cut.
  - apply crc32_combine_spec; [exact TABLE|rewrite ?LC,?UC;lia|rewrite ?LC,?UC;lia|rewrite UN;lia].
  - { intros final HP. unfold crc_return_post in HP.
    destruct HP as (g5_5 & g5_6 & g5_7 & g5_11 & g5_12 & g5_13 & g5_14 & g5_15 & g5_16 & g5_17 & g5_28 & g5_29 & g5_30 & g5_31 & HS & MU & WM). subst final. clear MU WM.
    rewrite ?LC,?LOP,?UC,?UN,?UOP.
    rewrite <- DOP, <- DCOM.
    replace (ret_pc (Z_to_bv 64 0x143c8)) with (Z_to_bv 64 0x143c8) by (apply bv_eq;vm_compute;reflexivity).
  idtac "CRC ASSERT call 7". do 5 zstep.
  try rewrite LC. try rewrite LOP.
  eapply evt_cut.
  - apply crc32_combine_op_any_memory_spec; rewrite ?LC,?LOP,?UC,?UOP;lia.
  - { intros final HP. unfold crc_return_post in HP.
    destruct HP as (g6_5 & g6_6 & g6_7 & g6_11 & g6_12 & g6_13 & g6_14 & g6_15 & g6_16 & g6_17 & g6_28 & g6_29 & g6_30 & g6_31 & HS & MU & WM). subst final. clear MU WM.
    rewrite ?LC,?LOP,?UC,?UN,?UOP.
    rewrite <- DCOM.
    replace (ret_pc (Z_to_bv 64 0x143dc)) with (Z_to_bv 64 0x143dc) by (apply bv_eq;vm_compute;reflexivity).
    zstep. if_cases K;zify_cond K;try (exfalso;lia). eapply CONT.
  }
  }
  }
  }
  }
  }
  }
Qed.
