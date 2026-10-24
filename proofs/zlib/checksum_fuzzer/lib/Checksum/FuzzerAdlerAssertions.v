(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(** Actual final Adler combine agreement assertion. *)
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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import Adler32 AdlerFrame AdlerModel AdlerWord AdlerComposition.
Local Opaque adler_output adler_model adler_pack.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import AdlerCombine.
Local Opaque adler_combine_model.
Theorem fuzzer_adler_assertion : forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (a b n : Z) (m : word -> option byte) (Q : machine_state -> Prop),
  (0 <= a < ADLER_BASE)%Z -> (0 <= b < ADLER_BASE)%Z -> (0 <= n <= 1048576)%Z ->
  ov_read_bytes rsegs m (wa 0x119e0) 8 = Some (le8 (Z_to_bv 64 ADLER_MAGIC)) ->
  (forall (h5 h6 h7 h11 h12 h13 h14 h15 h16 h17 h28 h29 h30 h31 : word) combined, evt rsegs Q (MS (mkR (Z_to_bv 64 0x1447c) sp gp tp h5 h6 h7 (Z_to_bv 64 n) (Z_to_bv 64 (adler_pack a b)) (Z_to_bv 64 combined) h11 h12 h13 h14 h15 h16 h17 (Z_to_bv 64 combined) (Z_to_bv 64 n) (Z_to_bv 64 (adler_pack a b)) s5 s6 s7 s8 s9 (Z_to_bv 64 4294967295) s11 h28 h29 h30 h31) F (Z_to_bv 64 0x14480) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 n) s1 (Z_to_bv 64 (adler_pack a b)) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 n) (Z_to_bv 64 (adler_pack a b)) s5 s6 s7 s8 s9 (Z_to_bv 64 4294967295) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14454) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc a b n m Q HA HB HN TABLE CONT.
  remember (adler_pack a b) as q eqn:DQ in *.
  pose proof (adler_pack_range a b HA HB) as HQ. rewrite <- DQ in HQ.
  assert (LQ : Z.land q 4294967295 = q).
  { change (Z.land q (Z.ones 32) = q). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
  remember (adler_combine_model a b a b n) as combined eqn:DCOM.
  idtac "ADLER ASSERT first call". do 5 zstep. try rewrite LQ. rewrite DQ.
  eapply evt_cut.
  - apply adler32_combine_spec;assumption.
  - intros final HP. unfold crc_return_post in HP.
    destruct HP as (g5 & g6 & g7 & g11 & g12 & g13 & g14 & g15 & g16 & g17 & g28 & g29 & g30 & g31 & HS & MU & WM). subst final. clear MU WM.
    rewrite <- DCOM, <- DQ.
    replace (ret_pc (Z_to_bv 64 0x14468)) with (Z_to_bv 64 0x14468) by (apply bv_eq;vm_compute;reflexivity).
    idtac "ADLER ASSERT second call". do 5 zstep. rewrite DQ.
    eapply evt_cut.
    + apply adler32_combine_spec;assumption.
    + intros final HP. unfold crc_return_post in HP.
      destruct HP as (h5 & h6 & h7 & h11 & h12 & h13 & h14 & h15 & h16 & h17 & h28 & h29 & h30 & h31 & HS & MU & WM). subst final.
      rewrite <- DCOM, <- DQ.
      replace (ret_pc (Z_to_bv 64 0x1447c)) with (Z_to_bv 64 0x1447c) by (apply bv_eq;vm_compute;reflexivity).
      zstep. if_cases K;zify_cond K;try (exfalso;lia). eapply CONT.
Qed.
