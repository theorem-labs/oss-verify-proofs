(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(** Composition of the complete actual CRC phase, from chunks through all assertions. *)
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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import FuzzerCrcLoop FuzzerCrcRemainder FuzzerCrcAssertions.
Theorem fuzzer_crc_phase : forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo B k : Z) (inp : list byte) (m : word -> option byte) (Q : machine_state -> Prop),
  bytes_at rsegs m B inp -> bytes_at rsegs m CRC_TABS crc_table_bytes -> bytes_at rsegs m X2N_TAB x2n_bytes ->
  (0 < B)%Z -> (B+Z.of_nat (length inp) < 2^64)%Z ->
  (1 <= Z.of_nat (length inp) <= 1048576)%Z -> (1 <= k <= 255)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo+80 <= bv_unsigned sp)%Z ->
  (B+Z.of_nat (length inp) <= bv_unsigned sp-80 \/ bv_unsigned sp <= B)%Z ->
  (CRC_TABS+5120 <= bv_unsigned sp-80 \/ bv_unsigned sp <= CRC_TABS)%Z ->
  (X2N_TAB+128 <= bv_unsigned sp-80 \/ bv_unsigned sp <= X2N_TAB)%Z ->
  (forall (h1 h5 h6 h7 h10 h11 h12 h13 h14 h15 h16 h17 h22 h23 h24 h25 h27 h28 h29 h30 h31 : word) mfinal,
    munch [(bv_unsigned sp-80,bv_unsigned sp)]%Z m mfinal -> wmono rsegs m mfinal ->
    stk rsegs mfinal lo (bv_unsigned sp) -> bytes_at rsegs mfinal B inp ->
    evt rsegs Q (MS (mkR h1 sp gp tp h5 h6 h7 (Z_to_bv 64 (Z.of_nat (length inp))) (Z_to_bv 64 B) h10 h11 h12 h13 h14 h15 h16 h17 (Z_to_bv 64 1) (Z_to_bv 64 (Z.of_nat (length inp))) (Z_to_bv 64 k) (Z_to_bv 64 (Z.of_nat (length inp) mod k)) h22 h23 h24 h25 (Z_to_bv 64 4294967295) h27 h28 h29 h30 h31) F (Z_to_bv 64 0x143e0) fc None mfinal (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat (length inp))) (Z_to_bv 64 B) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) (Z_to_bv 64 (Z.of_nat (length inp))) (Z_to_bv 64 k) (Z_to_bv 64 (combine_gen_model k)) (Z_to_bv 64 0) (Z_to_bv 64 0) s8 (Z_to_bv 64 0) (Z_to_bv 64 4294967295) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x142a0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s11 t3 t4 t5 t6 F fc lo B k inp m Q INP TABLE XTABLE HBUF TOP SIZE HK ST LO DI DT DX CONT.
  eapply fuzzer_crc_loop with (fuel:=length inp) (i:=0%Z) (q:=0%Z) (answer:=crc_model 0 inp) (lo:=lo);
    [exact SIZE|exact HK|exact HBUF|exact TOP|reflexivity|exact LO|exact DI|exact DT|exact INP|exact TABLE|exact ST|lia|lia|lia|apply Z.mod_0_l;lia|reflexivity|].
  intros j qr m1 l1 l5 l6 l7 l11 l12 l13 l14 l15 l16 l17 l24 l27 l28 l29 l30 l31 HJ END JMOD HR INV MU WM ST1 INP1 TABLE1.
  eapply fuzzer_crc_remainder with (lo:=lo);
    [exact INP1|exact TABLE1|exact HBUF|exact TOP|exact SIZE|exact HK|exact HJ|exact END|exact JMOD|exact HR|exact INV|exact ST1|exact LO|exact DI|exact DT|].
  intros g5 g6 g7 g11 g12 g13 g14 g15 g16 g17 g24 g28 g29 g30 g31 m2 MU2 WM2 ST2 INP2 TABLE2.
  assert (MUALL : munch [(bv_unsigned sp-80,bv_unsigned sp)]%Z m m2) by (eapply munch_trans;eassumption).
  assert (WMALL : wmono rsegs m m2) by (eapply wmono_trans;eassumption).
  assert (X2 : bytes_at rsegs m2 X2N_TAB x2n_bytes).
  { eapply bytes_at_transport;[exact XTABLE|exact MUALL|]. cbn [disjoint_from]. rewrite x2n_bytes_length. cbn. split;[exact DX|exact I]. }
  assert (RM : (Z.of_nat (length inp) mod k = Z.of_nat (length inp)-j)%Z) by (apply fuzzer_remainder_mod;lia).
  rewrite <- RM.
  eapply fuzzer_crc_assertions with (n:=Z.of_nat (length inp));
    [reflexivity|reflexivity|exact X2|lia|apply crc_model_range;lia|].
  intros z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z22 z23 z24 z25 z28 z29 z30 z31 combined.
  eapply CONT;[exact MUALL|exact WMALL|exact ST2|exact INP2].
Qed.
