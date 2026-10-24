(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(** Complete actual Adler phase, including inputs shorter than one chunk. *)
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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import FuzzerAdlerLoop FuzzerAdlerRemainder FuzzerAdlerAssertions FuzzerSlices.
Lemma fuzzer_adler_finish : forall (ra sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo B k i a b : Z) (inp : list byte) (m : word -> option byte) (Q : machine_state -> Prop),
  (0 <= a < ADLER_BASE)%Z -> (0 <= b < ADLER_BASE)%Z ->
  (0 <= i <= Z.of_nat (length inp))%Z -> (Z.of_nat (length inp) < i+k)%Z -> (i mod k = 0)%Z ->
  adler_model (adler_pack a b) (skipn (Z.to_nat i) inp) = adler_model 1 inp ->
  bytes_at rsegs m B inp -> bytes_at rsegs m 0x119e0 (le8 (Z_to_bv 64 ADLER_MAGIC)) ->
  (0 < B)%Z -> (B+Z.of_nat (length inp) < 2^64)%Z ->
  (1 <= Z.of_nat (length inp) <= 1048576)%Z -> (1 <= k <= 255)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo+32 <= bv_unsigned sp)%Z ->
  (B+Z.of_nat (length inp) <= bv_unsigned sp-32 \/ bv_unsigned sp <= B)%Z ->
  (0x119e0+8 <= bv_unsigned sp-32 \/ bv_unsigned sp <= 0x119e0)%Z ->
  (forall (v1 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 : word) mfinal,
    munch [(bv_unsigned sp-32,bv_unsigned sp)]%Z m mfinal -> wmono rsegs m mfinal ->
    stk rsegs mfinal lo (bv_unsigned sp) -> evt rsegs Q (MS (mkR v1 sp gp tp v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31) F (Z_to_bv 64 0x14480) fc None mfinal (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat (length inp))) (Z_to_bv 64 B) (Z_to_bv 64 (adler_pack a b)) (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) (Z_to_bv 64 (Z.of_nat (length inp))) (Z_to_bv 64 k) (Z_to_bv 64 (Z.of_nat (length inp) mod k)) s6 s7 s8 s9 (Z_to_bv 64 4294967295) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14424) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc lo B k i a b inp m Q HA HB HI END IMOD INV INP TABLE HBUF TOP SIZE HK ST LO DI DT CONT.
  eapply fuzzer_adler_remainder with (lo:=lo);
    [exact HA|exact HB|exact INP|exact TABLE|exact HBUF|exact TOP|exact SIZE|exact HK|exact HI|exact END|exact IMOD|exact INV|exact ST|exact LO|exact DI|exact DT|].
  intros h5 h6 h7 h11 h12 h13 h14 h15 h16 h17 h21 h28 h29 h30 h31 m2 MU WM ST2 INP2 TABLE2.
  destruct (adler_model_valid_seed 1 inp) as (ao & bo & HAO & HBO & DP).
  rewrite DP.
  eapply fuzzer_adler_assertion;
    [exact HAO|exact HBO|lia| |].
  - pose proof (bytes_at_ov_read rsegs m2 0x119e0 (le8 (Z_to_bv 64 ADLER_MAGIC)) 0 8 TABLE2 ltac:(reflexivity)) as RD.
    cbn [skipn firstn] in RD. replace (0x119e0+Z.of_nat 0)%Z with 0x119e0%Z in RD by reflexivity. exact RD.
  - intros g5 g6 g7 g11 g12 g13 g14 g15 g16 g17 g28 g29 g30 g31 combined.
    eapply CONT;[exact MU|exact WM|exact ST2].
Qed.
Theorem fuzzer_adler_phase : forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo B k : Z) (inp : list byte) (m : word -> option byte) (Q : machine_state -> Prop),
  bytes_at rsegs m B inp -> bytes_at rsegs m 0x119e0 (le8 (Z_to_bv 64 ADLER_MAGIC)) ->
  (0 < B)%Z -> (B+Z.of_nat (length inp) < 2^64)%Z ->
  (1 <= Z.of_nat (length inp) <= 1048576)%Z -> (1 <= k <= 255)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo+32 <= bv_unsigned sp)%Z ->
  (B+Z.of_nat (length inp) <= bv_unsigned sp-32 \/ bv_unsigned sp <= B)%Z ->
  (0x119e0+8 <= bv_unsigned sp-32 \/ bv_unsigned sp <= 0x119e0)%Z ->
  (forall (v1 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 : word) mfinal,
    munch [(bv_unsigned sp-32,bv_unsigned sp)]%Z m mfinal -> wmono rsegs m mfinal ->
    stk rsegs mfinal lo (bv_unsigned sp) -> evt rsegs Q (MS (mkR v1 sp gp tp v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31) F (Z_to_bv 64 0x14480) fc None mfinal (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat (length inp))) (Z_to_bv 64 B) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) (Z_to_bv 64 (Z.of_nat (length inp))) (Z_to_bv 64 k) (Z_to_bv 64 (Z.of_nat (length inp) mod k)) s6 s7 s8 s9 (Z_to_bv 64 4294967295) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x143e0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc lo B k inp m Q INP TABLE HBUF TOP SIZE HK ST LO DI DT CONT.
  zstep. if_cases K;zify_cond K.
  - do 2 zstep. change 1%Z with (adler_pack 1 0) at 1.
    eapply fuzzer_adler_loop with (fuel:=length inp) (i:=0%Z) (a:=1%Z) (b:=0%Z) (answer:=adler_model 1 inp) (lo:=lo);
      [exact SIZE|exact HK|exact HBUF|exact TOP|exact LO|exact DI|exact DT|exact INP|exact TABLE|exact ST|lia|exact K|lia|unfold ADLER_BASE;lia|unfold ADLER_BASE;lia|apply Z.mod_0_l;lia|rewrite adler_initial_word;reflexivity|].
    intros j ao bo m1 h5 h6 h7 h12 h13 h14 h15 h16 h17 h28 h29 h30 h31 HJ END JMOD HAO HBO INV MU WM ST1 INP1 TABLE1.
    eapply fuzzer_adler_finish with (lo:=lo);
      [exact HAO|exact HBO|exact HJ|exact END|exact JMOD|exact INV|exact INP1|exact TABLE1|exact HBUF|exact TOP|exact SIZE|exact HK|exact ST1|exact LO|exact DI|exact DT|].
    intros v1 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 mfinal MU2 WM2 ST2.
    eapply CONT;[eapply munch_trans;[exact MU|exact MU2]|eapply wmono_trans;[exact WM|exact WM2]|exact ST2].
  - do 3 zstep. change 1%Z with (adler_pack 1 0) at 1.
    eapply fuzzer_adler_finish with (lo:=lo) (i:=0%Z) (a:=1%Z) (b:=0%Z);
      [unfold ADLER_BASE;lia|unfold ADLER_BASE;lia|lia|lia|apply Z.mod_0_l;lia|rewrite adler_initial_word;reflexivity|exact INP|exact TABLE|exact HBUF|exact TOP|exact SIZE|exact HK|exact ST|exact LO|exact DI|exact DT|exact CONT].
Qed.
