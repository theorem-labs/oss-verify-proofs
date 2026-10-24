(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(** Functional multiplication loop adapted from the pinned Varnish proof to
    the actual zlib checksum_fuzzer instruction layout and register allocation. *)
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

From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import CrcUnrolledBytes.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import AdlerModel.
Definition adler_block16_bytes (inp : list byte) (i : Z) := [bbyte inp i;bbyte inp (i+1);bbyte inp (i+2);bbyte inp (i+3);bbyte inp (i+4);bbyte inp (i+5);bbyte inp (i+6);bbyte inp (i+7);bbyte inp (i+8);bbyte inp (i+9);bbyte inp (i+10);bbyte inp (i+11);bbyte inp (i+12);bbyte inp (i+13);bbyte inp (i+14);bbyte inp (i+15)].
Definition adler_block16_a inp i a b := fst (adler_raw (adler_block16_bytes inp i) a b).
Definition adler_block16_b inp i a b := snd (adler_raw (adler_block16_bytes inp i) a b).

Section AdlerBlock_outer.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (B : Z) (inp : list byte).
  Hypothesis INP : bytes_at rsegs m B inp.
  Variable Q : machine_state -> Prop.
  Lemma adler_block16_outer : forall i a b,
    (0 <= i)%Z -> (i+16 <= Z.of_nat (length inp))%Z -> (0 <= a < 2^48)%Z -> (0 <= b < 2^48)%Z ->
    (forall h8 h9 h18 h31, evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 h8 h9 a0 a1 a2 (Z_to_bv 64 (adler_block16_b inp i a b)) (Z_to_bv 64 (adler_block16_a inp i a b)) a5 a6 a7 h18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 (Z_to_bv 64 (B+i+16)) h31) F (Z_to_bv 64 0x14fdc) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 b) (Z_to_bv 64 a) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 (Z_to_bv 64 (B+i)) t6) F (Z_to_bv 64 0x14f18) fc None m (seg_rom rsegs)).
  Proof.
    intros i a b HI HL HA HB CONT.
    remember (bv_unsigned (bbyte inp i)) as V0 eqn:DV0.
    pose proof (byte_unsigned_range (bbyte inp i)) as HV0. rewrite <- DV0 in HV0.
    pose proof (rd1_at rsegs m B inp i _ INP ltac:(lia) ltac:(lia) eq_refl) as RD0.
    remember (bv_unsigned (bbyte inp (i+1))) as V1 eqn:DV1.
    pose proof (byte_unsigned_range (bbyte inp (i+1))) as HV1. rewrite <- DV1 in HV1.
    pose proof (rd1_at rsegs m B inp (i+1) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD1.
    remember (bv_unsigned (bbyte inp (i+2))) as V2 eqn:DV2.
    pose proof (byte_unsigned_range (bbyte inp (i+2))) as HV2. rewrite <- DV2 in HV2.
    pose proof (rd1_at rsegs m B inp (i+2) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD2.
    remember (bv_unsigned (bbyte inp (i+3))) as V3 eqn:DV3.
    pose proof (byte_unsigned_range (bbyte inp (i+3))) as HV3. rewrite <- DV3 in HV3.
    pose proof (rd1_at rsegs m B inp (i+3) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD3.
    remember (bv_unsigned (bbyte inp (i+4))) as V4 eqn:DV4.
    pose proof (byte_unsigned_range (bbyte inp (i+4))) as HV4. rewrite <- DV4 in HV4.
    pose proof (rd1_at rsegs m B inp (i+4) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD4.
    remember (bv_unsigned (bbyte inp (i+5))) as V5 eqn:DV5.
    pose proof (byte_unsigned_range (bbyte inp (i+5))) as HV5. rewrite <- DV5 in HV5.
    pose proof (rd1_at rsegs m B inp (i+5) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD5.
    remember (bv_unsigned (bbyte inp (i+6))) as V6 eqn:DV6.
    pose proof (byte_unsigned_range (bbyte inp (i+6))) as HV6. rewrite <- DV6 in HV6.
    pose proof (rd1_at rsegs m B inp (i+6) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD6.
    remember (bv_unsigned (bbyte inp (i+7))) as V7 eqn:DV7.
    pose proof (byte_unsigned_range (bbyte inp (i+7))) as HV7. rewrite <- DV7 in HV7.
    pose proof (rd1_at rsegs m B inp (i+7) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD7.
    remember (bv_unsigned (bbyte inp (i+8))) as V8 eqn:DV8.
    pose proof (byte_unsigned_range (bbyte inp (i+8))) as HV8. rewrite <- DV8 in HV8.
    pose proof (rd1_at rsegs m B inp (i+8) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD8.
    remember (bv_unsigned (bbyte inp (i+9))) as V9 eqn:DV9.
    pose proof (byte_unsigned_range (bbyte inp (i+9))) as HV9. rewrite <- DV9 in HV9.
    pose proof (rd1_at rsegs m B inp (i+9) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD9.
    remember (bv_unsigned (bbyte inp (i+10))) as V10 eqn:DV10.
    pose proof (byte_unsigned_range (bbyte inp (i+10))) as HV10. rewrite <- DV10 in HV10.
    pose proof (rd1_at rsegs m B inp (i+10) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD10.
    remember (bv_unsigned (bbyte inp (i+11))) as V11 eqn:DV11.
    pose proof (byte_unsigned_range (bbyte inp (i+11))) as HV11. rewrite <- DV11 in HV11.
    pose proof (rd1_at rsegs m B inp (i+11) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD11.
    remember (bv_unsigned (bbyte inp (i+12))) as V12 eqn:DV12.
    pose proof (byte_unsigned_range (bbyte inp (i+12))) as HV12. rewrite <- DV12 in HV12.
    pose proof (rd1_at rsegs m B inp (i+12) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD12.
    remember (bv_unsigned (bbyte inp (i+13))) as V13 eqn:DV13.
    pose proof (byte_unsigned_range (bbyte inp (i+13))) as HV13. rewrite <- DV13 in HV13.
    pose proof (rd1_at rsegs m B inp (i+13) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD13.
    remember (bv_unsigned (bbyte inp (i+14))) as V14 eqn:DV14.
    pose proof (byte_unsigned_range (bbyte inp (i+14))) as HV14. rewrite <- DV14 in HV14.
    pose proof (rd1_at rsegs m B inp (i+14) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD14.
    remember (bv_unsigned (bbyte inp (i+15))) as V15 eqn:DV15.
    pose proof (byte_unsigned_range (bbyte inp (i+15))) as HV15. rewrite <- DV15 in HV15.
    pose proof (rd1_at rsegs m B inp (i+15) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD15.
    remember (a+V0)%Z as A1 eqn:DA1. remember (b+A1)%Z as S1 eqn:DS1.
    assert (HA1 : (0 <= A1 < 2^64)%Z) by (rewrite DA1;lia).
    assert (HS1 : (0 <= S1 < 2^64)%Z) by (rewrite DS1,DA1;lia).
    remember (A1+V1)%Z as A2 eqn:DA2. remember (S1+A2)%Z as S2 eqn:DS2.
    assert (HA2 : (0 <= A2 < 2^64)%Z) by (rewrite DA2,DA1;lia).
    assert (HS2 : (0 <= S2 < 2^64)%Z) by (rewrite DS2,DS1,DA2,DA1;lia).
    remember (A2+V2)%Z as A3 eqn:DA3. remember (S2+A3)%Z as S3 eqn:DS3.
    assert (HA3 : (0 <= A3 < 2^64)%Z) by (rewrite DA3,DA2,DA1;lia).
    assert (HS3 : (0 <= S3 < 2^64)%Z) by (rewrite DS3,DS2,DS1,DA3,DA2,DA1;lia).
    remember (A3+V3)%Z as A4 eqn:DA4. remember (S3+A4)%Z as S4 eqn:DS4.
    assert (HA4 : (0 <= A4 < 2^64)%Z) by (rewrite DA4,DA3,DA2,DA1;lia).
    assert (HS4 : (0 <= S4 < 2^64)%Z) by (rewrite DS4,DS3,DS2,DS1,DA4,DA3,DA2,DA1;lia).
    remember (A4+V4)%Z as A5 eqn:DA5. remember (S4+A5)%Z as S5 eqn:DS5.
    assert (HA5 : (0 <= A5 < 2^64)%Z) by (rewrite DA5,DA4,DA3,DA2,DA1;lia).
    assert (HS5 : (0 <= S5 < 2^64)%Z) by (rewrite DS5,DS4,DS3,DS2,DS1,DA5,DA4,DA3,DA2,DA1;lia).
    remember (A5+V5)%Z as A6 eqn:DA6. remember (S5+A6)%Z as S6 eqn:DS6.
    assert (HA6 : (0 <= A6 < 2^64)%Z) by (rewrite DA6,DA5,DA4,DA3,DA2,DA1;lia).
    assert (HS6 : (0 <= S6 < 2^64)%Z) by (rewrite DS6,DS5,DS4,DS3,DS2,DS1,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    remember (A6+V6)%Z as A7 eqn:DA7. remember (S6+A7)%Z as S7 eqn:DS7.
    assert (HA7 : (0 <= A7 < 2^64)%Z) by (rewrite DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    assert (HS7 : (0 <= S7 < 2^64)%Z) by (rewrite DS7,DS6,DS5,DS4,DS3,DS2,DS1,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    remember (A7+V7)%Z as A8 eqn:DA8. remember (S7+A8)%Z as S8 eqn:DS8.
    assert (HA8 : (0 <= A8 < 2^64)%Z) by (rewrite DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    assert (HS8 : (0 <= S8 < 2^64)%Z) by (rewrite DS8,DS7,DS6,DS5,DS4,DS3,DS2,DS1,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    remember (A8+V8)%Z as A9 eqn:DA9. remember (S8+A9)%Z as S9 eqn:DS9.
    assert (HA9 : (0 <= A9 < 2^64)%Z) by (rewrite DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    assert (HS9 : (0 <= S9 < 2^64)%Z) by (rewrite DS9,DS8,DS7,DS6,DS5,DS4,DS3,DS2,DS1,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    remember (A9+V9)%Z as A10 eqn:DA10. remember (S9+A10)%Z as S10 eqn:DS10.
    assert (HA10 : (0 <= A10 < 2^64)%Z) by (rewrite DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    assert (HS10 : (0 <= S10 < 2^64)%Z) by (rewrite DS10,DS9,DS8,DS7,DS6,DS5,DS4,DS3,DS2,DS1,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    remember (A10+V10)%Z as A11 eqn:DA11. remember (S10+A11)%Z as S11 eqn:DS11.
    assert (HA11 : (0 <= A11 < 2^64)%Z) by (rewrite DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    assert (HS11 : (0 <= S11 < 2^64)%Z) by (rewrite DS11,DS10,DS9,DS8,DS7,DS6,DS5,DS4,DS3,DS2,DS1,DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    remember (A11+V11)%Z as A12 eqn:DA12. remember (S11+A12)%Z as S12 eqn:DS12.
    assert (HA12 : (0 <= A12 < 2^64)%Z) by (rewrite DA12,DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    assert (HS12 : (0 <= S12 < 2^64)%Z) by (rewrite DS12,DS11,DS10,DS9,DS8,DS7,DS6,DS5,DS4,DS3,DS2,DS1,DA12,DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    remember (A12+V12)%Z as A13 eqn:DA13. remember (S12+A13)%Z as S13 eqn:DS13.
    assert (HA13 : (0 <= A13 < 2^64)%Z) by (rewrite DA13,DA12,DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    assert (HS13 : (0 <= S13 < 2^64)%Z) by (rewrite DS13,DS12,DS11,DS10,DS9,DS8,DS7,DS6,DS5,DS4,DS3,DS2,DS1,DA13,DA12,DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    remember (A13+V13)%Z as A14 eqn:DA14. remember (S13+A14)%Z as S14 eqn:DS14.
    assert (HA14 : (0 <= A14 < 2^64)%Z) by (rewrite DA14,DA13,DA12,DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    assert (HS14 : (0 <= S14 < 2^64)%Z) by (rewrite DS14,DS13,DS12,DS11,DS10,DS9,DS8,DS7,DS6,DS5,DS4,DS3,DS2,DS1,DA14,DA13,DA12,DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    remember (A14+V14)%Z as A15 eqn:DA15. remember (S14+A15)%Z as S15 eqn:DS15.
    assert (HA15 : (0 <= A15 < 2^64)%Z) by (rewrite DA15,DA14,DA13,DA12,DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    assert (HS15 : (0 <= S15 < 2^64)%Z) by (rewrite DS15,DS14,DS13,DS12,DS11,DS10,DS9,DS8,DS7,DS6,DS5,DS4,DS3,DS2,DS1,DA15,DA14,DA13,DA12,DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    remember (A15+V15)%Z as A16 eqn:DA16. remember (S15+A16)%Z as S16 eqn:DS16.
    assert (HA16 : (0 <= A16 < 2^64)%Z) by (rewrite DA16,DA15,DA14,DA13,DA12,DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    assert (HS16 : (0 <= S16 < 2^64)%Z) by (rewrite DS16,DS15,DS14,DS13,DS12,DS11,DS10,DS9,DS8,DS7,DS6,DS5,DS4,DS3,DS2,DS1,DA16,DA15,DA14,DA13,DA12,DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    assert (EA : A16 = adler_block16_a inp i a b).
    { unfold adler_block16_a,adler_block16_bytes. cbn [adler_raw fst snd]. rewrite <-DV0,<-DV1,<-DV2,<-DV3,<-DV4,<-DV5,<-DV6,<-DV7,<-DV8,<-DV9,<-DV10,<-DV11,<-DV12,<-DV13,<-DV14,<-DV15,DA16,DA15,DA14,DA13,DA12,DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1. ring. }
    assert (ES : S16 = adler_block16_b inp i a b).
    { unfold adler_block16_b,adler_block16_bytes. cbn [adler_raw fst snd]. rewrite <-DV0,<-DV1,<-DV2,<-DV3,<-DV4,<-DV5,<-DV6,<-DV7,<-DV8,<-DV9,<-DV10,<-DV11,<-DV12,<-DV13,<-DV14,<-DV15,DS16,DS15,DS14,DS13,DS12,DS11,DS10,DS9,DS8,DS7,DS6,DS5,DS4,DS3,DS2,DS1,DA16,DA15,DA14,DA13,DA12,DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1. ring. }
    (* 0x14f18 lbu t6, 0(t5) *)
    zstep. try rewrite <- DV0.
    (* 0x14f1c lbu s0, 1(t5) *)
    zstep. try rewrite <- DV1.
    (* 0x14f20 lbu s1, 2(t5) *)
    zstep. try rewrite <- DV2.
    (* 0x14f24 lbu s2, 3(t5) *)
    zstep. try rewrite <- DV3.
    (* 0x14f28 add a4, a4, t6 *)
    zstep. try rewrite <- DA1.
    (* 0x14f2c add a3, a4, a3 *)
    zstep. replace (A1+b)%Z with (b+A1)%Z by ring. try rewrite <- DS1.
    (* 0x14f30 add a4, a4, s0 *)
    zstep. try rewrite <- DA2.
    (* 0x14f34 add a3, a3, a4 *)
    zstep. replace (A2+S1)%Z with (S1+A2)%Z by ring. try rewrite <- DS2.
    (* 0x14f38 add a4, a4, s1 *)
    zstep. try rewrite <- DA3.
    (* 0x14f3c add a3, a3, a4 *)
    zstep. replace (A3+S2)%Z with (S2+A3)%Z by ring. try rewrite <- DS3.
    (* 0x14f40 add a4, a4, s2 *)
    zstep. try rewrite <- DA4.
    (* 0x14f44 lbu t6, 4(t5) *)
    zstep. try rewrite <- DV4.
    (* 0x14f48 lbu s0, 5(t5) *)
    zstep. try rewrite <- DV5.
    (* 0x14f4c lbu s1, 6(t5) *)
    zstep. try rewrite <- DV6.
    (* 0x14f50 lbu s2, 7(t5) *)
    zstep. try rewrite <- DV7.
    (* 0x14f54 add a3, a3, a4 *)
    zstep. replace (A4+S3)%Z with (S3+A4)%Z by ring. try rewrite <- DS4.
    (* 0x14f58 add a4, a4, t6 *)
    zstep. try rewrite <- DA5.
    (* 0x14f5c add a3, a3, a4 *)
    zstep. replace (A5+S4)%Z with (S4+A5)%Z by ring. try rewrite <- DS5.
    (* 0x14f60 add a4, a4, s0 *)
    zstep. try rewrite <- DA6.
    (* 0x14f64 add a3, a3, a4 *)
    zstep. replace (A6+S5)%Z with (S5+A6)%Z by ring. try rewrite <- DS6.
    (* 0x14f68 add a4, a4, s1 *)
    zstep. try rewrite <- DA7.
    (* 0x14f6c add a3, a3, a4 *)
    zstep. replace (A7+S6)%Z with (S6+A7)%Z by ring. try rewrite <- DS7.
    (* 0x14f70 add a4, a4, s2 *)
    zstep. try rewrite <- DA8.
    (* 0x14f74 lbu t6, 8(t5) *)
    zstep. try rewrite <- DV8.
    (* 0x14f78 lbu s0, 9(t5) *)
    zstep. try rewrite <- DV9.
    (* 0x14f7c lbu s1, 0xa(t5) *)
    zstep. try rewrite <- DV10.
    (* 0x14f80 lbu s2, 0xb(t5) *)
    zstep. try rewrite <- DV11.
    (* 0x14f84 add a3, a3, a4 *)
    zstep. replace (A8+S7)%Z with (S7+A8)%Z by ring. try rewrite <- DS8.
    (* 0x14f88 add a4, a4, t6 *)
    zstep. try rewrite <- DA9.
    (* 0x14f8c add a3, a3, a4 *)
    zstep. replace (A9+S8)%Z with (S8+A9)%Z by ring. try rewrite <- DS9.
    (* 0x14f90 add a4, a4, s0 *)
    zstep. try rewrite <- DA10.
    (* 0x14f94 add a3, a3, a4 *)
    zstep. replace (A10+S9)%Z with (S9+A10)%Z by ring. try rewrite <- DS10.
    (* 0x14f98 add a4, a4, s1 *)
    zstep. try rewrite <- DA11.
    (* 0x14f9c add a3, a3, a4 *)
    zstep. replace (A11+S10)%Z with (S10+A11)%Z by ring. try rewrite <- DS11.
    (* 0x14fa0 add a4, a4, s2 *)
    zstep. try rewrite <- DA12.
    (* 0x14fa4 lbu t6, 0xc(t5) *)
    zstep. try rewrite <- DV12.
    (* 0x14fa8 lbu s0, 0xd(t5) *)
    zstep. try rewrite <- DV13.
    (* 0x14fac lbu s1, 0xe(t5) *)
    zstep. try rewrite <- DV14.
    (* 0x14fb0 lbu s2, 0xf(t5) *)
    zstep. try rewrite <- DV15.
    (* 0x14fb4 add a3, a3, a4 *)
    zstep. replace (A12+S11)%Z with (S11+A12)%Z by ring. try rewrite <- DS12.
    (* 0x14fb8 add a4, a4, t6 *)
    zstep. try rewrite <- DA13.
    (* 0x14fbc add a3, a3, a4 *)
    zstep. replace (A13+S12)%Z with (S12+A13)%Z by ring. try rewrite <- DS13.
    (* 0x14fc0 add a4, a4, s0 *)
    zstep. try rewrite <- DA14.
    (* 0x14fc4 add a3, a3, a4 *)
    zstep. replace (A14+S13)%Z with (S13+A14)%Z by ring. try rewrite <- DS14.
    (* 0x14fc8 add a4, a4, s1 *)
    zstep. try rewrite <- DA15.
    (* 0x14fcc add a3, a3, a4 *)
    zstep. replace (A15+S14)%Z with (S14+A15)%Z by ring. try rewrite <- DS15.
    (* 0x14fd0 add a4, a4, s2 *)
    zstep. try rewrite <- DA16.
    (* 0x14fd4 addi t5, t5, 0x10 *)
    zstep. 
    (* 0x14fd8 add a3, a3, a4 *)
    zstep. replace (A16+S15)%Z with (S15+A16)%Z by ring. try rewrite <- DS16.
    rewrite <- EA,<- ES in CONT. rewrite DS16,DS15,DS14,DS13,DS12,DS11,DS10,DS9,DS8,DS7,DS6,DS5,DS4,DS3,DS2,DS1,DA16,DA15,DA14,DA13,DA12,DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1,DV0,DV1,DV2,DV3,DV4,DV5,DV6,DV7,DV8,DV9,DV10,DV11,DV12,DV13,DV14,DV15 in CONT.
    replace (a+bv_unsigned (bbyte inp i)+b)%Z with (b+(a+bv_unsigned (bbyte inp i)))%Z by ring.
    apply CONT.
  Qed.
End AdlerBlock_outer.

Section AdlerBlock_inner.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (B : Z) (inp : list byte).
  Hypothesis INP : bytes_at rsegs m B inp.
  Variable Q : machine_state -> Prop.
  Lemma adler_block16_inner : forall i a b n,
    (0 <= i)%Z -> (i+16 <= Z.of_nat (length inp))%Z -> (0 <= a < 2^48)%Z -> (0 <= b < 2^48)%Z ->
    (16 <= n <= 1048576)%Z ->
    (forall h16 h17 h5 h6, evt rsegs Q (MS (mkR ra sp gp tp h5 h6 t2 s0 s1 a0 a1 (Z_to_bv 64 (n-16)) (Z_to_bv 64 (adler_block16_b inp i a b)) (Z_to_bv 64 (adler_block16_a inp i a b)) (Z_to_bv 64 (B+i+16)) h16 h17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15108) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 n) (Z_to_bv 64 b) (Z_to_bv 64 a) (Z_to_bv 64 (B+i)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15040) fc None m (seg_rom rsegs)).
  Proof.
    intros i a b n HI HL HA HB HN CONT.
    remember (bv_unsigned (bbyte inp i)) as V0 eqn:DV0.
    pose proof (byte_unsigned_range (bbyte inp i)) as HV0. rewrite <- DV0 in HV0.
    pose proof (rd1_at rsegs m B inp i _ INP ltac:(lia) ltac:(lia) eq_refl) as RD0.
    remember (bv_unsigned (bbyte inp (i+1))) as V1 eqn:DV1.
    pose proof (byte_unsigned_range (bbyte inp (i+1))) as HV1. rewrite <- DV1 in HV1.
    pose proof (rd1_at rsegs m B inp (i+1) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD1.
    remember (bv_unsigned (bbyte inp (i+2))) as V2 eqn:DV2.
    pose proof (byte_unsigned_range (bbyte inp (i+2))) as HV2. rewrite <- DV2 in HV2.
    pose proof (rd1_at rsegs m B inp (i+2) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD2.
    remember (bv_unsigned (bbyte inp (i+3))) as V3 eqn:DV3.
    pose proof (byte_unsigned_range (bbyte inp (i+3))) as HV3. rewrite <- DV3 in HV3.
    pose proof (rd1_at rsegs m B inp (i+3) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD3.
    remember (bv_unsigned (bbyte inp (i+4))) as V4 eqn:DV4.
    pose proof (byte_unsigned_range (bbyte inp (i+4))) as HV4. rewrite <- DV4 in HV4.
    pose proof (rd1_at rsegs m B inp (i+4) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD4.
    remember (bv_unsigned (bbyte inp (i+5))) as V5 eqn:DV5.
    pose proof (byte_unsigned_range (bbyte inp (i+5))) as HV5. rewrite <- DV5 in HV5.
    pose proof (rd1_at rsegs m B inp (i+5) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD5.
    remember (bv_unsigned (bbyte inp (i+6))) as V6 eqn:DV6.
    pose proof (byte_unsigned_range (bbyte inp (i+6))) as HV6. rewrite <- DV6 in HV6.
    pose proof (rd1_at rsegs m B inp (i+6) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD6.
    remember (bv_unsigned (bbyte inp (i+7))) as V7 eqn:DV7.
    pose proof (byte_unsigned_range (bbyte inp (i+7))) as HV7. rewrite <- DV7 in HV7.
    pose proof (rd1_at rsegs m B inp (i+7) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD7.
    remember (bv_unsigned (bbyte inp (i+8))) as V8 eqn:DV8.
    pose proof (byte_unsigned_range (bbyte inp (i+8))) as HV8. rewrite <- DV8 in HV8.
    pose proof (rd1_at rsegs m B inp (i+8) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD8.
    remember (bv_unsigned (bbyte inp (i+9))) as V9 eqn:DV9.
    pose proof (byte_unsigned_range (bbyte inp (i+9))) as HV9. rewrite <- DV9 in HV9.
    pose proof (rd1_at rsegs m B inp (i+9) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD9.
    remember (bv_unsigned (bbyte inp (i+10))) as V10 eqn:DV10.
    pose proof (byte_unsigned_range (bbyte inp (i+10))) as HV10. rewrite <- DV10 in HV10.
    pose proof (rd1_at rsegs m B inp (i+10) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD10.
    remember (bv_unsigned (bbyte inp (i+11))) as V11 eqn:DV11.
    pose proof (byte_unsigned_range (bbyte inp (i+11))) as HV11. rewrite <- DV11 in HV11.
    pose proof (rd1_at rsegs m B inp (i+11) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD11.
    remember (bv_unsigned (bbyte inp (i+12))) as V12 eqn:DV12.
    pose proof (byte_unsigned_range (bbyte inp (i+12))) as HV12. rewrite <- DV12 in HV12.
    pose proof (rd1_at rsegs m B inp (i+12) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD12.
    remember (bv_unsigned (bbyte inp (i+13))) as V13 eqn:DV13.
    pose proof (byte_unsigned_range (bbyte inp (i+13))) as HV13. rewrite <- DV13 in HV13.
    pose proof (rd1_at rsegs m B inp (i+13) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD13.
    remember (bv_unsigned (bbyte inp (i+14))) as V14 eqn:DV14.
    pose proof (byte_unsigned_range (bbyte inp (i+14))) as HV14. rewrite <- DV14 in HV14.
    pose proof (rd1_at rsegs m B inp (i+14) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD14.
    remember (bv_unsigned (bbyte inp (i+15))) as V15 eqn:DV15.
    pose proof (byte_unsigned_range (bbyte inp (i+15))) as HV15. rewrite <- DV15 in HV15.
    pose proof (rd1_at rsegs m B inp (i+15) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD15.
    remember (a+V0)%Z as A1 eqn:DA1. remember (b+A1)%Z as S1 eqn:DS1.
    assert (HA1 : (0 <= A1 < 2^64)%Z) by (rewrite DA1;lia).
    assert (HS1 : (0 <= S1 < 2^64)%Z) by (rewrite DS1,DA1;lia).
    remember (A1+V1)%Z as A2 eqn:DA2. remember (S1+A2)%Z as S2 eqn:DS2.
    assert (HA2 : (0 <= A2 < 2^64)%Z) by (rewrite DA2,DA1;lia).
    assert (HS2 : (0 <= S2 < 2^64)%Z) by (rewrite DS2,DS1,DA2,DA1;lia).
    remember (A2+V2)%Z as A3 eqn:DA3. remember (S2+A3)%Z as S3 eqn:DS3.
    assert (HA3 : (0 <= A3 < 2^64)%Z) by (rewrite DA3,DA2,DA1;lia).
    assert (HS3 : (0 <= S3 < 2^64)%Z) by (rewrite DS3,DS2,DS1,DA3,DA2,DA1;lia).
    remember (A3+V3)%Z as A4 eqn:DA4. remember (S3+A4)%Z as S4 eqn:DS4.
    assert (HA4 : (0 <= A4 < 2^64)%Z) by (rewrite DA4,DA3,DA2,DA1;lia).
    assert (HS4 : (0 <= S4 < 2^64)%Z) by (rewrite DS4,DS3,DS2,DS1,DA4,DA3,DA2,DA1;lia).
    remember (A4+V4)%Z as A5 eqn:DA5. remember (S4+A5)%Z as S5 eqn:DS5.
    assert (HA5 : (0 <= A5 < 2^64)%Z) by (rewrite DA5,DA4,DA3,DA2,DA1;lia).
    assert (HS5 : (0 <= S5 < 2^64)%Z) by (rewrite DS5,DS4,DS3,DS2,DS1,DA5,DA4,DA3,DA2,DA1;lia).
    remember (A5+V5)%Z as A6 eqn:DA6. remember (S5+A6)%Z as S6 eqn:DS6.
    assert (HA6 : (0 <= A6 < 2^64)%Z) by (rewrite DA6,DA5,DA4,DA3,DA2,DA1;lia).
    assert (HS6 : (0 <= S6 < 2^64)%Z) by (rewrite DS6,DS5,DS4,DS3,DS2,DS1,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    remember (A6+V6)%Z as A7 eqn:DA7. remember (S6+A7)%Z as S7 eqn:DS7.
    assert (HA7 : (0 <= A7 < 2^64)%Z) by (rewrite DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    assert (HS7 : (0 <= S7 < 2^64)%Z) by (rewrite DS7,DS6,DS5,DS4,DS3,DS2,DS1,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    remember (A7+V7)%Z as A8 eqn:DA8. remember (S7+A8)%Z as S8 eqn:DS8.
    assert (HA8 : (0 <= A8 < 2^64)%Z) by (rewrite DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    assert (HS8 : (0 <= S8 < 2^64)%Z) by (rewrite DS8,DS7,DS6,DS5,DS4,DS3,DS2,DS1,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    remember (A8+V8)%Z as A9 eqn:DA9. remember (S8+A9)%Z as S9 eqn:DS9.
    assert (HA9 : (0 <= A9 < 2^64)%Z) by (rewrite DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    assert (HS9 : (0 <= S9 < 2^64)%Z) by (rewrite DS9,DS8,DS7,DS6,DS5,DS4,DS3,DS2,DS1,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    remember (A9+V9)%Z as A10 eqn:DA10. remember (S9+A10)%Z as S10 eqn:DS10.
    assert (HA10 : (0 <= A10 < 2^64)%Z) by (rewrite DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    assert (HS10 : (0 <= S10 < 2^64)%Z) by (rewrite DS10,DS9,DS8,DS7,DS6,DS5,DS4,DS3,DS2,DS1,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    remember (A10+V10)%Z as A11 eqn:DA11. remember (S10+A11)%Z as S11 eqn:DS11.
    assert (HA11 : (0 <= A11 < 2^64)%Z) by (rewrite DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    assert (HS11 : (0 <= S11 < 2^64)%Z) by (rewrite DS11,DS10,DS9,DS8,DS7,DS6,DS5,DS4,DS3,DS2,DS1,DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    remember (A11+V11)%Z as A12 eqn:DA12. remember (S11+A12)%Z as S12 eqn:DS12.
    assert (HA12 : (0 <= A12 < 2^64)%Z) by (rewrite DA12,DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    assert (HS12 : (0 <= S12 < 2^64)%Z) by (rewrite DS12,DS11,DS10,DS9,DS8,DS7,DS6,DS5,DS4,DS3,DS2,DS1,DA12,DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    remember (A12+V12)%Z as A13 eqn:DA13. remember (S12+A13)%Z as S13 eqn:DS13.
    assert (HA13 : (0 <= A13 < 2^64)%Z) by (rewrite DA13,DA12,DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    assert (HS13 : (0 <= S13 < 2^64)%Z) by (rewrite DS13,DS12,DS11,DS10,DS9,DS8,DS7,DS6,DS5,DS4,DS3,DS2,DS1,DA13,DA12,DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    remember (A13+V13)%Z as A14 eqn:DA14. remember (S13+A14)%Z as S14 eqn:DS14.
    assert (HA14 : (0 <= A14 < 2^64)%Z) by (rewrite DA14,DA13,DA12,DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    assert (HS14 : (0 <= S14 < 2^64)%Z) by (rewrite DS14,DS13,DS12,DS11,DS10,DS9,DS8,DS7,DS6,DS5,DS4,DS3,DS2,DS1,DA14,DA13,DA12,DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    remember (A14+V14)%Z as A15 eqn:DA15. remember (S14+A15)%Z as S15 eqn:DS15.
    assert (HA15 : (0 <= A15 < 2^64)%Z) by (rewrite DA15,DA14,DA13,DA12,DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    assert (HS15 : (0 <= S15 < 2^64)%Z) by (rewrite DS15,DS14,DS13,DS12,DS11,DS10,DS9,DS8,DS7,DS6,DS5,DS4,DS3,DS2,DS1,DA15,DA14,DA13,DA12,DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    remember (A15+V15)%Z as A16 eqn:DA16. remember (S15+A16)%Z as S16 eqn:DS16.
    assert (HA16 : (0 <= A16 < 2^64)%Z) by (rewrite DA16,DA15,DA14,DA13,DA12,DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    assert (HS16 : (0 <= S16 < 2^64)%Z) by (rewrite DS16,DS15,DS14,DS13,DS12,DS11,DS10,DS9,DS8,DS7,DS6,DS5,DS4,DS3,DS2,DS1,DA16,DA15,DA14,DA13,DA12,DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1;lia).
    assert (EA : A16 = adler_block16_a inp i a b).
    { unfold adler_block16_a,adler_block16_bytes. cbn [adler_raw fst snd]. rewrite <-DV0,<-DV1,<-DV2,<-DV3,<-DV4,<-DV5,<-DV6,<-DV7,<-DV8,<-DV9,<-DV10,<-DV11,<-DV12,<-DV13,<-DV14,<-DV15,DA16,DA15,DA14,DA13,DA12,DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1. ring. }
    assert (ES : S16 = adler_block16_b inp i a b).
    { unfold adler_block16_b,adler_block16_bytes. cbn [adler_raw fst snd]. rewrite <-DV0,<-DV1,<-DV2,<-DV3,<-DV4,<-DV5,<-DV6,<-DV7,<-DV8,<-DV9,<-DV10,<-DV11,<-DV12,<-DV13,<-DV14,<-DV15,DS16,DS15,DS14,DS13,DS12,DS11,DS10,DS9,DS8,DS7,DS6,DS5,DS4,DS3,DS2,DS1,DA16,DA15,DA14,DA13,DA12,DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1. ring. }
    (* 0x15040 lbu a6, 0(a5) *)
    zstep. try rewrite <- DV0.
    (* 0x15044 lbu a7, 1(a5) *)
    zstep. try rewrite <- DV1.
    (* 0x15048 lbu t0, 2(a5) *)
    zstep. try rewrite <- DV2.
    (* 0x1504c lbu t1, 3(a5) *)
    zstep. try rewrite <- DV3.
    (* 0x15050 add a4, a4, a6 *)
    zstep. try rewrite <- DA1.
    (* 0x15054 add a3, a4, a3 *)
    zstep. replace (A1+b)%Z with (b+A1)%Z by ring. try rewrite <- DS1.
    (* 0x15058 add a4, a4, a7 *)
    zstep. try rewrite <- DA2.
    (* 0x1505c add a3, a3, a4 *)
    zstep. replace (A2+S1)%Z with (S1+A2)%Z by ring. try rewrite <- DS2.
    (* 0x15060 add a4, a4, t0 *)
    zstep. try rewrite <- DA3.
    (* 0x15064 add a3, a3, a4 *)
    zstep. replace (A3+S2)%Z with (S2+A3)%Z by ring. try rewrite <- DS3.
    (* 0x15068 add a4, a4, t1 *)
    zstep. try rewrite <- DA4.
    (* 0x1506c lbu a6, 4(a5) *)
    zstep. try rewrite <- DV4.
    (* 0x15070 lbu a7, 5(a5) *)
    zstep. try rewrite <- DV5.
    (* 0x15074 lbu t0, 6(a5) *)
    zstep. try rewrite <- DV6.
    (* 0x15078 lbu t1, 7(a5) *)
    zstep. try rewrite <- DV7.
    (* 0x1507c add a3, a3, a4 *)
    zstep. replace (A4+S3)%Z with (S3+A4)%Z by ring. try rewrite <- DS4.
    (* 0x15080 add a4, a4, a6 *)
    zstep. try rewrite <- DA5.
    (* 0x15084 add a3, a3, a4 *)
    zstep. replace (A5+S4)%Z with (S4+A5)%Z by ring. try rewrite <- DS5.
    (* 0x15088 add a4, a4, a7 *)
    zstep. try rewrite <- DA6.
    (* 0x1508c add a3, a3, a4 *)
    zstep. replace (A6+S5)%Z with (S5+A6)%Z by ring. try rewrite <- DS6.
    (* 0x15090 add a4, a4, t0 *)
    zstep. try rewrite <- DA7.
    (* 0x15094 add a3, a3, a4 *)
    zstep. replace (A7+S6)%Z with (S6+A7)%Z by ring. try rewrite <- DS7.
    (* 0x15098 add a4, a4, t1 *)
    zstep. try rewrite <- DA8.
    (* 0x1509c lbu a6, 8(a5) *)
    zstep. try rewrite <- DV8.
    (* 0x150a0 lbu a7, 9(a5) *)
    zstep. try rewrite <- DV9.
    (* 0x150a4 lbu t0, 0xa(a5) *)
    zstep. try rewrite <- DV10.
    (* 0x150a8 lbu t1, 0xb(a5) *)
    zstep. try rewrite <- DV11.
    (* 0x150ac add a3, a3, a4 *)
    zstep. replace (A8+S7)%Z with (S7+A8)%Z by ring. try rewrite <- DS8.
    (* 0x150b0 add a4, a4, a6 *)
    zstep. try rewrite <- DA9.
    (* 0x150b4 add a3, a3, a4 *)
    zstep. replace (A9+S8)%Z with (S8+A9)%Z by ring. try rewrite <- DS9.
    (* 0x150b8 add a4, a4, a7 *)
    zstep. try rewrite <- DA10.
    (* 0x150bc add a3, a3, a4 *)
    zstep. replace (A10+S9)%Z with (S9+A10)%Z by ring. try rewrite <- DS10.
    (* 0x150c0 add a4, a4, t0 *)
    zstep. try rewrite <- DA11.
    (* 0x150c4 add a3, a3, a4 *)
    zstep. replace (A11+S10)%Z with (S10+A11)%Z by ring. try rewrite <- DS11.
    (* 0x150c8 add a4, a4, t1 *)
    zstep. try rewrite <- DA12.
    (* 0x150cc lbu a6, 0xc(a5) *)
    zstep. try rewrite <- DV12.
    (* 0x150d0 lbu a7, 0xd(a5) *)
    zstep. try rewrite <- DV13.
    (* 0x150d4 lbu t0, 0xe(a5) *)
    zstep. try rewrite <- DV14.
    (* 0x150d8 lbu t1, 0xf(a5) *)
    zstep. try rewrite <- DV15.
    (* 0x150dc add a3, a3, a4 *)
    zstep. replace (A12+S11)%Z with (S11+A12)%Z by ring. try rewrite <- DS12.
    (* 0x150e0 add a4, a4, a6 *)
    zstep. try rewrite <- DA13.
    (* 0x150e4 add a3, a3, a4 *)
    zstep. replace (A13+S12)%Z with (S12+A13)%Z by ring. try rewrite <- DS13.
    (* 0x150e8 add a4, a4, a7 *)
    zstep. try rewrite <- DA14.
    (* 0x150ec add a3, a3, a4 *)
    zstep. replace (A14+S13)%Z with (S13+A14)%Z by ring. try rewrite <- DS14.
    (* 0x150f0 add a4, a4, t0 *)
    zstep. try rewrite <- DA15.
    (* 0x150f4 addi a2, a2, -0x10 *)
    zstep. 
    (* 0x150f8 add a3, a3, a4 *)
    zstep. replace (A15+S14)%Z with (S14+A15)%Z by ring. try rewrite <- DS15.
    (* 0x150fc add a4, a4, t1 *)
    zstep. try rewrite <- DA16.
    (* 0x15100 add a3, a3, a4 *)
    zstep. replace (A16+S15)%Z with (S15+A16)%Z by ring. try rewrite <- DS16.
    (* 0x15104 addi a5, a5, 0x10 *)
    zstep. 
    rewrite <- EA,<- ES in CONT. rewrite DS16,DS15,DS14,DS13,DS12,DS11,DS10,DS9,DS8,DS7,DS6,DS5,DS4,DS3,DS2,DS1,DA16,DA15,DA14,DA13,DA12,DA11,DA10,DA9,DA8,DA7,DA6,DA5,DA4,DA3,DA2,DA1,DV0,DV1,DV2,DV3,DV4,DV5,DV6,DV7,DV8,DV9,DV10,DV11,DV12,DV13,DV14,DV15 in CONT.
    replace (a+bv_unsigned (bbyte inp i)+b)%Z with (b+(a+bv_unsigned (bbyte inp i)))%Z by ring.
    apply CONT.
  Qed.
End AdlerBlock_inner.
