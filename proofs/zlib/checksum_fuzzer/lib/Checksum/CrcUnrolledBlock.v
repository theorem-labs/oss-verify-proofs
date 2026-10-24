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

From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import CrcUnrolledBytes CrcChunks.
Section UnrolledBlock.
  Variables (ra sp gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (B : Z) (inp : list byte).
  Hypothesis INP : bytes_at rsegs m B inp.
  Hypothesis TABLE : bytes_at rsegs m CRC_TABS crc_table_bytes.
  Hypothesis TOP : (B+Z.of_nat (length inp) < 2^64)%Z.
  Variable Q : machine_state -> Prop.
  Notation L := (Z.of_nat (length inp)).
  Notation AT pc x5 x6 x11 x12 x13 x14 x16 x17 :=
    (MS (mkR ra sp gp tp x5 x6 t2 s0 s1 (Z_to_bv 64 CRC_TABS)
      x11 x12 x13 x14 (Z_to_bv 64 7) x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
  Theorem unrolled8_update : forall (i q : Z) x5 x6 x13 x16 x17,
    (0 <= i)%Z -> (i+8 <= L)%Z -> (0 <= q < 2^32)%Z ->
    (forall x5' x6' x16' x17', evt rsegs Q
      (AT 0x14b78 x5' x6' (Z_to_bv 64 (B+(i+8))) (Z_to_bv 64 (L-(i+8))) x13
        (Z_to_bv 64 (eight_crc inp i q)) x16' x17')) ->
    evt rsegs Q (AT 0x14a70 x5 x6 (Z_to_bv 64 (B+i)) (Z_to_bv 64 (L-i)) x13
      (Z_to_bv 64 q) x16 x17).
  Proof.
    intros i q x5 x6 x13 x16 x17 Hi HL Hq CONT.
    pose proof (bytes_at_bound _ _ _ _ INP) as BB.
    rewrite (eight_crc_bytes inp i q Hi HL) in CONT.
    assert (PU : bv_unsigned (Z_to_bv 64 (B+i)) = (B+i)%Z).
    { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. lia. }
    assert (LU : bv_unsigned (Z_to_bv 64 (L-i)) = (L-i)%Z).
    { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. lia. }
    set (q1 := raw_byte q (bbyte inp i)).
    assert (Hq1 : (0 <= q1 < 2^32)%Z) by (unfold q1;apply raw_byte_range;exact Hq).
    set (q2 := raw_byte q1 (bbyte inp (i+1))).
    assert (Hq2 : (0 <= q2 < 2^32)%Z) by (unfold q2;apply raw_byte_range;exact Hq1).
    set (q3 := raw_byte q2 (bbyte inp (i+2))).
    assert (Hq3 : (0 <= q3 < 2^32)%Z) by (unfold q3;apply raw_byte_range;exact Hq2).
    set (q4 := raw_byte q3 (bbyte inp (i+3))).
    assert (Hq4 : (0 <= q4 < 2^32)%Z) by (unfold q4;apply raw_byte_range;exact Hq3).
    set (q5 := raw_byte q4 (bbyte inp (i+4))).
    assert (Hq5 : (0 <= q5 < 2^32)%Z) by (unfold q5;apply raw_byte_range;exact Hq4).
    set (q6 := raw_byte q5 (bbyte inp (i+5))).
    assert (Hq6 : (0 <= q6 < 2^32)%Z) by (unfold q6;apply raw_byte_range;exact Hq5).
    set (q7 := raw_byte q6 (bbyte inp (i+6))).
    assert (Hq7 : (0 <= q7 < 2^32)%Z) by (unfold q7;apply raw_byte_range;exact Hq6).
    set (q8 := raw_byte q7 (bbyte inp (i+7))).
    assert (Hq8 : (0 <= q8 < 2^32)%Z) by (unfold q8;apply raw_byte_range;exact Hq7).
    pose proof (rd1_at rsegs m B inp i _ INP ltac:(lia) ltac:(lia) eq_refl) as RD0. zstep.
    pose proof (rd1_at rsegs m B inp (i+1) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD1. zstep.
    pose proof (rd1_at rsegs m B inp (i+2) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD2. zstep.
    pose proof (rd1_at rsegs m B inp (i+3) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD3. zstep.
    eapply unrolled_byte_a6 with (start:=0x14a80) (q:=q) (b:=bbyte inp i);
      [exact TABLE|left;reflexivity|exact Hq|].
    intros u0.
    eapply unrolled_byte_a7 with (start:=0x14a9c) (q:=q1) (b:=bbyte inp (i+1));
      [exact TABLE|left;reflexivity|exact Hq1|].
    intros u1.
    eapply unrolled_byte_t0 with (start:=0x14ab8) (q:=q2) (b:=bbyte inp (i+2));
      [exact TABLE|left;reflexivity|exact Hq2|].
    intros u2.
    eapply unrolled_byte_t1 with (start:=0x14ad4) (q:=q3) (b:=bbyte inp (i+3));
      [exact TABLE|reflexivity|exact Hq3|].
    intros u3.
    pose proof (rd1_at rsegs m B inp (i+4) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD4. zstep.
    pose proof (rd1_at rsegs m B inp (i+5) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD5. zstep.
    pose proof (rd1_at rsegs m B inp (i+6) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD6. zstep.
    pose proof (rd1_at rsegs m B inp (i+7) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD7. zstep.
    eapply unrolled_byte_a6 with (start:=0x14b00) (q:=q4) (b:=bbyte inp (i+4));
      [exact TABLE|right;reflexivity|exact Hq4|].
    intros u4.
    eapply unrolled_byte_a7 with (start:=0x14b1c) (q:=q5) (b:=bbyte inp (i+5));
      [exact TABLE|right;reflexivity|exact Hq5|].
    intros u5.
    eapply unrolled_byte_t0 with (start:=0x14b38) (q:=q6) (b:=bbyte inp (i+6));
      [exact TABLE|right;reflexivity|exact Hq6|].
    intros u6.
    eapply unrolled_byte_last with (q:=q7) (b:=bbyte inp (i+7));
      [exact TABLE|exact Hq7|].
    intros u7. rewrite PU,LU.
    replace (B+i+8)%Z with (B+(i+8))%Z by lia.
    replace (L-i-8)%Z with (L-(i+8))%Z by lia.
    apply CONT.
  Qed.
End UnrolledBlock.
