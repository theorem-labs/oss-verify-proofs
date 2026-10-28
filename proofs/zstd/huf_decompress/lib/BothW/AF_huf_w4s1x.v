(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseRdKit HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Startup_kit.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.

Definition AW4_LHEAD : Z := 0x89de4.
Definition AW4_LEND : Z := 0x8a93c.
Definition AW4_LEND3 : Z := 0x8a940.
Definition AW4_LEX : Z := 0x8ac58.
Definition AW4_LFIN : Z := 0x8ac7c.

Lemma w4s_st_zero : forall a b c d, (a = 0 \/ a = 3) -> (b = 0 \/ b = 3) -> (c = 0 \/ c = 3) -> (d = 0 \/ d = 3) ->
  Z.lor (Z.lor b a) (Z.lor c d) = 0 -> a = 0 /\ b = 0 /\ c = 0 /\ d = 0.
Proof.
  intros a b c d Ha Hb Hc Hd H.
  destruct Ha as [->| ->], Hb as [->| ->], Hc as [->| ->], Hd as [->| ->]; vm_compute in H; try discriminate; auto.
Qed.

(* [comment removed for export] *)
Lemma w4s_end3 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 : word),
  (Z.lor (Z.lor (bv_unsigned r11) (bv_unsigned r25)) (Z.lor (bv_unsigned r31) (bv_unsigned r16)) = 0 ->
     evtF bsegs RNG Q (MS (mkR r15 r2 r3 r4 r5 r6 r7 r8 r9 r10
                              (Z_to_bv 64 (Z.lor (Z.lor (bv_unsigned r11) (bv_unsigned r25))
                                                 (Z.lor (bv_unsigned r31) (bv_unsigned r16))))
                              r12 r13 r14 r15 (Z_to_bv 64 (Z.lor (bv_unsigned r31) (bv_unsigned r16))) r17 r13 r14 r20 r21 r22 r23
                              r24 r12 r26 r27 r28 r29 r30 r31) F (Z_to_bv 64 AW4_LHEAD) fc None mm (seg_rom bsegs))) ->
  (Z.lor (Z.lor (bv_unsigned r11) (bv_unsigned r25)) (Z.lor (bv_unsigned r31) (bv_unsigned r16)) <> 0 ->
     evtF bsegs RNG Q (MS (mkR r15 r2 r3 r4 r5 r6 r7 r8 r9 r10
                              (Z_to_bv 64 (Z.lor (Z.lor (bv_unsigned r11) (bv_unsigned r25))
                                                 (Z.lor (bv_unsigned r31) (bv_unsigned r16))))
                              r12 r13 r14 r15 (Z_to_bv 64 (Z.lor (bv_unsigned r31) (bv_unsigned r16))) r17 r13 r14 r20 r21 r22 r23
                              r24 r12 r26 r27 r28 r29 r30 r31) F (Z_to_bv 64 AW4_LEX) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
                           r27 r28 r29 r30 r31) F (Z_to_bv 64 AW4_LEND3) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
    r27 r28 r29 r30 r31 KL KN.
  unfold AW4_LEND3. do 8 zstep.
  if_cases K2.
  - apply KL. zify_cond K2. exact K2.
  - zstep. apply KN. zify_cond K2. exact K2.
Qed.

Lemma w4s_end : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 : word),
  (bv_unsigned r8 <= bv_unsigned r9 ->
     evtF bsegs RNG Q (MS (mkR r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
                              r27 r28 r29 r30 r31) F (Z_to_bv 64 AW4_LEX) fc None mm (seg_rom bsegs))) ->
  (bv_unsigned r9 < bv_unsigned r8 ->
     Z.lor (Z.lor (bv_unsigned r11) (bv_unsigned r25)) (Z.lor (bv_unsigned r31) (bv_unsigned r16)) = 0 ->
     evtF bsegs RNG Q (MS (mkR r15 r2 r3 r4 r5 r6 r7 r8 r9 r10
                              (Z_to_bv 64 (Z.lor (Z.lor (bv_unsigned r11) (bv_unsigned r25))
                                                 (Z.lor (bv_unsigned r31) (bv_unsigned r16))))
                              r12 r13 r14 r15 (Z_to_bv 64 (Z.lor (bv_unsigned r31) (bv_unsigned r16))) r17 r13 r14 r20 r21 r22 r23
                              r24 r12 r26 r27 r28 r29 r30 r31) F (Z_to_bv 64 AW4_LHEAD) fc None mm (seg_rom bsegs))) ->
  (bv_unsigned r9 < bv_unsigned r8 ->
     Z.lor (Z.lor (bv_unsigned r11) (bv_unsigned r25)) (Z.lor (bv_unsigned r31) (bv_unsigned r16)) <> 0 ->
     evtF bsegs RNG Q (MS (mkR r15 r2 r3 r4 r5 r6 r7 r8 r9 r10
                              (Z_to_bv 64 (Z.lor (Z.lor (bv_unsigned r11) (bv_unsigned r25))
                                                 (Z.lor (bv_unsigned r31) (bv_unsigned r16))))
                              r12 r13 r14 r15 (Z_to_bv 64 (Z.lor (bv_unsigned r31) (bv_unsigned r16))) r17 r13 r14 r20 r21 r22 r23
                              r24 r12 r26 r27 r28 r29 r30 r31) F (Z_to_bv 64 AW4_LEX) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
                           r27 r28 r29 r30 r31) F (Z_to_bv 64 AW4_LEND) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26
    r27 r28 r29 r30 r31 KX KL KN.
  unfold AW4_LEND. zstep.
  if_cases KA.
  - apply KX. zify_cond KA. lia.
  - zify_cond KA. apply w4s_end3; [apply KL; lia | apply KN; lia].
Qed.

(* [comment removed for export] *)
Lemma w4s_exit : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (r1 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 : word)
    (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 : word) (P : Z),
  rw_cells bsegs mm P [C8 f0; C8 f1; C8 f2; C8 f3; C8 f4; C8 f5; C8 f6; C8 f7; C8 f8; C8 f9; C8 f10; C8 f11; C8 f12] ->
  mem_inv bsegs mm -> rng RNG P 104 -> 1048576 <= P -> P + 104 <= 2^47 ->
  evtF bsegs RNG Q (MS (mkR f2 (Z_to_bv 64 P) r3 r4 r5 r6 r7 (Z_to_bv 64 (bv_unsigned f8 + bv_unsigned r20)) r9 r10 r11 r12
                           r13 r14 r15 r16 r17 (Z_to_bv 64 (bv_unsigned r21 + bv_unsigned r20)) f1
                           (Z_to_bv 64 (bv_unsigned f2 + bv_unsigned r20)) r21 (Z_to_bv 64 (bv_unsigned f11 + bv_unsigned r20))
                           f8 r24 r25 r26 f4 r28 r29 r30 r31) F (Z_to_bv 64 AW4_LFIN) fc None mm (seg_rom bsegs)) ->
  evtF bsegs RNG Q (MS (mkR r1 (Z_to_bv 64 P) r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23
                           r24 r25 r26 r27 r28 r29 r30 r31) F (Z_to_bv 64 AW4_LEX) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc r1 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28
    r29 r30 r31 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 P FRC MI RP P1 P2.
  intros K. unfold AW4_LEX.
  do 9 zstep.
  exact K.
Qed.

End CANSEC1.
