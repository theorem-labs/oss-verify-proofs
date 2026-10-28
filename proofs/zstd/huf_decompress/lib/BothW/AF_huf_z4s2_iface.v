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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_z4s_iface AF_huf_z4s3_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
Definition z4strm (L pt b : Z) : Prop := 0 <= pt /\ (pt = 0 \/ pt + 8 <= L) /\ 0 <= b < 2^31.

Section CANSEC1. Context {rc : runConstT}.
Section Z4S2I.
  Variable RNG : footprint.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Notation Zw z := (Z_to_bv 64 z) (only parsing).
  Notation Z4SF' := (Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs).
  Notation ZS pc mm r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29
             r30 r31 :=
    (MS (mkR r1 (Z_to_bv 64 (SP + -384)) gp tp r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23
             r24 r25 r26 r27 r28 r29 r30 r31) FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)) (only parsing).

  Definition z4s2_goal (Q : machine_state -> Prop) : Prop :=
    forall (l1 l2 l3 : Z) (q1 q2 q3 q4 pt1 pt2 pt3 pt4 b1 b2 b3 b4 : Z) (c1 c2 c3 c4 : word) (jp1 jp2 jp3 jp4 : list byte)
           (w0 w4 w5 w7 w8 w11 w12 : word) (mm : amem)
           (x1 x5 x6 x7 x8 x10 x11 x13 x14 x15 x16 x20 x22 x23 x24 x25 x26 x27 x28 x29 x31 : word),
    Z4SF' mm (SPD w0 (Zw (DST + 3 * seg)) (Zw (tl + 256 * mtl)) (Zw (DST + dcap - 7)) w4 w5 (Zw (DST + dcap)) w7 w8
                  (Zw (DST + seg)) (Zw (DST + 2 * seg)) w11 w12 (Zw (DT + 4)) (Zw dcap))
          (BD4A c4 (Zw b4) jp4 (Zw (SS + 6 + l1 + l2 + l3 + pt4)) (Zw (SS + 6 + l1 + l2 + l3)) (Zw (SS + 6 + l1 + l2 + l3 + 8)))
          (BD4A c3 (Zw b3) jp3 (Zw (SS + 6 + l1 + l2 + pt3)) (Zw (SS + 6 + l1 + l2)) (Zw (SS + 6 + l1 + l2 + 8)))
          (BD4A c2 (Zw b2) jp2 (Zw (SS + 6 + l1 + pt2)) (Zw (SS + 6 + l1)) (Zw (SS + 6 + l1 + 8)))
          (BD4A c1 (Zw b1) jp1 (Zw (SS + 6 + pt1)) (Zw (SS + 6)) (Zw (SS + 6 + 8))) ->
    1 <= l1 -> 1 <= l2 -> 1 <= l3 -> 6 + l1 + l2 + l3 + 1 <= n -> 6 <= dcap -> 3 * seg <= dcap ->
    0 <= q1 <= dcap -> 0 <= q2 <= dcap -> 0 <= q3 <= dcap -> 0 <= q4 <= dcap ->
    z4strm l1 pt1 b1 -> z4strm l2 pt2 b2 -> z4strm l3 pt3 b3 -> z4strm (n - (6 + l1 + l2 + l3)) pt4 b4 ->
    (forall mm' (spl bd4 bd3 bd2 bd1 : list cell) (r : Z)
            (z1 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 : word),
       Z4SF' mm' spl bd4 bd3 bd2 bd1 -> r = dcap \/ r = 2^64 - 20 ->
       evtF bsegs RNG Q (ZS AZ4_DEPI mm' z1 (Zw r) z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24
                            z25 z26 z27 z28 z29 z30 z31)) ->
    evtF bsegs RNG Q (ZS AZ4_C0 mm x1 x5 x6 x7 x8 (Zw (DST + q4)) x10 x11 (Zw (DST + q1)) x13 x14 x15 x16 (Zw (DST + seg))
                         (Zw (DST + q3)) (Zw (DST + q2)) x20 (Zw AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 (Zw (DT + 4)) x31).
End Z4S2I.
End CANSEC1.
