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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s2_iface AF_huf_z4d_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXTac KXGoM.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
Definition z1hd (L pt b : Z) : Prop := 0 <= pt /\ (pt = 0 \/ pt + 8 <= L) /\ 0 <= b <= 64 /\ (8 <= pt -> b <= 8).

(* [comment removed for export] *)
Definition z1ops (SEG q1 q2 q3 q4 : Z) : Prop :=
  0 <= q1 /\ q1 <= 2 * (q4 - 3 * SEG) /\ SEG <= q2 /\ q2 - SEG <= 2 * (q4 - 3 * SEG) /\
  2 * SEG <= q3 /\ q3 - 2 * SEG <= 2 * (q4 - 3 * SEG) /\ 3 * SEG <= q4.

Section CANSEC1. Context {rc : runConstT}.
Section Z4L.
  Variables (RNG : footprint) (Q : machine_state -> Prop) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (SP DST dcap seg DT tl mtl dl DBL DBH : Z) (cbs : list byte).
  Notation Zw z := (Z_to_bv 64 z) (only parsing).
  Notation WM := [(SP + -384, SP + -104); (DST, DST + dcap)].
  Notation ZL pc mm r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29
             r30 r31 :=
    (MS (mkR r1 (Zw (SP + -384)) gp tp r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23
             r24 r25 r26 r27 r28 r29 r30 r31) FR (Zw pc) fc None mm (seg_rom bsegs)) (only parsing).

  Definition z4L_ctx : Prop :=
    rng RNG (SP + -384) 384 /\ zlen cbs = 4 * 2^tl /\
    DBL <= DT + 4 /\ DT + 4 + 4 * 2^tl <= DBH /\ rng RNG (shad DBL) (shlen (DBH - DBL + 7)) /\
    DBL mod 8 = 0 /\ 4096 <= DBL /\ DBH <= 2^47 /\
    rng RNG (shad DST) (shlen (dcap + 7)) /\ DST mod 8 = 0 /\
    rng RNG (DT + 4) (4 * 2^tl) /\ rng RNG DST dcap /\ rng_aimg RNG /\
    4096 <= DST /\ AIMG_HI <= DST /\ DST + dcap + 8 <= 2^47 /\ 4096 <= DT /\ DT + 4 + 4 * 2^tl <= 2^47 /\
    8192 <= SP <= 2^47 /\
    KXGoM.apart DST dcap (SP + -384) 384 /\ KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -384) 384 /\
    KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) /\ KXGoM.apart DST dcap AIMG_LO (AIMG_HI - AIMG_LO) /\
    (DT + 4) mod 4 = 0 /\ 6 <= dcap < 2^32 /\ 0 <= seg <= 2^32 /\ dl = tl + 256 * mtl /\
    1 <= tl <= 12 /\ 1 <= mtl <= 12 /\ 2 <= 2^tl <= 4096 /\
    DST + dcap <= ATOP /\ DT + 4 + 4 * 2^tl <= ATOP /\
    KXGoM.apart (SP + -384) 384 ASHOFF (ATOP / 8 + 1) /\ KXGoM.apart DST dcap ASHOFF (ATOP / 8 + 1) /\
    KXGoM.apart (DT + 4) (4 * 2^tl) ASHOFF (ATOP / 8 + 1) /\ DBH <= ATOP.

  Definition z4L_mem (mm : amem) (w0 w4 w5 w7 : word) (c1 c2 c3 c4 b1 b2 b3 b4 p1 p2 p3 p4 : Z)
             (jp1 jp2 jp3 jp4 : list byte) (s1 s2 s3 s4 e1 e2 e3 e4 : word) : Prop :=
    rw_cells bsegs mm (SP + -384) [C8 w0] /\ rw_cells bsegs mm (SP + -376) [C8 (Zw (DST + 3 * seg))] /\
    rw_cells bsegs mm (SP + -368) [C8 (Zw dl)] /\ rw_cells bsegs mm (SP + -360) [C8 (Zw (DST + dcap - 7))] /\
    rw_cells bsegs mm (SP + -352) [C8 w4; C8 w5; C8 (Zw (DST + dcap)); C8 w7] /\
    rw_cells bsegs mm (SP + -320) [C8 (Zw c2)] /\
    rw_cells bsegs mm (SP + -312) [C8 (Zw (DST + seg)); C8 (Zw (DST + 2 * seg))] /\
    rw_cells bsegs mm (SP + -296) [C8 (Zw c4)] /\ rw_cells bsegs mm (SP + -288) [C8 (Zw c3)] /\
    rw_cells bsegs mm (SP + -280) [C8 (Zw (DT + 4)); C8 (Zw dcap)] /\
    rw_cells bsegs mm (SP + -264) (BD4A (Zw c4) (Zw b4) jp4 (Zw p4) s4 e4) /\
    rw_cells bsegs mm (SP + -224) (BD4A (Zw c3) (Zw b3) jp3 (Zw p3) s3 e3) /\
    rw_cells bsegs mm (SP + -184) (BD4A (Zw c2) (Zw b2) jp2 (Zw p2) s2 e2) /\
    rw_cells bsegs mm (SP + -144) (BD4A (Zw c1) (Zw b1) jp1 (Zw p1) s1 e1) /\
    mem_inv bsegs mm /\
    KXTac.ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)] /\ bytes_at bsegs mm (DT + 4) cbs /\
    (exists obuf : list byte, u8arr bsegs mm DST obuf /\ zlen obuf = dcap) /\
    unpoisoned mm DBL DBH /\ unpoisoned mm DST (DST + dcap).

  Definition z4L_bnd (c1 c2 c3 c4 p1 p2 p3 p4 b1 b2 b3 b4 O1 O2 O3 O4 : Z) : Prop :=
    0 <= c1 < 2^64 /\ 0 <= c2 < 2^64 /\ 0 <= c3 < 2^64 /\ 0 <= c4 < 2^64 /\
    0 <= p1 < 2^64 /\ 0 <= p2 < 2^64 /\ 0 <= p3 < 2^64 /\ 0 <= p4 < 2^64 /\
    0 <= b1 <= 64 /\ 0 <= b2 <= 64 /\ 0 <= b3 <= 64 /\ 0 <= b4 <= 64 /\
    DST <= O1 /\ O1 + 8 <= DST + dcap /\ DST <= O2 /\ O2 + 8 <= DST + dcap /\
    DST <= O3 /\ O3 + 8 <= DST + dcap /\ DST <= O4 /\ O4 + 8 <= DST + dcap.

  Definition z4L_md1_goal : Prop :=
    z4L_ctx ->
    forall mm (w0 w4 w5 w7 : word) (c1 c2 c3 c4 p1 p2 p3 p4 b1 b2 b3 b4 O1 O2 O3 O4 : Z)
           (jp1 jp2 jp3 jp4 : list byte) (s1 s2 s3 s4 e1 e2 e3 e4 : word)
           (x8 x10 x11 x13 x17 x22 x25 x27 x28 x29 : word),
    z4L_mem mm w0 w4 w5 w7 c1 c2 c3 c4 b1 b2 b3 b4 p1 p2 p3 p4 jp1 jp2 jp3 jp4 s1 s2 s3 s4 e1 e2 e3 e4 ->
    z4L_bnd c1 c2 c3 c4 p1 p2 p3 p4 b1 b2 b3 b4 O1 O2 O3 O4 ->
    (forall mm' (v0 v4 v5 v7 : word) (d1 d2 d3 d4 : Z) (l1 l2 l3 l4 y11 y13 y20 y27 y29 : word),
       munch WM mm mm' -> wmono bsegs mm mm' ->
       z4L_mem mm' v0 v4 v5 v7 c1 c2 c3 c4 d1 d2 d3 d4 p1 p2 p3 p4 jp1 jp2 jp3 jp4 s1 s2 s3 s4 e1 e2 e3 e4 ->
       1 <= bv_unsigned l1 <= 2 -> 1 <= bv_unsigned l2 <= 2 -> 1 <= bv_unsigned l3 <= 2 -> 1 <= bv_unsigned l4 <= 2 ->
       b1 <= d1 <= b1 + 12 -> b2 <= d2 <= b2 + 12 -> b3 <= d3 <= b3 + 12 -> b4 <= d4 <= b4 + 12 ->
       evtF bsegs RNG Q (ZL 584460 mm' (Zw d2) (Zw (2^61)) (Zw (64 - tl)) (Zw (- DT - 5)) (Zw d1) (Zw O4) (Zw c1) y11
                           (Zw O1) y13 (Zw p1) (Zw p2) (Zw p3) (Zw c2) (Zw O3) (Zw O2) y20 (Zw AZ4_SB) l4 (Zw d3)
                           (Zw d4) l1 l2 y27 l3 y29 (Zw (DT + 4)) (Zw p4))) ->
    evtF bsegs RNG Q (ZL 583740 mm (Zw b2) (Zw (2^61)) (Zw (64 - tl)) (Zw (- DT - 5)) x8 (Zw O4) x10 x11 (Zw O1) x13
                        (Zw p1) (Zw p2) (Zw p3) x17 (Zw O3) (Zw O2) (Zw b3) (Zw AZ4_SB) x22 (Zw c1) (Zw b4) x25 (Zw b1)
                        x27 x28 x29 (Zw (DT + 4)) (Zw p4)).

  Definition z4L_md2_goal : Prop :=
    z4L_ctx ->
    forall mm (w0 w4 w5 w7 : word) (c1 c2 c3 c4 p1 p2 p3 p4 b1 b2 b3 b4 O1 O2 O3 O4 d1 d2 d3 d4 : Z)
           (jp1 jp2 jp3 jp4 : list byte) (s1 s2 s3 s4 e1 e2 e3 e4 : word)
           (l1 l2 l3 l4 x11 x13 x20 x27 x29 : word),
    z4L_mem mm w0 w4 w5 w7 c1 c2 c3 c4 d1 d2 d3 d4 p1 p2 p3 p4 jp1 jp2 jp3 jp4 s1 s2 s3 s4 e1 e2 e3 e4 ->
    z4L_bnd c1 c2 c3 c4 p1 p2 p3 p4 b1 b2 b3 b4 O1 O2 O3 O4 ->
    1 <= bv_unsigned l1 <= 2 -> 1 <= bv_unsigned l2 <= 2 -> 1 <= bv_unsigned l3 <= 2 -> 1 <= bv_unsigned l4 <= 2 ->
    b1 <= d1 <= b1 + 12 -> b2 <= d2 <= b2 + 12 -> b3 <= d3 <= b3 + 12 -> b4 <= d4 <= b4 + 12 ->
    (forall mm' (v0 v4 v5 v7 : word) (U1 U2 U3 U4 f1 f2 f3 f4 : Z) (l5 l6 l7 l8 y1 y11 y13 y28 y29 : word),
       munch WM mm mm' -> wmono bsegs mm mm' ->
       z4L_mem mm' v0 v4 v5 v7 c1 c2 c3 c4 f1 f2 f3 f4 p1 p2 p3 p4 jp1 jp2 jp3 jp4 s1 s2 s3 s4 e1 e2 e3 e4 ->
       1 <= bv_unsigned l5 <= 2 -> 1 <= bv_unsigned l6 <= 2 -> 1 <= bv_unsigned l7 <= 2 -> 1 <= bv_unsigned l8 <= 2 ->
       O1 + 1 <= U1 <= O1 + 2 -> O2 + 1 <= U2 <= O2 + 2 -> O3 + 1 <= U3 <= O3 + 2 -> O4 + 1 <= U4 <= O4 + 2 ->
       b1 <= f1 <= b1 + 24 -> b2 <= f2 <= b2 + 24 -> b3 <= f3 <= b3 + 24 -> b4 <= f4 <= b4 + 24 ->
       evtF bsegs RNG Q (ZL 585188 mm' y1 (Zw (2^61)) (Zw (64 - tl)) (Zw (- DT - 5)) (Zw f1) (Zw U4) (Zw c1) y11
                           (Zw U1) y13 (Zw p1) (Zw p2) (Zw p3) (Zw c2) (Zw U3) (Zw U2) (Zw f2) (Zw AZ4_SB) l8 (Zw f3)
                           (Zw f4) l5 l6 l7 y28 y29 (Zw (DT + 4)) (Zw p4))) ->
    evtF bsegs RNG Q (ZL 584460 mm (Zw d2) (Zw (2^61)) (Zw (64 - tl)) (Zw (- DT - 5)) (Zw d1) (Zw O4) (Zw c1) x11
                        (Zw O1) x13 (Zw p1) (Zw p2) (Zw p3) (Zw c2) (Zw O3) (Zw O2) x20 (Zw AZ4_SB) l4 (Zw d3)
                        (Zw d4) l1 l2 x27 l3 x29 (Zw (DT + 4)) (Zw p4)).

  Definition z4L_md3_goal : Prop :=
    z4L_ctx ->
    forall mm (w0 w4 w5 w7 : word) (c1 c2 c3 c4 p1 p2 p3 p4 b1 b2 b3 b4 O1 O2 O3 O4 U1 U2 U3 U4 f1 f2 f3 f4 : Z)
           (jp1 jp2 jp3 jp4 : list byte) (s1 s2 s3 s4 e1 e2 e3 e4 : word)
           (l5 l6 l7 l8 x1 x11 x13 x28 x29 : word),
    z4L_mem mm w0 w4 w5 w7 c1 c2 c3 c4 f1 f2 f3 f4 p1 p2 p3 p4 jp1 jp2 jp3 jp4 s1 s2 s3 s4 e1 e2 e3 e4 ->
    z4L_bnd c1 c2 c3 c4 p1 p2 p3 p4 b1 b2 b3 b4 O1 O2 O3 O4 ->
    1 <= bv_unsigned l5 <= 2 -> 1 <= bv_unsigned l6 <= 2 -> 1 <= bv_unsigned l7 <= 2 -> 1 <= bv_unsigned l8 <= 2 ->
    O1 + 1 <= U1 <= O1 + 2 -> O2 + 1 <= U2 <= O2 + 2 -> O3 + 1 <= U3 <= O3 + 2 -> O4 + 1 <= U4 <= O4 + 2 ->
    b1 <= f1 <= b1 + 24 -> b2 <= f2 <= b2 + 24 -> b3 <= f3 <= b3 + 24 -> b4 <= f4 <= b4 + 24 ->
    (forall mm' (v0 v4 v5 v7 : word) (V1 V2 V3 V4 g1 g2 g3 g4 : Z) (l9 l10 l11 l12 y11 y13 y26 y27 y29 : word),
       munch WM mm mm' -> wmono bsegs mm mm' ->
       z4L_mem mm' v0 v4 v5 v7 c1 c2 c3 c4 g1 g2 g3 g4 p1 p2 p3 p4 jp1 jp2 jp3 jp4 s1 s2 s3 s4 e1 e2 e3 e4 ->
       1 <= bv_unsigned l9 <= 2 -> 1 <= bv_unsigned l10 <= 2 -> 1 <= bv_unsigned l11 <= 2 -> 1 <= bv_unsigned l12 <= 2 ->
       O1 + 2 <= V1 <= O1 + 4 -> O2 + 2 <= V2 <= O2 + 4 -> O3 + 2 <= V3 <= O3 + 4 -> O4 + 2 <= V4 <= O4 + 4 ->
       b1 <= g1 <= b1 + 36 -> b2 <= g2 <= b2 + 36 -> b3 <= g3 <= b3 + 36 -> b4 <= g4 <= b4 + 36 ->
       evtF bsegs RNG Q (ZL 585916 mm' l10 (Zw (2^61)) (Zw (64 - tl)) (Zw (- DT - 5)) (Zw g1) (Zw V4) (Zw c1) y11
                           (Zw V1) y13 (Zw p1) (Zw p2) (Zw p3) (Zw c2) (Zw V3) (Zw V2) (Zw g2) (Zw AZ4_SB) l12 (Zw g3)
                           (Zw g4) l9 y26 y27 l11 y29 (Zw (DT + 4)) (Zw p4))) ->
    evtF bsegs RNG Q (ZL 585188 mm x1 (Zw (2^61)) (Zw (64 - tl)) (Zw (- DT - 5)) (Zw f1) (Zw U4) (Zw c1) x11
                        (Zw U1) x13 (Zw p1) (Zw p2) (Zw p3) (Zw c2) (Zw U3) (Zw U2) (Zw f2) (Zw AZ4_SB) l8 (Zw f3)
                        (Zw f4) l5 l6 l7 x28 x29 (Zw (DT + 4)) (Zw p4)).

  Definition z4L_md4_goal : Prop :=
    z4L_ctx ->
    forall mm (w0 w4 w5 w7 : word) (c1 c2 c3 c4 p1 p2 p3 p4 b1 b2 b3 b4 O1 O2 O3 O4 V1 V2 V3 V4 g1 g2 g3 g4 : Z)
           (jp1 jp2 jp3 jp4 : list byte) (s1 s2 s3 s4 e1 e2 e3 e4 : word)
           (l9 l10 l11 l12 x11 x13 x26 x27 x29 : word),
    z4L_mem mm w0 w4 w5 w7 c1 c2 c3 c4 g1 g2 g3 g4 p1 p2 p3 p4 jp1 jp2 jp3 jp4 s1 s2 s3 s4 e1 e2 e3 e4 ->
    z4L_bnd c1 c2 c3 c4 p1 p2 p3 p4 b1 b2 b3 b4 O1 O2 O3 O4 ->
    1 <= bv_unsigned l9 <= 2 -> 1 <= bv_unsigned l10 <= 2 -> 1 <= bv_unsigned l11 <= 2 -> 1 <= bv_unsigned l12 <= 2 ->
    O1 + 2 <= V1 <= O1 + 4 -> O2 + 2 <= V2 <= O2 + 4 -> O3 + 2 <= V3 <= O3 + 4 -> O4 + 2 <= V4 <= O4 + 4 ->
    b1 <= g1 <= b1 + 36 -> b2 <= g2 <= b2 + 36 -> b3 <= g3 <= b3 + 36 -> b4 <= g4 <= b4 + 36 ->
    (forall mm' (v0 v4 v7 : word) (R1 R2 R3 R4 h1 h2 h3 h4 : Z) (l13 l14 l15 l16 y13 y22 y23 y27 y28 y29 : word),
       munch WM mm mm' -> wmono bsegs mm mm' ->
       z4L_mem mm' v0 v4 l13 v7 c1 c2 c3 c4 h1 h2 h3 h4 p1 p2 p3 p4 jp1 jp2 jp3 jp4 s1 s2 s3 s4 e1 e2 e3 e4 ->
       1 <= bv_unsigned l13 <= 2 -> 1 <= bv_unsigned l14 <= 2 -> 1 <= bv_unsigned l15 <= 2 -> 1 <= bv_unsigned l16 <= 2 ->
       O1 + 3 <= R1 <= O1 + 6 -> O2 + 3 <= R2 <= O2 + 6 -> O3 + 3 <= R3 <= O3 + 6 -> O4 + 3 <= R4 <= O4 + 6 ->
       b1 <= h1 <= b1 + 48 -> b2 <= h2 <= b2 + 48 -> b3 <= h3 <= b3 + 48 -> b4 <= h4 <= b4 + 48 ->
       evtF bsegs RNG Q (ZL 586648 mm' (Zw h2) (Zw (2^61)) (Zw (64 - tl)) (Zw (- DT - 5)) l15 (Zw R4) (Zw c1) l16
                           (Zw R1) y13 (Zw p1) (Zw p2) (Zw p3) (Zw c2) (Zw R3) (Zw R2) (Zw h3) (Zw AZ4_SB) y22 y23
                           (Zw h4) l14 (Zw h1) y27 y28 y29 (Zw (DT + 4)) (Zw p4))) ->
    evtF bsegs RNG Q (ZL 585916 mm l10 (Zw (2^61)) (Zw (64 - tl)) (Zw (- DT - 5)) (Zw g1) (Zw V4) (Zw c1) x11
                        (Zw V1) x13 (Zw p1) (Zw p2) (Zw p3) (Zw c2) (Zw V3) (Zw V2) (Zw g2) (Zw AZ4_SB) l12 (Zw g3)
                        (Zw g4) l9 x26 x27 l11 x29 (Zw (DT + 4)) (Zw p4)).
End Z4L.

Definition z4R_pre (L o cq cr : Z) (r : bool) : Prop :=
  0 <= o /\ (o = 0 \/ (o + 8 <= L /\ 8 * cq + cr <= 56)) /\ 0 <= cr <= 7 /\ 0 <= cq /\ 8 * cq + cr <= 112 /\
  (if r then 8 <= o else o < 8).
Definition z4R_post (L o b : Z) : Prop := 1 <= o /\ o + 8 <= L /\ 0 <= b <= 7.

Section Z4R.
  Variable RNG : footprint.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Notation Zw z := (Z_to_bv 64 z) (only parsing).
  Notation Z4SF' := (Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs).
  Notation ZR pc mm r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29
             r30 r31 :=
    (MS (mkR r1 (Zw (SP + -384)) gp tp r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23
             r24 r25 r26 r27 r28 r29 r30 r31) FR (Zw pc) fc None mm (seg_rom bsegs)) (only parsing).
  Notation BDS k b jp O o := (BD4A k (Zw b) jp (Zw (SS + O + o)) (Zw (SS + O)) (Zw (SS + O + 8))) (only parsing).
  Notation SPL w0 w4 w5 w7 k2 k4 k3 :=
    (SPD w0 (Zw (DST + 3 * seg)) (Zw (tl + 256 * mtl)) (Zw (DST + dcap - 7)) w4 w5 (Zw (DST + dcap)) w7 k2
         (Zw (DST + seg)) (Zw (DST + 2 * seg)) k4 k3 (Zw (DT + 4)) (Zw dcap)) (only parsing).

  Definition z4R_epi : Prop :=
    forall mm' (spl bd4 bd3 bd2 bd1 : list cell) (r : Z)
           (z1 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 : word),
      Z4SF' mm' spl bd4 bd3 bd2 bd1 -> r = dcap \/ r = 2^64 - 20 ->
      evtF bsegs RNG Q (ZR AZ4_DEPI mm' z1 (Zw r) z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24
                          z25 z26 z27 z28 z29 z30 z31).

  Definition z4R_goal (r1 r2 r3 r4 : bool) : Prop :=
    z4s2_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q ->
    z4R_epi ->
    forall mm (l1 l2 l3 q1 q2 q3 q4 e1 e2 e3 e4 o1 o2 o3 o4 cq1 cr1 cq2 cr2 cq3 cr3 cq4 cr4 : Z)
           (k1 k2 k3 k4 : word) (jp1 jp2 jp3 jp4 : list byte)
           (w0 w4 w7 l13 l14 l15 l16 x13 x22 x23 x27 x28 x29 : word),
    Z4SF' mm (SPL w0 w4 l13 w7 k2 k4 k3)
      (BDS k4 (8 * cq4 + cr4) jp4 (6 + l1 + l2 + l3) o4) (BDS k3 (8 * cq3 + cr3) jp3 (6 + l1 + l2) o3)
      (BDS k2 (8 * cq2 + cr2) jp2 (6 + l1) o2) (BDS k1 (8 * cq1 + cr1) jp1 6 o1) ->
    1 <= l1 -> 1 <= l2 -> 1 <= l3 -> 6 + l1 + l2 + l3 + 1 <= n -> 6 <= dcap -> 3 * seg <= dcap ->
    z4R_pre l1 o1 cq1 cr1 r1 -> z4R_pre l2 o2 cq2 cr2 r2 -> z4R_pre l3 o3 cq3 cr3 r3 ->
    z4R_pre (n - (6 + l1 + l2 + l3)) o4 cq4 cr4 r4 ->
    1 <= bv_unsigned l13 <= 2 -> 1 <= bv_unsigned l14 <= 2 -> 1 <= bv_unsigned l15 <= 2 -> 1 <= bv_unsigned l16 <= 2 ->
    q1 + 3 <= e1 <= q1 + 6 -> q2 + 3 <= e2 <= q2 + 6 -> q3 + 3 <= e3 <= q3 + 6 -> q4 + 3 <= e4 <= q4 + 6 ->
    q1 + 8 <= dcap -> q2 + 8 <= dcap -> q3 + 8 <= dcap -> q4 + 8 <= dcap ->
    0 <= q1 -> seg <= q2 -> 2 * seg <= q3 -> 3 * seg <= q4 ->
    (forall mm' (q1' q2' q3' q4' o1' o2' o3' o4' b1' b2' b3' b4' : Z) (k1' k2' k3' k4' : word)
            (w0' w4' w5' w7' y8 y10 y11 y13 y17 y22 y25 y27 y28 y29 : word),
       Z4SF' mm' (SPL w0' w4' w5' w7' k2' k4' k3')
         (BDS k4' b4' jp4 (6 + l1 + l2 + l3) o4') (BDS k3' b3' jp3 (6 + l1 + l2) o3')
         (BDS k2' b2' jp2 (6 + l1) o2') (BDS k1' b1' jp1 6 o1') ->
       z4R_post l1 o1' b1' -> z4R_post l2 o2' b2' -> z4R_post l3 o3' b3' ->
       z4R_post (n - (6 + l1 + l2 + l3)) o4' b4' ->
       e1 + 1 <= q1' <= e1 + 2 -> e2 + 1 <= q2' <= e2 + 2 -> e3 + 1 <= q3' <= e3 + 2 -> e4 + 1 <= q4' <= e4 + 2 ->
       q4' + 8 <= dcap ->
       evtF bsegs RNG Q (ZR 583740 mm' (Zw b2') (Zw (2^61)) (Zw (64 - tl)) (Zw (- DT - 5)) y8 (Zw (DST + q4')) y10 y11
                           (Zw (DST + q1')) y13 (Zw (SS + 6 + o1')) (Zw (SS + 6 + l1 + o2')) (Zw (SS + 6 + l1 + l2 + o3'))
                           y17 (Zw (DST + q3')) (Zw (DST + q2')) (Zw b3') (Zw AZ4_SB) y22 k1' (Zw b4') y25 (Zw b1')
                           y27 y28 y29 (Zw (DT + 4)) (Zw (SS + 6 + l1 + l2 + l3 + o4')))) ->
    evtF bsegs RNG Q (ZR 586648 mm (Zw (8 * cq2 + cr2)) (Zw (2^61)) (Zw (64 - tl)) (Zw (- DT - 5)) l15 (Zw (DST + e4))
                        k1 l16 (Zw (DST + e1)) x13 (Zw (SS + 6 + o1)) (Zw (SS + 6 + l1 + o2)) (Zw (SS + 6 + l1 + l2 + o3))
                        k2 (Zw (DST + e3)) (Zw (DST + e2)) (Zw (8 * cq3 + cr3)) (Zw AZ4_SB) x22 x23 (Zw (8 * cq4 + cr4))
                        l14 (Zw (8 * cq1 + cr1)) x27 x28 x29 (Zw (DT + 4)) (Zw (SS + 6 + l1 + l2 + l3 + o4))).

  Definition z4H (L o b : Z) : Prop := 0 <= o /\ ((o + 8 <= L /\ 0 <= b <= 8) \/ (o = 0 /\ 0 <= b <= 64)).

  Definition z4I_goal : Prop :=
    z4s2_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q ->
    z4R_epi ->
    forall mm (l1 l2 l3 q1 q2 q3 q4 o1 o2 o3 o4 b1 b2 b3 b4 : Z) (k1 k2 k3 k4 : word) (jp1 jp2 jp3 jp4 : list byte)
           (w0 w4 w5 w7 x8 x10 x11 x13 x17 x22 x25 x27 x28 x29 : word),
    Z4SF' mm (SPL w0 w4 w5 w7 k2 k4 k3)
      (BDS k4 b4 jp4 (6 + l1 + l2 + l3) o4) (BDS k3 b3 jp3 (6 + l1 + l2) o3)
      (BDS k2 b2 jp2 (6 + l1) o2) (BDS k1 b1 jp1 6 o1) ->
    1 <= l1 -> 1 <= l2 -> 1 <= l3 -> 6 + l1 + l2 + l3 + 1 <= n -> 6 <= dcap -> 3 * seg <= dcap ->
    z4H l1 o1 b1 -> z4H l2 o2 b2 -> z4H l3 o3 b3 -> z4H (n - (6 + l1 + l2 + l3)) o4 b4 ->
    z1ops seg q1 q2 q3 q4 -> q4 + 8 <= dcap ->
    evtF bsegs RNG Q (ZR 583740 mm (Zw b2) (Zw (2^61)) (Zw (64 - tl)) (Zw (- DT - 5)) x8 (Zw (DST + q4)) x10 x11
                        (Zw (DST + q1)) x13 (Zw (SS + 6 + o1)) (Zw (SS + 6 + l1 + o2)) (Zw (SS + 6 + l1 + l2 + o3))
                        x17 (Zw (DST + q3)) (Zw (DST + q2)) (Zw b3) (Zw AZ4_SB) x22 k1 (Zw b4) x25 (Zw b1)
                        x27 x28 x29 (Zw (DT + 4)) (Zw (SS + 6 + l1 + l2 + l3 + o4))).
End Z4R.

Definition z4F_case : Prop :=
  forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (rng_fs : alayout -> footprint -> Prop)
         (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
         (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
         (SBL SBH : Z) (rstk : region),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  z4I_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q ->
  z4i1_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q.
End CANSEC1.
