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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkKit FseRdKit HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXTac KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_z4s_iface AF_huf_z4s3_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s2_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s3b.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).
Notation amem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.

Lemma z4c0_walk : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x10 x11 x13 x14 x15 x16 x20 x22 x23 x24 x25 x26 x27 x28 x29 x31 : word)
    (w0 w2 w3 w4 w5 w6 w7 w8 w9 w11 w12 w13 w14 : word)
    (SP DST dcap seg q1 q2 q3 q4 DT : Z),
  rw_cells bsegs mm (SP + -384) [C8 w0; C8 (Z_to_bv 64 (DST + 3 * seg)); C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8;
                                 C8 w9; C8 (Z_to_bv 64 (DST + 2 * seg)); C8 w11; C8 w12; C8 w13; C8 w14] ->
  mem_inv bsegs mm -> rng RNG (SP + -384) 384 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg -> 3 * seg <= dcap ->
  0 <= q1 <= dcap -> 0 <= q2 <= dcap -> 0 <= q3 <= dcap -> 0 <= q4 <= dcap ->
  4096 <= DT <= 2^47 -> 2^46 <= SP < 2^64 ->
  (q1 <= seg -> q2 <= 2 * seg -> q3 <= 3 * seg ->
   forall (y1 y5 y6 y7 y8 y10 y11 y13 y14 y15 y16 y20 y22 y23 y24 y25 y26 y27 y28 y29 y31 : word),
   evtF bsegs RNG Q
      (MS (mkR y1 (Z_to_bv 64 (SP + -384)) gp tp y5 y6 y7 y8 (Z_to_bv 64 (DST + q4)) y10 y11 (Z_to_bv 64 (DST + q1))
               y13 y14 y15 y16 (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (DST + q3)) (Z_to_bv 64 (DST + q2)) y20
               (Z_to_bv 64 AZ4_SB) y22 y23 y24 y25 y26 y27 y28 y29 (Z_to_bv 64 (DT + 4)) y31)
          F (Z_to_bv 64 AZ4_S1) fc None mm (seg_rom bsegs))) ->
  (forall (y1 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
      evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (SP + -384)) gp tp (Z_to_bv 64 (2^64 - 20)) y6 y7 y8 y9 y10 y11 y12 y13 y14
                                y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                           F (Z_to_bv 64 AZ4_DEPI) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (DST + q4)) x10 x11 (Z_to_bv 64 (DST + q1))
               x13 x14 x15 x16 (Z_to_bv 64 (DST + seg)) (Z_to_bv 64 (DST + q3)) (Z_to_bv 64 (DST + q2)) x20
               (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 AZ4_C0) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x10 x11 x13 x14 x15 x16 x20 x22 x23 x24 x25 x26 x27 x28 x29 x31
    w0 w2 w3 w4 w5 w6 w7 w8 w9 w11 w12 w13 w14 SP DST dcap seg q1 q2 q3 q4 DT
    FR MI RS HD HDE HC HS0 HS HQ1 HQ2 HQ3 HQ4 HDT HSP K1 K2.
  unfold AZ4_C0, AZ4_S1, AZ4_DEPI, AZ4_SB in *.
  destruct (Z_le_gt_dec q1 seg) as [A1|A1]; [destruct (Z_le_gt_dec q2 (2 * seg)) as [A2|A2];
    [destruct (Z_le_gt_dec q3 (3 * seg)) as [A3|A3]|]|].
  - kx_runFmd [0x8fc74; 0x8fbec] 40%nat [false; false; false]
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q1 0 (2^32); KZRange q2 0 (2^32);
       KZRange q3 0 (2^32); KZRange q4 0 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^64 - 1);
       KZWord (SP + -376) 8 (DST + 3 * seg); KZWord (SP + -304) 8 (DST + 2 * seg)]
      (@nil (Z * Z)) [(SP + -384, 384)] (@nil (Z * Z)).
    all: try z4br.
    kx_post_regs. cbn [mem_denot]. rewrite ?Z.add_assoc. apply K1; assumption.
  - kx_runFmd [0x8fc74; 0x8fbec] 40%nat [false; false; true]
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q1 0 (2^32); KZRange q2 0 (2^32);
       KZRange q3 0 (2^32); KZRange q4 0 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^64 - 1);
       KZWord (SP + -376) 8 (DST + 3 * seg); KZWord (SP + -304) 8 (DST + 2 * seg)]
      (@nil (Z * Z)) [(SP + -384, 384)] (@nil (Z * Z)).
    all: try z4br.
    kx_post_regs. cbn [mem_denot]. apply K2.
  - kx_runFmd [0x8fc74; 0x8fbec] 40%nat [false; true]
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q1 0 (2^32); KZRange q2 0 (2^32);
       KZRange q3 0 (2^32); KZRange q4 0 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^64 - 1);
       KZWord (SP + -376) 8 (DST + 3 * seg); KZWord (SP + -304) 8 (DST + 2 * seg)]
      (@nil (Z * Z)) [(SP + -384, 384)] (@nil (Z * Z)).
    all: try z4br.
    kx_post_regs. cbn [mem_denot]. apply K2.
  - kx_runFmd [0x8fc74; 0x8fbec] 40%nat [true]
      [KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q1 0 (2^32); KZRange q2 0 (2^32);
       KZRange q3 0 (2^32); KZRange q4 0 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^64 - 1);
       KZWord (SP + -376) 8 (DST + 3 * seg); KZWord (SP + -304) 8 (DST + 2 * seg)]
      (@nil (Z * Z)) [(SP + -384, 384)] (@nil (Z * Z)).
    all: try z4br.
    kx_post_regs. cbn [mem_denot]. apply K2.
Qed.

Theorem z4s2_proof : z4s31_stmtA -> z4s32_stmtA -> z4s33_stmtA -> z4s34_stmtA -> z4end_stmtA ->
  forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (rng_fs : alayout -> footprint -> Prop)
         (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
         (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
         (SBL SBH : Z) (rstk : region),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  z4s2_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q.
Proof.
  intros Y31 Y32 Y33 Y34 YE Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0
    DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk HC.
  unfold z4s2_goal.
  intros l1 l2 l3 q1 q2 q3 q4 pt1 pt2 pt3 pt4 b1 b2 b3 b4 c1 c2 c3 c4 jp1 jp2 jp3 jp4 w0 w4 w5 w7 w8 w11 w12 mm
    x1 x5 x6 x7 x8 x10 x11 x13 x14 x15 x16 x20 x22 x23 x24 x25 x26 x27 x28 x29 x31
    Z4 L1 L2 L3 LN D6 SG Q1 Q2 Q3 Q4 ST1 ST2 ST3 ST4 EX.
  pose proof (z4ctx_facts AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk HC ltac:(lia))
    as (FD1 & FD2 & FDC & FT1 & FT2 & FS & FSP1 & FSP2 & FRNG).
  pose proof (ATOP_lo) as ATL. unfold AIMG_HI in *.
  assert (NS : 0 < zlen src) by lia. specialize (FS NS).
  assert (SEG0 : 0 <= (dcap + 3) / 4) by (apply Z.div_pos; lia).
  pose proof Z4 as Z4'.
  destruct Z4' as (BUF & SRC & CBS & DTH & STK & SPL & SPLs & B4 & B4s & B3 & B3s & B2 & B2s & B1 & B1s & FRSc & MI & MU & WM).
  unfold SPD in SPL.
  destruct ST1 as (P1a & P1b & P1c). destruct ST2 as (P2a & P2b & P2c).
  destruct ST3 as (P3a & P3b & P3c). destruct ST4 as (P4a & P4b & P4c).
  eapply (z4c0_walk Q RNG mm FR fc gp tp x1 x5 x6 x7 x8 x10 x11 x13 x14 x15 x16 x20 x22 x23 x24 x25 x26 x27 x28 x29 x31
            w0 _ _ w4 w5 _ w7 w8 _ w11 w12 _ _ (bv_unsigned sp) DST dcap ((dcap + 3) / 4) q1 q2 q3 q4 DT);
    [exact SPL | exact MI | eapply rng_sub; [exact FRNG | lia | lia] | lia | lia | lia | lia | lia | lia | lia | lia | lia
    | lia | lia | | ].
  2: { intros. eapply (EX mm); [exact Z4 | right; reflexivity]. }
  intros A1 A2 A3 y1 y5 y6 y7 y8 y10 y11 y13 y14 y15 y16 y20 y22 y23 y24 y25 y26 y27 y28 y29 y31.
  pose proof (Y31 Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
                src cells cbs pdt SBL SBH rstk 6 l1 ((dcap + 3) / 4) HC ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as G1.
  unfold z4s31_goal in G1.
  eapply (G1 q1 pt1 b1 c1 jp1); [exact Z4 | lia | lia | lia | lia |].
  intros mm1 c1' b1' p1' s1' l1' jp1' v0 v4 v5 v7 v8 v9 v11
    z1 z5 z7 z8 z10 z11 z12 z13 z14 z15 z16 z17 z20 z22 z23 z24 z25 z27 z28 z29 z31 Z41.
  pose proof (Y32 Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
                src cells cbs pdt SBL SBH rstk (6 + l1) l2 (2 * ((dcap + 3) / 4)) HC ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia))
    as G2.
  unfold z4s32_goal in G2.
  rewrite <- (Z.add_assoc SS 6 l1) in Z41.
  eapply (G2 q2 pt2 b2 c2 jp2); [exact Z41 | lia | lia | lia | lia |].
  intros mm2 c2' b2' p2' s2' l2' jp2' u0 u4 u5 u7 u8 u9 u10 u11
    r1 r5 r7 r8 r10 r11 r12 r13 r14 r15 r16 r17 r19 r20 r22 r23 r24 r25 r27 r28 r29 r31 Z42.
  pose proof (Y33 Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
                src cells cbs pdt SBL SBH rstk (6 + l1 + l2) l3 (3 * ((dcap + 3) / 4)) HC ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia))
    as G3.
  unfold z4s33_goal in G3.
  rewrite <- (Z.add_assoc SS (6 + l1) l2) in Z42.
  eapply (G3 q3 pt3 b3 c3 jp3); [exact Z42 | lia | lia | lia | lia |].
  intros mm3 c3' b3' p3' s3' l3' jp3' t0 t1 t4 t5 t7 t8 t9 t10 t11
    e1 e5 e7 e8 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e22 e23 e24 e25 e27 e28 e29 e31 Z43.
  pose proof (Y34 Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
                src cells cbs pdt SBL SBH rstk (6 + l1 + l2 + l3) (zlen src - (6 + l1 + l2 + l3)) HC ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia))
    as G4.
  unfold z4s34_goal in G4.
  rewrite <- (Z.add_assoc SS (6 + l1 + l2) l3) in Z43.
  eapply (G4 q4 pt4 b4 c4 jp4); [exact Z43 | lia | lia | lia | lia |].
  intros mm4 c4' b4' p4' s4' l4' jp4' f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
    g1 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29 g30 g31 Z44.
  pose proof (YE Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo
                src cells cbs pdt SBL SBH rstk HC ltac:(lia)) as GE.
  unfold z4end_goal in GE.
  eapply GE; [exact Z44 |].
  intros mm5 spl5 r h1 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 Z45 HR.
  eapply (EX mm5); [exact Z45 | exact HR].
Qed.

End CANSEC1.
