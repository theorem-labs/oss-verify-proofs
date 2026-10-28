From Stdlib Require Import ZArith NArith List Lia Bool.
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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_z4s3_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s2_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_tbl_iface2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXCell KXCell2.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s1_iface AF_huf_z4s1mk.

Notation amem := (word -> option byte).
Notation Zw z := (Z_to_bv 64 z) (only parsing).

From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s3b.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s1rl_iface.

Section CANSEC1. Context {rc : runConstT}.

Definition z4R_case (r1 r2 r3 r4 : bool) : Prop :=
  forall (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word)
         (fc : bv 32) (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte)
         (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (st : astate) (LB : list ablock)
         (rng_fs : alayout -> footprint -> Prop) (cells : list deltX2) (pdt : aptr) (SBL SBH : Z) (rstk : region),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  z4R_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q r1 r2 r3 r4.

Definition z4R_c0000 : Prop := z4R_case false false false false.
Definition z4R_c0001 : Prop := z4R_case false false false true.
Definition z4R_c0010 : Prop := z4R_case false false true false.
Definition z4R_c0011 : Prop := z4R_case false false true true.
Definition z4R_c0100 : Prop := z4R_case false true false false.
Definition z4R_c0101 : Prop := z4R_case false true false true.
Definition z4R_c0110 : Prop := z4R_case false true true false.
Definition z4R_c0111 : Prop := z4R_case false true true true.
Definition z4R_c1000 : Prop := z4R_case true false false false.
Definition z4R_c1001 : Prop := z4R_case true false false true.
Definition z4R_c1010 : Prop := z4R_case true false true false.
Definition z4R_c1011 : Prop := z4R_case true false true true.
Definition z4R_c1100 : Prop := z4R_case true true false false.
Definition z4R_c1101 : Prop := z4R_case true true false true.
Definition z4R_c1110 : Prop := z4R_case true true true false.
Definition z4R_c1111 : Prop := z4R_case true true true true.

Section Z4R1.
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
  Notation CTX AI L st LB rng_fs cells pdt SBL SBH rstk :=
    (z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk) (only parsing).
  Notation LAY l1 l2 l3 := (1 <= l1 /\ 1 <= l2 /\ 1 <= l3 /\ 6 + l1 + l2 + l3 + 1 <= n /\ 6 <= dcap /\ 3 * seg <= dcap)
    (only parsing).

  Definition z4R_s1_goal (r1 : bool) : Prop :=
    forall (AI : AMallocIface) (L : alayout) (st : astate) (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
           (cells : list deltX2) (pdt : aptr) (SBL SBH : Z) (rstk : region)
           mm (l1 l2 l3 e1 e2 e3 e4 o1 cq1 cr1 o2 cq2 cr2 o3 cq3 cr3 o4 cq4 cr4 : Z) (k1 k2 k3 k4 : word)
           (jp1 jp2 jp3 jp4 : list byte) (w0 w4 w7 l13 l14 l15 l16 x13 x22 x23 x27 x28 x29 : word),
    CTX AI L st LB rng_fs cells pdt SBL SBH rstk -> LAY l1 l2 l3 -> z4R_pre l1 o1 cq1 cr1 r1 ->
    Z4SF' mm (SPL w0 w4 l13 w7 k2 k4 k3)
      (BDS k4 (8 * cq4 + cr4) jp4 (6 + l1 + l2 + l3) o4) (BDS k3 (8 * cq3 + cr3) jp3 (6 + l1 + l2) o3)
      (BDS k2 (8 * cq2 + cr2) jp2 (6 + l1) o2) (BDS k1 (8 * cq1 + cr1) jp1 6 o1) ->
    (forall mm' (o1' b1' : Z) (c1 : word) (v14 v22 v27 v28 v29 v31 : word),
       Z4SF' mm' (SPL w0 (Zw (z4R_fl r1)) l13 (Zw 3) k2 k4 k3)
         (BDS k4 (8 * cq4 + cr4) jp4 (6 + l1 + l2 + l3) o4) (BDS k3 (8 * cq3 + cr3) jp3 (6 + l1 + l2) o3)
         (BDS k2 (8 * cq2 + cr2) jp2 (6 + l1) o2) (BDS c1 b1' jp1 6 o1') ->
       z4R_res r1 o1 cq1 cr1 o1' b1' ->
       evtF bsegs RNG Q (ZR (if r1 then 586868 else 587592) mm' (Zw (8 * cq2 + cr2)) (Zw (2^61)) (Zw (64 - tl))
                           (Zw (- DT - 5)) l15 (Zw (DST + e4)) c1 l16 (Zw (DST + e1)) (Zw (SS + 6 + o1')) v14
                           (Zw (SS + 6 + l1 + o2)) (Zw (SS + 6 + l1 + l2 + o3)) k2 (Zw (DST + e3)) (Zw (DST + e2))
                           (Zw (8 * cq3 + cr3)) (Zw AZ4_SB) v22 (Zw (SS + 6 + l1 + l2 + l3 + o4)) (Zw (8 * cq4 + cr4))
                           l14 (Zw b1') v27 v28 v29 (Zw (DT + 4)) v31)) ->
    evtF bsegs RNG Q (ZR 586648 mm (Zw (8 * cq2 + cr2)) (Zw (2^61)) (Zw (64 - tl)) (Zw (- DT - 5)) l15 (Zw (DST + e4))
                        k1 l16 (Zw (DST + e1)) x13 (Zw (SS + 6 + o1)) (Zw (SS + 6 + l1 + o2)) (Zw (SS + 6 + l1 + l2 + o3))
                        k2 (Zw (DST + e3)) (Zw (DST + e2)) (Zw (8 * cq3 + cr3)) (Zw AZ4_SB) x22 x23 (Zw (8 * cq4 + cr4))
                        l14 (Zw (8 * cq1 + cr1)) x27 x28 x29 (Zw (DT + 4)) (Zw (SS + 6 + l1 + l2 + l3 + o4))).
End Z4R1.

Section Z4RT.
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
  Notation CTX AI L st LB rng_fs cells pdt SBL SBH rstk :=
    (z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk) (only parsing).
  Notation LAY l1 l2 l3 := (1 <= l1 /\ 1 <= l2 /\ 1 <= l3 /\ 6 + l1 + l2 + l3 + 1 <= n /\ 6 <= dcap /\ 3 * seg <= dcap)
    (only parsing).

  Definition z4R_tl_goal (r1 r2 r3 r4 : bool) : Prop :=
    forall (AI : AMallocIface) (L : alayout) (st : astate) (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
           (cells : list deltX2) (pdt : aptr) (SBL SBH : Z) (rstk : region)
           mm (l1 l2 l3 q1 q2 q3 q4 e1 e2 e3 e4 o1 cq1 cr1 o2 cq2 cr2 o3 cq3 cr3 o4 cq4 cr4 : Z)
           (o1' b1' o2' b2' o3' b3' o4' b4' : Z) (c1 c2 c3 c4 : word) (jp1 jp2 jp3 jp4 : list byte)
           (w0 l13 l14 l15 l16 u10 u17 u22 u27 u31 : word),
    z4s2_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q ->
    z4R_epi RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q ->
    CTX AI L st LB rng_fs cells pdt SBL SBH rstk -> LAY l1 l2 l3 ->
    z4R_pre l1 o1 cq1 cr1 r1 -> z4R_pre l2 o2 cq2 cr2 r2 -> z4R_pre l3 o3 cq3 cr3 r3 ->
    z4R_pre (n - (6 + l1 + l2 + l3)) o4 cq4 cr4 r4 ->
    z4R_res r1 o1 cq1 cr1 o1' b1' -> z4R_res r2 o2 cq2 cr2 o2' b2' -> z4R_res r3 o3 cq3 cr3 o3' b3' ->
    z4R_res r4 o4 cq4 cr4 o4' b4' ->
    1 <= bv_unsigned l13 <= 2 -> 1 <= bv_unsigned l14 <= 2 -> 1 <= bv_unsigned l15 <= 2 -> 1 <= bv_unsigned l16 <= 2 ->
    q1 + 3 <= e1 <= q1 + 6 -> q2 + 3 <= e2 <= q2 + 6 -> q3 + 3 <= e3 <= q3 + 6 -> q4 + 3 <= e4 <= q4 + 6 ->
    q1 + 8 <= dcap -> q2 + 8 <= dcap -> q3 + 8 <= dcap -> q4 + 8 <= dcap ->
    0 <= q1 -> seg <= q2 -> 2 * seg <= q3 -> 3 * seg <= q4 ->
    Z4SF' mm (SPL w0 (Zw (z4R_fl r1)) l13 (Zw (z4R_fl r2)) c2 c4 c3)
      (BDS c4 b4' jp4 (6 + l1 + l2 + l3) o4') (BDS c3 b3' jp3 (6 + l1 + l2) o3')
      (BDS c2 b2' jp2 (6 + l1) o2') (BDS c1 b1' jp1 6 o1') ->
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
    evtF bsegs RNG Q (ZR 587500 mm (Zw b2') (Zw (2^61)) (Zw (64 - tl)) (Zw (- DT - 5)) l15 (Zw (DST + e4)) u10 l16
                        (Zw (DST + e1)) (Zw (SS + 6 + o1')) (Zw (SS + 6 + l1 + o2')) (Zw (SS + 6 + l1 + l2 + o3'))
                        (Zw (SS + 6 + l1 + l2 + l3 + o4')) u17 (Zw (DST + e3)) (Zw (DST + e2)) (Zw b3')
                        (Zw AZ4_SB) u22 c1 (Zw b4') l14 (Zw b1') u27 (Zw (z4R_fl r4)) (Zw (z4R_fl r3))
                        (Zw (DT + 4)) u31).
End Z4RT.

Lemma z4R_s1_false : forall RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q,
  z4R_s1_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q false.
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q.
  intros AI L st LB rng_fs cells pdt SBL SBH rstk mm l1 l2 l3 e1 e2 e3 e4 o1 cq1 cr1 o2 cq2 cr2 o3 cq3 cr3 o4 cq4 cr4
    k1 k2 k3 k4 jp1 jp2 jp3 jp4 w0 w4 w7 l13 l14 l15 l16 x13 x22 x23 x27 x28 x29 CTX LY PRE SF K.
  destruct LY as (HL1 & HL2 & HL3 & HN & HD6 & HSG).
  unfold z4R_pre in PRE. cbn iota in PRE. destruct PRE as (O1a & O1e & C1r & C1q & C1b & O1r).
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ltac:(lia))
    as (FD1 & FD2 & FD3 & FT1 & FT2 & FSS & FP1 & FP2 & FRN).
  destruct (FSS ltac:(lia)) as (FS1 & FS2).
  pose proof CTX as CTX0.
  destruct CTX0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2
    & DJ3 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof (AI_layout AI _ _ _ _ _ AH) as ALY.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  unfold AIMG_HI in FD1, FT1, FS1.
  clear AH NFK ABL HDT TOK ECB LCB DSTF BYS SRCB DJ1 DJ2 DJ3 LOA LOS SP16 TPA HINV RCL RLO RHI RRL RRS
    WSK WIM WIS WFS FSS.
  pose proof SF as SF0.
  destruct SF0 as ((buf & BUF & BUFL) & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S
    & FRM & MI & MU & WM).
  assert (FRN' : rng RNG (bv_unsigned sp + -400) 400) by (replace (bv_unsigned sp + -400) with (bv_unsigned sp - 400) by lia; exact FRN).
  pose proof (munch_refl [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -144, bv_unsigned sp + -144 + 40);
                          (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof (SysStep.rw_cells_wr_at bsegs mm _ _ 120 SPL ltac:(rewrite SPLS; lia)) as WSP.
  unfold AZ4_SB in *.
  kx_runFLd [587592; 586868; AZ4_C0] 200%nat (repeat false 64)
    [KZRange (bv_unsigned sp) 8192 (2^47); KZRange SS 4096 (2^47); KZRange o1 0 7; KZRange l1 1 (2^26);
     KZWord (bv_unsigned sp + -112) 8 (SS + 6 + 8); KZWr (bv_unsigned sp + -384) 120]
    (@nil (Z * Z)) [(bv_unsigned sp + -400, 400)] (@nil (Z * Z)).
  all: try lia.
  all: try z4r_stok.
  kx_post_regs_keep.
  unfold SPD in SPL. kx_cells_split SPL. kx_cells_post.
  kx_munch MUW. kx_post_mem_free.
  kx_frame B4. kx_frame B3. kx_frame B2. kx_frame B1.
  lazymatch goal with HL : log_flat ?E ?l |- context [mem_denot ?E ?m ?l] =>
    destruct (kx_u8arr_ex bsegs E m l DST buf BUF HL) as (buf' & BUF' & BUFL') end.
  z4post_ez.
  cbn [mem_denot] in *.
  replace (SS + o1 + 6) with (SS + 6 + o1) by lia.
  replace (SS + (l1 + (l2 + (l3 + o4))) + 6) with (SS + 6 + l1 + l2 + l3 + o4) by lia.
  eapply (K _ o1 (8 * cq1 + cr1) k1); [| cbn [z4R_res]; split; reflexivity].
  cbn [z4R_fl].
  eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
            cells cbs pdt SBL SBH rstk mm _ (-144)); [exact CTX | lia | lia | lia | exact SF | exact MUW | idtac .. ].
  all: try reflexivity.
  all: try assumption.
  all: try (exists buf'; split; [exact BUF' | lia]).
  all: try (unfold SPD; kx_cells_merge).
Qed.

Lemma z4R_s1_true : forall RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q,
  z4R_s1_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q true.
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q.
  intros AI L st LB rng_fs cells pdt SBL SBH rstk mm l1 l2 l3 e1 e2 e3 e4 o1 cq1 cr1 o2 cq2 cr2 o3 cq3 cr3 o4 cq4 cr4
    k1 k2 k3 k4 jp1 jp2 jp3 jp4 w0 w4 w7 l13 l14 l15 l16 x13 x22 x23 x27 x28 x29 CTX LY PRE SF K.
  destruct LY as (HL1 & HL2 & HL3 & HN & HD6 & HSG).
  unfold z4R_pre in PRE. cbn iota in PRE. destruct PRE as (O1a & [O1b|(O1c & O1d)] & C1r & C1q & C1b & O1r); [lia|].
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ltac:(lia))
    as (FD1 & FD2 & FD3 & FT1 & FT2 & FSS & FP1 & FP2 & FRN).
  destruct (FSS ltac:(lia)) as (FS1 & FS2).
  pose proof CTX as CTX0.
  destruct CTX0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2
    & DJ3 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof (AI_layout AI _ _ _ _ _ AH) as ALY.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  unfold AIMG_HI in FD1, FT1, FS1.
  clear AH NFK ABL HDT TOK ECB LCB DSTF BYS SRCB DJ1 DJ2 DJ3 LOA LOS SP16 TPA HINV RCL RLO RHI RRL RRS
    WSK WIM WIS WFS FSS.
  pose proof SF as SF0.
  destruct SF0 as ((buf & BUF & BUFL) & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S
    & FRM & MI & MU & WM).
  assert (FRN' : rng RNG (bv_unsigned sp + -400) 400) by (replace (bv_unsigned sp + -400) with (bv_unsigned sp - 400) by lia; exact FRN).
  pose proof (munch_refl [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -144, bv_unsigned sp + -144 + 40);
                          (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  destruct (z4R_srcwin AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk mm CTX MU
    ltac:(lia) ltac:(lia)) as (USS & SBA & SBL1 & SBL2 & SBR & SSR).
  pose proof (z4R_srctop AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk CTX
    ltac:(lia)) as SBT.
  pose proof (z4_bytes_sub mm SS src (6 + o1 - 8) 16 BSS ltac:(lia) ltac:(lia) ltac:(lia)) as BSL.
  replace (SS + (6 + o1 - 8)) with (SS + 6 + o1 - 8) in BSL by lia.
  pose proof (unpoisoned_sub mm SS (SS + zlen src) (SS + 6 + o1 - 8) (SS + 6 + o1 - 8 + 16) USS ltac:(lia) ltac:(lia)) as USL.
  assert (RSL : rng RNG (SS + 6 + o1 - 8) 16) by (eapply rng_sub; [exact SSR | lia | lia]).
  pose proof (SysStep.rw_cells_wr_at bsegs mm _ _ 120 SPL ltac:(rewrite SPLS; lia)) as WSP.
  pose proof (SysStep.rw_cells_wr_at bsegs mm _ _ 40 B1 ltac:(rewrite B1S; lia)) as WB1.
  assert (AS3 : KXGoM.apart (bv_unsigned sp + -400) 400 ASHOFF (ATOP / 8 + 1))
    by (unfold KXGoM.apart, ASHOFF; right; Z.div_mod_to_equations; lia).
  assert (TF : KXGoM.apart (SS + 6 + o1 - 8) 16 (bv_unsigned sp + -400) 400) by (unfold KXGoM.apart; left; lia).
  remember (8 * cq1 + cr1) as b1 eqn:EB1.
  pose proof (bv_unsigned_in_range _ k2) as K2R. unfold bv_modulus in K2R.
  rewrite <- (Z_to_bv_bv_unsigned k2) in SPL.
  unfold AZ4_SB in *.
  kx_runFLd [587592; 586868; AZ4_C0] 300%nat (true :: repeat false 63)
    [KZRange (bv_unsigned sp) 8192 (2^47); KZRange SS 4096 (2^47); KZRange o1 8 (2^26); KZRange l1 1 (2^26);
     KZRange b1 0 63; KZRange (l1 - o1) 8 (2^26);
     KZRange (SS + 6 + o1) 4096 (2^47);
     KZWord (bv_unsigned sp + -112) 8 (SS + 6 + 8); KZWord (bv_unsigned sp + -280) 8 (DT + 4);
     KZWord (bv_unsigned sp + -320) 8 (bv_unsigned k2);
     KZWr (bv_unsigned sp + -384) 120; KZWr (bv_unsigned sp + -144) 40]
    [(SS + 6 + o1 - 8, 16)] [(bv_unsigned sp + -400, 400)] [(SS + 6 + o1 - 8, 16)].
  all: try (lazymatch goal with |- _ <= _ < _ => lia | |- _ <= _ <= _ => lia end).
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => z4r_brx end).
  all: try (lazymatch goal with |- accP _ _ _ => clear - AS3 TF RSL SBT SBL1 SBL2 HN HL1 HL2 HL3 O1a O1c O1d C1r C1q C1b EB1 FP1 FP2 ATR FS1 FS2 NSM ALY SPT K2R; z4r_acc RSL end).
  all: try (lazymatch goal with |- flat _ _ _ /\ _ => clear - AS3 TF RSL SBT SBL1 SBL2 HN HL1 HL2 HL3 O1a O1c O1d C1r C1q C1b EB1 FP1 FP2 ATR FS1 FS2 NSM ALY SPT K2R; z4r_flat tl AS3 AS3 TF TF end).
  all: try z4r_stok.
  kx_post_regs_keep.
  unfold SPD in SPL. kx_cells_split SPL. unfold BD4A in B1. kx_cells_split B1. kx_cells_post.
  kx_munch MUW. kx_post_mem_free.
  kx_frame B4. kx_frame B3. kx_frame B2.
  lazymatch goal with HL : log_flat ?E ?l |- context [mem_denot ?E ?m ?l] =>
    destruct (kx_u8arr_ex bsegs E m l DST buf BUF HL) as (buf' & BUF' & BUFL') end.
  z4post_ez.
  cbn [mem_denot] in *.
  assert (HAND : edenot KXE (EAlu ALU_AND (EVar 31) (ELit 7)) = Z_to_bv 64 cr1).
  { apply bv_eq. cbn [edenot]. rewrite u_and64.
    assert (EV : ev KXE 31 = Z_to_bv 64 b1) by reflexivity. rewrite EV, !Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus. rewrite !(Z.mod_small _ (2 ^ Z.of_N 64)) by (change (2 ^ Z.of_N 64) with (2^64); lia).
    change 7 with (Z.ones 3). rewrite Z.land_ones by lia. subst b1. Z.div_mod_to_equations; lia. }
  rewrite (z4_srlw3 KXE (EVar 31) b1) in * by (first [reflexivity | lia]).
  rewrite HAND in *.
  assert (S8 : bv_unsigned (Z_to_bv 64 (b1 / 8)) = cq1).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
    subst b1. rewrite Z.mod_small; Z.div_mod_to_equations; lia. }
  rewrite S8 in *.
  try replace (SS + (o1 + - cq1) + 6) with (SS + 6 + (o1 - cq1)) in * by lia.
  try replace (SS + (o1 + -1 * cq1) + 6) with (SS + 6 + (o1 - cq1)) in * by lia.
  try replace (SS + (l1 + (l2 + (l3 + o4))) + 6) with (SS + 6 + l1 + l2 + l3 + o4) by lia.
  eapply (K _ (o1 - cq1) cr1); [| cbn [z4R_res]; split; reflexivity].
  cbn [z4R_fl].
  eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
            cells cbs pdt SBL SBH rstk mm _ (-144)); [exact CTX | lia | lia | lia | exact SF | exact MUW | idtac .. ].
  all: try reflexivity.
  all: try assumption.
  all: try (exists buf'; split; [exact BUF' | lia]).
  all: try (unfold SPD; kx_cells_merge).
  all: try (unfold BD4A; kx_cells_merge).
Qed.

Lemma z4R_s1 : forall RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q r1,
  z4R_s1_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q r1.
Proof. intros; destruct r1; [apply z4R_s1_true | apply z4R_s1_false]. Qed.

Lemma z4R_tl_1111 : forall RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q,
  z4R_tl_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    true true true true.
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q.
  intros AI L st LB rng_fs cells pdt SBL SBH rstk mm l1 l2 l3 q1 q2 q3 q4 e1 e2 e3 e4 o1 cq1 cr1 o2 cq2 cr2 o3 cq3 cr3
    o4 cq4 cr4 o1' b1' o2' b2' o3' b3' o4' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4 w0 l13 l14 l15 l16 u10 u17 u22 u27 u31
    K0 KE CTX LY P1 P2 P3 P4 R1 R2 R3 R4 L13 L14 L15 L16 E1 E2 E3 E4 QD1 QD2 QD3 QD4 Q1 Q2 Q3 Q4 SF K.
  destruct LY as (HL1 & HL2 & HL3 & HN & HD6 & HSG).
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ltac:(lia))
    as (FD1 & FD2 & FD3 & FT1 & FT2 & FSS & FP1 & FP2 & FRN).
  pose proof CTX as CTX0.
  destruct CTX0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2
    & DJ3 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof (AI_layout AI _ _ _ _ _ AH) as ALY.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  unfold AIMG_HI in FD1, FT1.
  clear AH NFK ABL HDT TOK ECB LCB DSTF BYS SRCB DJ1 DJ2 DJ3 LOA LOS SP16 TPA HINV RCL RLO RHI RRL RRS
    WSK WIM WIS WFS FSS.
  pose proof SF as SF0.
  destruct SF0 as ((buf & BUF & BUFL) & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S
    & FRM & MI & MU & WM).
  pose proof (bv_unsigned_in_range _ l13) as L13R. pose proof (bv_unsigned_in_range _ l14) as L14R.
  pose proof (bv_unsigned_in_range _ l15) as L15R. pose proof (bv_unsigned_in_range _ l16) as L16R.
  rewrite <- (Z_to_bv_bv_unsigned l13) in SPL.
  unfold AZ4_SB in *. cbn [z4R_fl] in *.
  destruct (Z_lt_ge_dec (e4 + bv_unsigned l16) (dcap - 7)) as [LT|GE].
  - kx_runFLd [583740; 587592; AZ4_C0] 100%nat [true]
      [KZRange (bv_unsigned sp) 8192 (2^47); KZRange DST 4096 (2^47); KZRange dcap 6 (2^32);
       KZRange e1 0 (2^32); KZRange e2 0 (2^32); KZRange e3 0 (2^32); KZRange e4 0 (2^32);
       KZRange (bv_unsigned l13) 1 2; KZRange (bv_unsigned l14) 1 2; KZRange (bv_unsigned l15) 1 2;
       KZRange (bv_unsigned l16) 1 2;
       KZWord (bv_unsigned sp + -344) 8 (bv_unsigned l13); KZWord (bv_unsigned sp + -352) 8 0;
       KZWord (bv_unsigned sp + -328) 8 0; KZWord (bv_unsigned sp + -360) 8 (DST + dcap - 7);
       KZWord (bv_unsigned sp + -312) 8 (DST + (dcap + 3) / 4)]
      (@nil (Z * Z)) [(bv_unsigned sp + -400, 400)] (@nil (Z * Z)).
    all: try (lazymatch goal with |- branch_taken _ _ _ = _ => z4br end).
    kx_post_regs_keep.
    z4post_ez.
    cbn [mem_denot] in *.
    try replace (bv_unsigned l15 + (DST + e3)) with (DST + (e3 + bv_unsigned l15)) by lia.
    try replace (SS + o1' + 6) with (SS + 6 + o1') by lia.
    try replace (SS + (l1 + o2') + 6) with (SS + 6 + l1 + o2') by lia.
    try replace (SS + (l1 + (l2 + o3')) + 6) with (SS + 6 + l1 + l2 + o3') by lia.
    try replace (SS + (l1 + (l2 + (l3 + o4'))) + 6) with (SS + 6 + l1 + l2 + l3 + o4') by lia.
    eapply (K mm (e1 + bv_unsigned l13) (e2 + bv_unsigned l14) (e3 + bv_unsigned l15) (e4 + bv_unsigned l16)
              o1' o2' o3' o4' b1' b2' b3' b4' c1 c2 c3 c4); [exact SF | ..].
    all: unfold z4R_post, z4R_pre, z4R_res in *; cbn iota in *; lia.
  - kx_runFLd [583740; 587592; AZ4_C0] 100%nat [false]
      [KZRange (bv_unsigned sp) 8192 (2^47); KZRange DST 4096 (2^47); KZRange dcap 6 (2^32);
       KZRange e1 0 (2^32); KZRange e2 0 (2^32); KZRange e3 0 (2^32); KZRange e4 0 (2^32);
       KZRange (bv_unsigned l13) 1 2; KZRange (bv_unsigned l14) 1 2; KZRange (bv_unsigned l15) 1 2;
       KZRange (bv_unsigned l16) 1 2;
       KZWord (bv_unsigned sp + -344) 8 (bv_unsigned l13); KZWord (bv_unsigned sp + -352) 8 0;
       KZWord (bv_unsigned sp + -328) 8 0; KZWord (bv_unsigned sp + -360) 8 (DST + dcap - 7);
       KZWord (bv_unsigned sp + -312) 8 (DST + (dcap + 3) / 4)]
      (@nil (Z * Z)) [(bv_unsigned sp + -400, 400)] (@nil (Z * Z)).
    all: try (lazymatch goal with |- branch_taken _ _ _ = _ => z4br end).
    kx_post_regs_keep.
    z4post_ez.
    cbn [mem_denot] in *.
    try replace (bv_unsigned l15 + (DST + e3)) with (DST + (e3 + bv_unsigned l15)) by lia.
    try replace (SS + o1' + 6) with (SS + 6 + o1') by lia.
    try replace (SS + (l1 + o2') + 6) with (SS + 6 + l1 + o2') by lia.
    try replace (SS + (l1 + (l2 + o3')) + 6) with (SS + 6 + l1 + l2 + o3') by lia.
    try replace (SS + (l1 + (l2 + (l3 + o4'))) + 6) with (SS + 6 + l1 + l2 + l3 + o4') by lia.
    replace (SS + (6 + l1 + l2 + l3)) with (SS + 6 + l1 + l2 + l3) in SF by lia.
    replace (SS + (6 + l1 + l2)) with (SS + 6 + l1 + l2) in SF by lia.
    replace (SS + (6 + l1)) with (SS + 6 + l1) in SF by lia.
    eapply (K0 l1 l2 l3 (e1 + bv_unsigned l13) (e2 + bv_unsigned l14) (e3 + bv_unsigned l15) (e4 + bv_unsigned l16)
              o1' o2' o3' o4' b1' b2' b3' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4); [exact SF | .. | exact KE].
    all: unfold z4strm, z4R_pre, z4R_res in *; cbn iota in *; lia.
Qed.

Lemma z4R_tl_0000 : forall RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q,
  z4R_tl_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    false false false false.
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q.
  intros AI L st LB rng_fs cells pdt SBL SBH rstk mm l1 l2 l3 q1 q2 q3 q4 e1 e2 e3 e4 o1 cq1 cr1 o2 cq2 cr2 o3 cq3 cr3
    o4 cq4 cr4 o1' b1' o2' b2' o3' b3' o4' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4 w0 l13 l14 l15 l16 u10 u17 u22 u27 u31
    K0 KE CTX LY P1 P2 P3 P4 R1 R2 R3 R4 L13 L14 L15 L16 E1 E2 E3 E4 QD1 QD2 QD3 QD4 Q1 Q2 Q3 Q4 SF K.
  destruct LY as (HL1 & HL2 & HL3 & HN & HD6 & HSG).
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ltac:(lia))
    as (FD1 & FD2 & FD3 & FT1 & FT2 & FSS & FP1 & FP2 & FRN).
  pose proof CTX as CTX0.
  destruct CTX0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2
    & DJ3 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof (AI_layout AI _ _ _ _ _ AH) as ALY.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  unfold AIMG_HI in FD1, FT1.
  clear AH NFK ABL HDT TOK ECB LCB DSTF BYS SRCB DJ1 DJ2 DJ3 LOA LOS SP16 TPA HINV RCL RLO RHI RRL RRS
    WSK WIM WIS WFS FSS.
  pose proof SF as SF0.
  destruct SF0 as ((buf & BUF & BUFL) & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S
    & FRM & MI & MU & WM).
  pose proof (bv_unsigned_in_range _ l13) as L13R. pose proof (bv_unsigned_in_range _ l14) as L14R.
  pose proof (bv_unsigned_in_range _ l15) as L15R. pose proof (bv_unsigned_in_range _ l16) as L16R.
  rewrite <- (Z_to_bv_bv_unsigned l13) in SPL.
  unfold AZ4_SB in *. cbn [z4R_fl] in *.
  kx_runFLd [583740; 587592; AZ4_C0] 100%nat (@nil bool)
    [KZRange (bv_unsigned sp) 8192 (2^47); KZRange DST 4096 (2^47); KZRange dcap 6 (2^32);
     KZRange e1 0 (2^32); KZRange e2 0 (2^32); KZRange e3 0 (2^32); KZRange e4 0 (2^32);
     KZRange (bv_unsigned l13) 1 2; KZRange (bv_unsigned l14) 1 2; KZRange (bv_unsigned l15) 1 2;
     KZRange (bv_unsigned l16) 1 2;
     KZWord (bv_unsigned sp + -344) 8 (bv_unsigned l13); KZWord (bv_unsigned sp + -352) 8 3;
     KZWord (bv_unsigned sp + -328) 8 3;
     KZWord (bv_unsigned sp + -312) 8 (DST + (dcap + 3) / 4)]
    (@nil (Z * Z)) [(bv_unsigned sp + -400, 400)] (@nil (Z * Z)).
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => z4br end).
  kx_post_regs_keep.
  z4post_ez.
  cbn [mem_denot] in *.
  try replace (bv_unsigned l15 + (DST + e3)) with (DST + (e3 + bv_unsigned l15)) by lia.
  try replace (SS + o1' + 6) with (SS + 6 + o1') by lia.
  try replace (SS + (l1 + o2') + 6) with (SS + 6 + l1 + o2') by lia.
  try replace (SS + (l1 + (l2 + o3')) + 6) with (SS + 6 + l1 + l2 + o3') by lia.
  try replace (SS + (l1 + (l2 + (l3 + o4'))) + 6) with (SS + 6 + l1 + l2 + l3 + o4') by lia.
  replace (SS + (6 + l1 + l2 + l3)) with (SS + 6 + l1 + l2 + l3) in SF by lia.
  replace (SS + (6 + l1 + l2)) with (SS + 6 + l1 + l2) in SF by lia.
  replace (SS + (6 + l1)) with (SS + 6 + l1) in SF by lia.
  eapply (K0 l1 l2 l3 (e1 + bv_unsigned l13) (e2 + bv_unsigned l14) (e3 + bv_unsigned l15) (e4 + bv_unsigned l16)
            o1' o2' o3' o4' b1' b2' b3' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4); [exact SF | .. | exact KE].
  all: unfold z4strm, z4R_pre, z4R_res in *; cbn iota in *; lia.
Qed.

Lemma z4R_tl_0001 : forall RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q,
  z4R_tl_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    false false false true.
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q.
  intros AI L st LB rng_fs cells pdt SBL SBH rstk mm l1 l2 l3 q1 q2 q3 q4 e1 e2 e3 e4 o1 cq1 cr1 o2 cq2 cr2 o3 cq3 cr3
    o4 cq4 cr4 o1' b1' o2' b2' o3' b3' o4' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4 w0 l13 l14 l15 l16 u10 u17 u22 u27 u31
    K0 KE CTX LY P1 P2 P3 P4 R1 R2 R3 R4 L13 L14 L15 L16 E1 E2 E3 E4 QD1 QD2 QD3 QD4 Q1 Q2 Q3 Q4 SF K.
  destruct LY as (HL1 & HL2 & HL3 & HN & HD6 & HSG).
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ltac:(lia))
    as (FD1 & FD2 & FD3 & FT1 & FT2 & FSS & FP1 & FP2 & FRN).
  pose proof CTX as CTX0.
  destruct CTX0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2
    & DJ3 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof (AI_layout AI _ _ _ _ _ AH) as ALY.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  unfold AIMG_HI in FD1, FT1.
  clear AH NFK ABL HDT TOK ECB LCB DSTF BYS SRCB DJ1 DJ2 DJ3 LOA LOS SP16 TPA HINV RCL RLO RHI RRL RRS
    WSK WIM WIS WFS FSS.
  pose proof SF as SF0.
  destruct SF0 as ((buf & BUF & BUFL) & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S
    & FRM & MI & MU & WM).
  pose proof (bv_unsigned_in_range _ l13) as L13R. pose proof (bv_unsigned_in_range _ l14) as L14R.
  pose proof (bv_unsigned_in_range _ l15) as L15R. pose proof (bv_unsigned_in_range _ l16) as L16R.
  rewrite <- (Z_to_bv_bv_unsigned l13) in SPL.
  unfold AZ4_SB in *. cbn [z4R_fl] in *.
  kx_runFLd [583740; 587592; AZ4_C0] 100%nat (@nil bool)
    [KZRange (bv_unsigned sp) 8192 (2^47); KZRange DST 4096 (2^47); KZRange dcap 6 (2^32);
     KZRange e1 0 (2^32); KZRange e2 0 (2^32); KZRange e3 0 (2^32); KZRange e4 0 (2^32);
     KZRange (bv_unsigned l13) 1 2; KZRange (bv_unsigned l14) 1 2; KZRange (bv_unsigned l15) 1 2;
     KZRange (bv_unsigned l16) 1 2;
     KZWord (bv_unsigned sp + -344) 8 (bv_unsigned l13); KZWord (bv_unsigned sp + -352) 8 3;
     KZWord (bv_unsigned sp + -328) 8 3;
     KZWord (bv_unsigned sp + -312) 8 (DST + (dcap + 3) / 4)]
    (@nil (Z * Z)) [(bv_unsigned sp + -400, 400)] (@nil (Z * Z)).
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => z4br end).
  kx_post_regs_keep.
  z4post_ez.
  cbn [mem_denot] in *.
  try replace (bv_unsigned l15 + (DST + e3)) with (DST + (e3 + bv_unsigned l15)) by lia.
  try replace (SS + o1' + 6) with (SS + 6 + o1') by lia.
  try replace (SS + (l1 + o2') + 6) with (SS + 6 + l1 + o2') by lia.
  try replace (SS + (l1 + (l2 + o3')) + 6) with (SS + 6 + l1 + l2 + o3') by lia.
  try replace (SS + (l1 + (l2 + (l3 + o4'))) + 6) with (SS + 6 + l1 + l2 + l3 + o4') by lia.
  replace (SS + (6 + l1 + l2 + l3)) with (SS + 6 + l1 + l2 + l3) in SF by lia.
  replace (SS + (6 + l1 + l2)) with (SS + 6 + l1 + l2) in SF by lia.
  replace (SS + (6 + l1)) with (SS + 6 + l1) in SF by lia.
  eapply (K0 l1 l2 l3 (e1 + bv_unsigned l13) (e2 + bv_unsigned l14) (e3 + bv_unsigned l15) (e4 + bv_unsigned l16)
            o1' o2' o3' o4' b1' b2' b3' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4); [exact SF | .. | exact KE].
  all: unfold z4strm, z4R_pre, z4R_res in *; cbn iota in *; lia.
Qed.

Lemma z4R_tl_0010 : forall RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q,
  z4R_tl_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    false false true false.
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q.
  intros AI L st LB rng_fs cells pdt SBL SBH rstk mm l1 l2 l3 q1 q2 q3 q4 e1 e2 e3 e4 o1 cq1 cr1 o2 cq2 cr2 o3 cq3 cr3
    o4 cq4 cr4 o1' b1' o2' b2' o3' b3' o4' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4 w0 l13 l14 l15 l16 u10 u17 u22 u27 u31
    K0 KE CTX LY P1 P2 P3 P4 R1 R2 R3 R4 L13 L14 L15 L16 E1 E2 E3 E4 QD1 QD2 QD3 QD4 Q1 Q2 Q3 Q4 SF K.
  destruct LY as (HL1 & HL2 & HL3 & HN & HD6 & HSG).
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ltac:(lia))
    as (FD1 & FD2 & FD3 & FT1 & FT2 & FSS & FP1 & FP2 & FRN).
  pose proof CTX as CTX0.
  destruct CTX0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2
    & DJ3 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof (AI_layout AI _ _ _ _ _ AH) as ALY.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  unfold AIMG_HI in FD1, FT1.
  clear AH NFK ABL HDT TOK ECB LCB DSTF BYS SRCB DJ1 DJ2 DJ3 LOA LOS SP16 TPA HINV RCL RLO RHI RRL RRS
    WSK WIM WIS WFS FSS.
  pose proof SF as SF0.
  destruct SF0 as ((buf & BUF & BUFL) & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S
    & FRM & MI & MU & WM).
  pose proof (bv_unsigned_in_range _ l13) as L13R. pose proof (bv_unsigned_in_range _ l14) as L14R.
  pose proof (bv_unsigned_in_range _ l15) as L15R. pose proof (bv_unsigned_in_range _ l16) as L16R.
  rewrite <- (Z_to_bv_bv_unsigned l13) in SPL.
  unfold AZ4_SB in *. cbn [z4R_fl] in *.
  kx_runFLd [583740; 587592; AZ4_C0] 100%nat (@nil bool)
    [KZRange (bv_unsigned sp) 8192 (2^47); KZRange DST 4096 (2^47); KZRange dcap 6 (2^32);
     KZRange e1 0 (2^32); KZRange e2 0 (2^32); KZRange e3 0 (2^32); KZRange e4 0 (2^32);
     KZRange (bv_unsigned l13) 1 2; KZRange (bv_unsigned l14) 1 2; KZRange (bv_unsigned l15) 1 2;
     KZRange (bv_unsigned l16) 1 2;
     KZWord (bv_unsigned sp + -344) 8 (bv_unsigned l13); KZWord (bv_unsigned sp + -352) 8 3;
     KZWord (bv_unsigned sp + -328) 8 3;
     KZWord (bv_unsigned sp + -312) 8 (DST + (dcap + 3) / 4)]
    (@nil (Z * Z)) [(bv_unsigned sp + -400, 400)] (@nil (Z * Z)).
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => z4br end).
  kx_post_regs_keep.
  z4post_ez.
  cbn [mem_denot] in *.
  try replace (bv_unsigned l15 + (DST + e3)) with (DST + (e3 + bv_unsigned l15)) by lia.
  try replace (SS + o1' + 6) with (SS + 6 + o1') by lia.
  try replace (SS + (l1 + o2') + 6) with (SS + 6 + l1 + o2') by lia.
  try replace (SS + (l1 + (l2 + o3')) + 6) with (SS + 6 + l1 + l2 + o3') by lia.
  try replace (SS + (l1 + (l2 + (l3 + o4'))) + 6) with (SS + 6 + l1 + l2 + l3 + o4') by lia.
  replace (SS + (6 + l1 + l2 + l3)) with (SS + 6 + l1 + l2 + l3) in SF by lia.
  replace (SS + (6 + l1 + l2)) with (SS + 6 + l1 + l2) in SF by lia.
  replace (SS + (6 + l1)) with (SS + 6 + l1) in SF by lia.
  eapply (K0 l1 l2 l3 (e1 + bv_unsigned l13) (e2 + bv_unsigned l14) (e3 + bv_unsigned l15) (e4 + bv_unsigned l16)
            o1' o2' o3' o4' b1' b2' b3' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4); [exact SF | .. | exact KE].
  all: unfold z4strm, z4R_pre, z4R_res in *; cbn iota in *; lia.
Qed.

Lemma z4R_tl_0011 : forall RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q,
  z4R_tl_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    false false true true.
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q.
  intros AI L st LB rng_fs cells pdt SBL SBH rstk mm l1 l2 l3 q1 q2 q3 q4 e1 e2 e3 e4 o1 cq1 cr1 o2 cq2 cr2 o3 cq3 cr3
    o4 cq4 cr4 o1' b1' o2' b2' o3' b3' o4' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4 w0 l13 l14 l15 l16 u10 u17 u22 u27 u31
    K0 KE CTX LY P1 P2 P3 P4 R1 R2 R3 R4 L13 L14 L15 L16 E1 E2 E3 E4 QD1 QD2 QD3 QD4 Q1 Q2 Q3 Q4 SF K.
  destruct LY as (HL1 & HL2 & HL3 & HN & HD6 & HSG).
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ltac:(lia))
    as (FD1 & FD2 & FD3 & FT1 & FT2 & FSS & FP1 & FP2 & FRN).
  pose proof CTX as CTX0.
  destruct CTX0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2
    & DJ3 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof (AI_layout AI _ _ _ _ _ AH) as ALY.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  unfold AIMG_HI in FD1, FT1.
  clear AH NFK ABL HDT TOK ECB LCB DSTF BYS SRCB DJ1 DJ2 DJ3 LOA LOS SP16 TPA HINV RCL RLO RHI RRL RRS
    WSK WIM WIS WFS FSS.
  pose proof SF as SF0.
  destruct SF0 as ((buf & BUF & BUFL) & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S
    & FRM & MI & MU & WM).
  pose proof (bv_unsigned_in_range _ l13) as L13R. pose proof (bv_unsigned_in_range _ l14) as L14R.
  pose proof (bv_unsigned_in_range _ l15) as L15R. pose proof (bv_unsigned_in_range _ l16) as L16R.
  rewrite <- (Z_to_bv_bv_unsigned l13) in SPL.
  unfold AZ4_SB in *. cbn [z4R_fl] in *.
  kx_runFLd [583740; 587592; AZ4_C0] 100%nat (@nil bool)
    [KZRange (bv_unsigned sp) 8192 (2^47); KZRange DST 4096 (2^47); KZRange dcap 6 (2^32);
     KZRange e1 0 (2^32); KZRange e2 0 (2^32); KZRange e3 0 (2^32); KZRange e4 0 (2^32);
     KZRange (bv_unsigned l13) 1 2; KZRange (bv_unsigned l14) 1 2; KZRange (bv_unsigned l15) 1 2;
     KZRange (bv_unsigned l16) 1 2;
     KZWord (bv_unsigned sp + -344) 8 (bv_unsigned l13); KZWord (bv_unsigned sp + -352) 8 3;
     KZWord (bv_unsigned sp + -328) 8 3;
     KZWord (bv_unsigned sp + -312) 8 (DST + (dcap + 3) / 4)]
    (@nil (Z * Z)) [(bv_unsigned sp + -400, 400)] (@nil (Z * Z)).
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => z4br end).
  kx_post_regs_keep.
  z4post_ez.
  cbn [mem_denot] in *.
  try replace (bv_unsigned l15 + (DST + e3)) with (DST + (e3 + bv_unsigned l15)) by lia.
  try replace (SS + o1' + 6) with (SS + 6 + o1') by lia.
  try replace (SS + (l1 + o2') + 6) with (SS + 6 + l1 + o2') by lia.
  try replace (SS + (l1 + (l2 + o3')) + 6) with (SS + 6 + l1 + l2 + o3') by lia.
  try replace (SS + (l1 + (l2 + (l3 + o4'))) + 6) with (SS + 6 + l1 + l2 + l3 + o4') by lia.
  replace (SS + (6 + l1 + l2 + l3)) with (SS + 6 + l1 + l2 + l3) in SF by lia.
  replace (SS + (6 + l1 + l2)) with (SS + 6 + l1 + l2) in SF by lia.
  replace (SS + (6 + l1)) with (SS + 6 + l1) in SF by lia.
  eapply (K0 l1 l2 l3 (e1 + bv_unsigned l13) (e2 + bv_unsigned l14) (e3 + bv_unsigned l15) (e4 + bv_unsigned l16)
            o1' o2' o3' o4' b1' b2' b3' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4); [exact SF | .. | exact KE].
  all: unfold z4strm, z4R_pre, z4R_res in *; cbn iota in *; lia.
Qed.

Lemma z4R_tl_0100 : forall RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q,
  z4R_tl_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    false true false false.
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q.
  intros AI L st LB rng_fs cells pdt SBL SBH rstk mm l1 l2 l3 q1 q2 q3 q4 e1 e2 e3 e4 o1 cq1 cr1 o2 cq2 cr2 o3 cq3 cr3
    o4 cq4 cr4 o1' b1' o2' b2' o3' b3' o4' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4 w0 l13 l14 l15 l16 u10 u17 u22 u27 u31
    K0 KE CTX LY P1 P2 P3 P4 R1 R2 R3 R4 L13 L14 L15 L16 E1 E2 E3 E4 QD1 QD2 QD3 QD4 Q1 Q2 Q3 Q4 SF K.
  destruct LY as (HL1 & HL2 & HL3 & HN & HD6 & HSG).
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ltac:(lia))
    as (FD1 & FD2 & FD3 & FT1 & FT2 & FSS & FP1 & FP2 & FRN).
  pose proof CTX as CTX0.
  destruct CTX0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2
    & DJ3 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof (AI_layout AI _ _ _ _ _ AH) as ALY.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  unfold AIMG_HI in FD1, FT1.
  clear AH NFK ABL HDT TOK ECB LCB DSTF BYS SRCB DJ1 DJ2 DJ3 LOA LOS SP16 TPA HINV RCL RLO RHI RRL RRS
    WSK WIM WIS WFS FSS.
  pose proof SF as SF0.
  destruct SF0 as ((buf & BUF & BUFL) & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S
    & FRM & MI & MU & WM).
  pose proof (bv_unsigned_in_range _ l13) as L13R. pose proof (bv_unsigned_in_range _ l14) as L14R.
  pose proof (bv_unsigned_in_range _ l15) as L15R. pose proof (bv_unsigned_in_range _ l16) as L16R.
  rewrite <- (Z_to_bv_bv_unsigned l13) in SPL.
  unfold AZ4_SB in *. cbn [z4R_fl] in *.
  kx_runFLd [583740; 587592; AZ4_C0] 100%nat (@nil bool)
    [KZRange (bv_unsigned sp) 8192 (2^47); KZRange DST 4096 (2^47); KZRange dcap 6 (2^32);
     KZRange e1 0 (2^32); KZRange e2 0 (2^32); KZRange e3 0 (2^32); KZRange e4 0 (2^32);
     KZRange (bv_unsigned l13) 1 2; KZRange (bv_unsigned l14) 1 2; KZRange (bv_unsigned l15) 1 2;
     KZRange (bv_unsigned l16) 1 2;
     KZWord (bv_unsigned sp + -344) 8 (bv_unsigned l13); KZWord (bv_unsigned sp + -352) 8 3;
     KZWord (bv_unsigned sp + -328) 8 0;
     KZWord (bv_unsigned sp + -312) 8 (DST + (dcap + 3) / 4)]
    (@nil (Z * Z)) [(bv_unsigned sp + -400, 400)] (@nil (Z * Z)).
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => z4br end).
  kx_post_regs_keep.
  z4post_ez.
  cbn [mem_denot] in *.
  try replace (bv_unsigned l15 + (DST + e3)) with (DST + (e3 + bv_unsigned l15)) by lia.
  try replace (SS + o1' + 6) with (SS + 6 + o1') by lia.
  try replace (SS + (l1 + o2') + 6) with (SS + 6 + l1 + o2') by lia.
  try replace (SS + (l1 + (l2 + o3')) + 6) with (SS + 6 + l1 + l2 + o3') by lia.
  try replace (SS + (l1 + (l2 + (l3 + o4'))) + 6) with (SS + 6 + l1 + l2 + l3 + o4') by lia.
  replace (SS + (6 + l1 + l2 + l3)) with (SS + 6 + l1 + l2 + l3) in SF by lia.
  replace (SS + (6 + l1 + l2)) with (SS + 6 + l1 + l2) in SF by lia.
  replace (SS + (6 + l1)) with (SS + 6 + l1) in SF by lia.
  eapply (K0 l1 l2 l3 (e1 + bv_unsigned l13) (e2 + bv_unsigned l14) (e3 + bv_unsigned l15) (e4 + bv_unsigned l16)
            o1' o2' o3' o4' b1' b2' b3' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4); [exact SF | .. | exact KE].
  all: unfold z4strm, z4R_pre, z4R_res in *; cbn iota in *; lia.
Qed.

Lemma z4R_tl_0101 : forall RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q,
  z4R_tl_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    false true false true.
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q.
  intros AI L st LB rng_fs cells pdt SBL SBH rstk mm l1 l2 l3 q1 q2 q3 q4 e1 e2 e3 e4 o1 cq1 cr1 o2 cq2 cr2 o3 cq3 cr3
    o4 cq4 cr4 o1' b1' o2' b2' o3' b3' o4' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4 w0 l13 l14 l15 l16 u10 u17 u22 u27 u31
    K0 KE CTX LY P1 P2 P3 P4 R1 R2 R3 R4 L13 L14 L15 L16 E1 E2 E3 E4 QD1 QD2 QD3 QD4 Q1 Q2 Q3 Q4 SF K.
  destruct LY as (HL1 & HL2 & HL3 & HN & HD6 & HSG).
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ltac:(lia))
    as (FD1 & FD2 & FD3 & FT1 & FT2 & FSS & FP1 & FP2 & FRN).
  pose proof CTX as CTX0.
  destruct CTX0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2
    & DJ3 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof (AI_layout AI _ _ _ _ _ AH) as ALY.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  unfold AIMG_HI in FD1, FT1.
  clear AH NFK ABL HDT TOK ECB LCB DSTF BYS SRCB DJ1 DJ2 DJ3 LOA LOS SP16 TPA HINV RCL RLO RHI RRL RRS
    WSK WIM WIS WFS FSS.
  pose proof SF as SF0.
  destruct SF0 as ((buf & BUF & BUFL) & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S
    & FRM & MI & MU & WM).
  pose proof (bv_unsigned_in_range _ l13) as L13R. pose proof (bv_unsigned_in_range _ l14) as L14R.
  pose proof (bv_unsigned_in_range _ l15) as L15R. pose proof (bv_unsigned_in_range _ l16) as L16R.
  rewrite <- (Z_to_bv_bv_unsigned l13) in SPL.
  unfold AZ4_SB in *. cbn [z4R_fl] in *.
  kx_runFLd [583740; 587592; AZ4_C0] 100%nat (@nil bool)
    [KZRange (bv_unsigned sp) 8192 (2^47); KZRange DST 4096 (2^47); KZRange dcap 6 (2^32);
     KZRange e1 0 (2^32); KZRange e2 0 (2^32); KZRange e3 0 (2^32); KZRange e4 0 (2^32);
     KZRange (bv_unsigned l13) 1 2; KZRange (bv_unsigned l14) 1 2; KZRange (bv_unsigned l15) 1 2;
     KZRange (bv_unsigned l16) 1 2;
     KZWord (bv_unsigned sp + -344) 8 (bv_unsigned l13); KZWord (bv_unsigned sp + -352) 8 3;
     KZWord (bv_unsigned sp + -328) 8 0;
     KZWord (bv_unsigned sp + -312) 8 (DST + (dcap + 3) / 4)]
    (@nil (Z * Z)) [(bv_unsigned sp + -400, 400)] (@nil (Z * Z)).
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => z4br end).
  kx_post_regs_keep.
  z4post_ez.
  cbn [mem_denot] in *.
  try replace (bv_unsigned l15 + (DST + e3)) with (DST + (e3 + bv_unsigned l15)) by lia.
  try replace (SS + o1' + 6) with (SS + 6 + o1') by lia.
  try replace (SS + (l1 + o2') + 6) with (SS + 6 + l1 + o2') by lia.
  try replace (SS + (l1 + (l2 + o3')) + 6) with (SS + 6 + l1 + l2 + o3') by lia.
  try replace (SS + (l1 + (l2 + (l3 + o4'))) + 6) with (SS + 6 + l1 + l2 + l3 + o4') by lia.
  replace (SS + (6 + l1 + l2 + l3)) with (SS + 6 + l1 + l2 + l3) in SF by lia.
  replace (SS + (6 + l1 + l2)) with (SS + 6 + l1 + l2) in SF by lia.
  replace (SS + (6 + l1)) with (SS + 6 + l1) in SF by lia.
  eapply (K0 l1 l2 l3 (e1 + bv_unsigned l13) (e2 + bv_unsigned l14) (e3 + bv_unsigned l15) (e4 + bv_unsigned l16)
            o1' o2' o3' o4' b1' b2' b3' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4); [exact SF | .. | exact KE].
  all: unfold z4strm, z4R_pre, z4R_res in *; cbn iota in *; lia.
Qed.

Lemma z4R_tl_0110 : forall RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q,
  z4R_tl_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    false true true false.
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q.
  intros AI L st LB rng_fs cells pdt SBL SBH rstk mm l1 l2 l3 q1 q2 q3 q4 e1 e2 e3 e4 o1 cq1 cr1 o2 cq2 cr2 o3 cq3 cr3
    o4 cq4 cr4 o1' b1' o2' b2' o3' b3' o4' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4 w0 l13 l14 l15 l16 u10 u17 u22 u27 u31
    K0 KE CTX LY P1 P2 P3 P4 R1 R2 R3 R4 L13 L14 L15 L16 E1 E2 E3 E4 QD1 QD2 QD3 QD4 Q1 Q2 Q3 Q4 SF K.
  destruct LY as (HL1 & HL2 & HL3 & HN & HD6 & HSG).
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ltac:(lia))
    as (FD1 & FD2 & FD3 & FT1 & FT2 & FSS & FP1 & FP2 & FRN).
  pose proof CTX as CTX0.
  destruct CTX0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2
    & DJ3 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof (AI_layout AI _ _ _ _ _ AH) as ALY.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  unfold AIMG_HI in FD1, FT1.
  clear AH NFK ABL HDT TOK ECB LCB DSTF BYS SRCB DJ1 DJ2 DJ3 LOA LOS SP16 TPA HINV RCL RLO RHI RRL RRS
    WSK WIM WIS WFS FSS.
  pose proof SF as SF0.
  destruct SF0 as ((buf & BUF & BUFL) & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S
    & FRM & MI & MU & WM).
  pose proof (bv_unsigned_in_range _ l13) as L13R. pose proof (bv_unsigned_in_range _ l14) as L14R.
  pose proof (bv_unsigned_in_range _ l15) as L15R. pose proof (bv_unsigned_in_range _ l16) as L16R.
  rewrite <- (Z_to_bv_bv_unsigned l13) in SPL.
  unfold AZ4_SB in *. cbn [z4R_fl] in *.
  kx_runFLd [583740; 587592; AZ4_C0] 100%nat (@nil bool)
    [KZRange (bv_unsigned sp) 8192 (2^47); KZRange DST 4096 (2^47); KZRange dcap 6 (2^32);
     KZRange e1 0 (2^32); KZRange e2 0 (2^32); KZRange e3 0 (2^32); KZRange e4 0 (2^32);
     KZRange (bv_unsigned l13) 1 2; KZRange (bv_unsigned l14) 1 2; KZRange (bv_unsigned l15) 1 2;
     KZRange (bv_unsigned l16) 1 2;
     KZWord (bv_unsigned sp + -344) 8 (bv_unsigned l13); KZWord (bv_unsigned sp + -352) 8 3;
     KZWord (bv_unsigned sp + -328) 8 0;
     KZWord (bv_unsigned sp + -312) 8 (DST + (dcap + 3) / 4)]
    (@nil (Z * Z)) [(bv_unsigned sp + -400, 400)] (@nil (Z * Z)).
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => z4br end).
  kx_post_regs_keep.
  z4post_ez.
  cbn [mem_denot] in *.
  try replace (bv_unsigned l15 + (DST + e3)) with (DST + (e3 + bv_unsigned l15)) by lia.
  try replace (SS + o1' + 6) with (SS + 6 + o1') by lia.
  try replace (SS + (l1 + o2') + 6) with (SS + 6 + l1 + o2') by lia.
  try replace (SS + (l1 + (l2 + o3')) + 6) with (SS + 6 + l1 + l2 + o3') by lia.
  try replace (SS + (l1 + (l2 + (l3 + o4'))) + 6) with (SS + 6 + l1 + l2 + l3 + o4') by lia.
  replace (SS + (6 + l1 + l2 + l3)) with (SS + 6 + l1 + l2 + l3) in SF by lia.
  replace (SS + (6 + l1 + l2)) with (SS + 6 + l1 + l2) in SF by lia.
  replace (SS + (6 + l1)) with (SS + 6 + l1) in SF by lia.
  eapply (K0 l1 l2 l3 (e1 + bv_unsigned l13) (e2 + bv_unsigned l14) (e3 + bv_unsigned l15) (e4 + bv_unsigned l16)
            o1' o2' o3' o4' b1' b2' b3' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4); [exact SF | .. | exact KE].
  all: unfold z4strm, z4R_pre, z4R_res in *; cbn iota in *; lia.
Qed.

Lemma z4R_tl_0111 : forall RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q,
  z4R_tl_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    false true true true.
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q.
  intros AI L st LB rng_fs cells pdt SBL SBH rstk mm l1 l2 l3 q1 q2 q3 q4 e1 e2 e3 e4 o1 cq1 cr1 o2 cq2 cr2 o3 cq3 cr3
    o4 cq4 cr4 o1' b1' o2' b2' o3' b3' o4' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4 w0 l13 l14 l15 l16 u10 u17 u22 u27 u31
    K0 KE CTX LY P1 P2 P3 P4 R1 R2 R3 R4 L13 L14 L15 L16 E1 E2 E3 E4 QD1 QD2 QD3 QD4 Q1 Q2 Q3 Q4 SF K.
  destruct LY as (HL1 & HL2 & HL3 & HN & HD6 & HSG).
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ltac:(lia))
    as (FD1 & FD2 & FD3 & FT1 & FT2 & FSS & FP1 & FP2 & FRN).
  pose proof CTX as CTX0.
  destruct CTX0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2
    & DJ3 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof (AI_layout AI _ _ _ _ _ AH) as ALY.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  unfold AIMG_HI in FD1, FT1.
  clear AH NFK ABL HDT TOK ECB LCB DSTF BYS SRCB DJ1 DJ2 DJ3 LOA LOS SP16 TPA HINV RCL RLO RHI RRL RRS
    WSK WIM WIS WFS FSS.
  pose proof SF as SF0.
  destruct SF0 as ((buf & BUF & BUFL) & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S
    & FRM & MI & MU & WM).
  pose proof (bv_unsigned_in_range _ l13) as L13R. pose proof (bv_unsigned_in_range _ l14) as L14R.
  pose proof (bv_unsigned_in_range _ l15) as L15R. pose proof (bv_unsigned_in_range _ l16) as L16R.
  rewrite <- (Z_to_bv_bv_unsigned l13) in SPL.
  unfold AZ4_SB in *. cbn [z4R_fl] in *.
  kx_runFLd [583740; 587592; AZ4_C0] 100%nat (@nil bool)
    [KZRange (bv_unsigned sp) 8192 (2^47); KZRange DST 4096 (2^47); KZRange dcap 6 (2^32);
     KZRange e1 0 (2^32); KZRange e2 0 (2^32); KZRange e3 0 (2^32); KZRange e4 0 (2^32);
     KZRange (bv_unsigned l13) 1 2; KZRange (bv_unsigned l14) 1 2; KZRange (bv_unsigned l15) 1 2;
     KZRange (bv_unsigned l16) 1 2;
     KZWord (bv_unsigned sp + -344) 8 (bv_unsigned l13); KZWord (bv_unsigned sp + -352) 8 3;
     KZWord (bv_unsigned sp + -328) 8 0;
     KZWord (bv_unsigned sp + -312) 8 (DST + (dcap + 3) / 4)]
    (@nil (Z * Z)) [(bv_unsigned sp + -400, 400)] (@nil (Z * Z)).
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => z4br end).
  kx_post_regs_keep.
  z4post_ez.
  cbn [mem_denot] in *.
  try replace (bv_unsigned l15 + (DST + e3)) with (DST + (e3 + bv_unsigned l15)) by lia.
  try replace (SS + o1' + 6) with (SS + 6 + o1') by lia.
  try replace (SS + (l1 + o2') + 6) with (SS + 6 + l1 + o2') by lia.
  try replace (SS + (l1 + (l2 + o3')) + 6) with (SS + 6 + l1 + l2 + o3') by lia.
  try replace (SS + (l1 + (l2 + (l3 + o4'))) + 6) with (SS + 6 + l1 + l2 + l3 + o4') by lia.
  replace (SS + (6 + l1 + l2 + l3)) with (SS + 6 + l1 + l2 + l3) in SF by lia.
  replace (SS + (6 + l1 + l2)) with (SS + 6 + l1 + l2) in SF by lia.
  replace (SS + (6 + l1)) with (SS + 6 + l1) in SF by lia.
  eapply (K0 l1 l2 l3 (e1 + bv_unsigned l13) (e2 + bv_unsigned l14) (e3 + bv_unsigned l15) (e4 + bv_unsigned l16)
            o1' o2' o3' o4' b1' b2' b3' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4); [exact SF | .. | exact KE].
  all: unfold z4strm, z4R_pre, z4R_res in *; cbn iota in *; lia.
Qed.

Lemma z4R_tl_1000 : forall RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q,
  z4R_tl_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    true false false false.
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q.
  intros AI L st LB rng_fs cells pdt SBL SBH rstk mm l1 l2 l3 q1 q2 q3 q4 e1 e2 e3 e4 o1 cq1 cr1 o2 cq2 cr2 o3 cq3 cr3
    o4 cq4 cr4 o1' b1' o2' b2' o3' b3' o4' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4 w0 l13 l14 l15 l16 u10 u17 u22 u27 u31
    K0 KE CTX LY P1 P2 P3 P4 R1 R2 R3 R4 L13 L14 L15 L16 E1 E2 E3 E4 QD1 QD2 QD3 QD4 Q1 Q2 Q3 Q4 SF K.
  destruct LY as (HL1 & HL2 & HL3 & HN & HD6 & HSG).
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ltac:(lia))
    as (FD1 & FD2 & FD3 & FT1 & FT2 & FSS & FP1 & FP2 & FRN).
  pose proof CTX as CTX0.
  destruct CTX0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2
    & DJ3 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof (AI_layout AI _ _ _ _ _ AH) as ALY.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  unfold AIMG_HI in FD1, FT1.
  clear AH NFK ABL HDT TOK ECB LCB DSTF BYS SRCB DJ1 DJ2 DJ3 LOA LOS SP16 TPA HINV RCL RLO RHI RRL RRS
    WSK WIM WIS WFS FSS.
  pose proof SF as SF0.
  destruct SF0 as ((buf & BUF & BUFL) & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S
    & FRM & MI & MU & WM).
  pose proof (bv_unsigned_in_range _ l13) as L13R. pose proof (bv_unsigned_in_range _ l14) as L14R.
  pose proof (bv_unsigned_in_range _ l15) as L15R. pose proof (bv_unsigned_in_range _ l16) as L16R.
  rewrite <- (Z_to_bv_bv_unsigned l13) in SPL.
  unfold AZ4_SB in *. cbn [z4R_fl] in *.
  kx_runFLd [583740; 587592; AZ4_C0] 100%nat (@nil bool)
    [KZRange (bv_unsigned sp) 8192 (2^47); KZRange DST 4096 (2^47); KZRange dcap 6 (2^32);
     KZRange e1 0 (2^32); KZRange e2 0 (2^32); KZRange e3 0 (2^32); KZRange e4 0 (2^32);
     KZRange (bv_unsigned l13) 1 2; KZRange (bv_unsigned l14) 1 2; KZRange (bv_unsigned l15) 1 2;
     KZRange (bv_unsigned l16) 1 2;
     KZWord (bv_unsigned sp + -344) 8 (bv_unsigned l13); KZWord (bv_unsigned sp + -352) 8 0;
     KZWord (bv_unsigned sp + -328) 8 3;
     KZWord (bv_unsigned sp + -312) 8 (DST + (dcap + 3) / 4)]
    (@nil (Z * Z)) [(bv_unsigned sp + -400, 400)] (@nil (Z * Z)).
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => z4br end).
  kx_post_regs_keep.
  z4post_ez.
  cbn [mem_denot] in *.
  try replace (bv_unsigned l15 + (DST + e3)) with (DST + (e3 + bv_unsigned l15)) by lia.
  try replace (SS + o1' + 6) with (SS + 6 + o1') by lia.
  try replace (SS + (l1 + o2') + 6) with (SS + 6 + l1 + o2') by lia.
  try replace (SS + (l1 + (l2 + o3')) + 6) with (SS + 6 + l1 + l2 + o3') by lia.
  try replace (SS + (l1 + (l2 + (l3 + o4'))) + 6) with (SS + 6 + l1 + l2 + l3 + o4') by lia.
  replace (SS + (6 + l1 + l2 + l3)) with (SS + 6 + l1 + l2 + l3) in SF by lia.
  replace (SS + (6 + l1 + l2)) with (SS + 6 + l1 + l2) in SF by lia.
  replace (SS + (6 + l1)) with (SS + 6 + l1) in SF by lia.
  eapply (K0 l1 l2 l3 (e1 + bv_unsigned l13) (e2 + bv_unsigned l14) (e3 + bv_unsigned l15) (e4 + bv_unsigned l16)
            o1' o2' o3' o4' b1' b2' b3' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4); [exact SF | .. | exact KE].
  all: unfold z4strm, z4R_pre, z4R_res in *; cbn iota in *; lia.
Qed.

Lemma z4R_tl_1001 : forall RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q,
  z4R_tl_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    true false false true.
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q.
  intros AI L st LB rng_fs cells pdt SBL SBH rstk mm l1 l2 l3 q1 q2 q3 q4 e1 e2 e3 e4 o1 cq1 cr1 o2 cq2 cr2 o3 cq3 cr3
    o4 cq4 cr4 o1' b1' o2' b2' o3' b3' o4' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4 w0 l13 l14 l15 l16 u10 u17 u22 u27 u31
    K0 KE CTX LY P1 P2 P3 P4 R1 R2 R3 R4 L13 L14 L15 L16 E1 E2 E3 E4 QD1 QD2 QD3 QD4 Q1 Q2 Q3 Q4 SF K.
  destruct LY as (HL1 & HL2 & HL3 & HN & HD6 & HSG).
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ltac:(lia))
    as (FD1 & FD2 & FD3 & FT1 & FT2 & FSS & FP1 & FP2 & FRN).
  pose proof CTX as CTX0.
  destruct CTX0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2
    & DJ3 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof (AI_layout AI _ _ _ _ _ AH) as ALY.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  unfold AIMG_HI in FD1, FT1.
  clear AH NFK ABL HDT TOK ECB LCB DSTF BYS SRCB DJ1 DJ2 DJ3 LOA LOS SP16 TPA HINV RCL RLO RHI RRL RRS
    WSK WIM WIS WFS FSS.
  pose proof SF as SF0.
  destruct SF0 as ((buf & BUF & BUFL) & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S
    & FRM & MI & MU & WM).
  pose proof (bv_unsigned_in_range _ l13) as L13R. pose proof (bv_unsigned_in_range _ l14) as L14R.
  pose proof (bv_unsigned_in_range _ l15) as L15R. pose proof (bv_unsigned_in_range _ l16) as L16R.
  rewrite <- (Z_to_bv_bv_unsigned l13) in SPL.
  unfold AZ4_SB in *. cbn [z4R_fl] in *.
  kx_runFLd [583740; 587592; AZ4_C0] 100%nat (@nil bool)
    [KZRange (bv_unsigned sp) 8192 (2^47); KZRange DST 4096 (2^47); KZRange dcap 6 (2^32);
     KZRange e1 0 (2^32); KZRange e2 0 (2^32); KZRange e3 0 (2^32); KZRange e4 0 (2^32);
     KZRange (bv_unsigned l13) 1 2; KZRange (bv_unsigned l14) 1 2; KZRange (bv_unsigned l15) 1 2;
     KZRange (bv_unsigned l16) 1 2;
     KZWord (bv_unsigned sp + -344) 8 (bv_unsigned l13); KZWord (bv_unsigned sp + -352) 8 0;
     KZWord (bv_unsigned sp + -328) 8 3;
     KZWord (bv_unsigned sp + -312) 8 (DST + (dcap + 3) / 4)]
    (@nil (Z * Z)) [(bv_unsigned sp + -400, 400)] (@nil (Z * Z)).
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => z4br end).
  kx_post_regs_keep.
  z4post_ez.
  cbn [mem_denot] in *.
  try replace (bv_unsigned l15 + (DST + e3)) with (DST + (e3 + bv_unsigned l15)) by lia.
  try replace (SS + o1' + 6) with (SS + 6 + o1') by lia.
  try replace (SS + (l1 + o2') + 6) with (SS + 6 + l1 + o2') by lia.
  try replace (SS + (l1 + (l2 + o3')) + 6) with (SS + 6 + l1 + l2 + o3') by lia.
  try replace (SS + (l1 + (l2 + (l3 + o4'))) + 6) with (SS + 6 + l1 + l2 + l3 + o4') by lia.
  replace (SS + (6 + l1 + l2 + l3)) with (SS + 6 + l1 + l2 + l3) in SF by lia.
  replace (SS + (6 + l1 + l2)) with (SS + 6 + l1 + l2) in SF by lia.
  replace (SS + (6 + l1)) with (SS + 6 + l1) in SF by lia.
  eapply (K0 l1 l2 l3 (e1 + bv_unsigned l13) (e2 + bv_unsigned l14) (e3 + bv_unsigned l15) (e4 + bv_unsigned l16)
            o1' o2' o3' o4' b1' b2' b3' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4); [exact SF | .. | exact KE].
  all: unfold z4strm, z4R_pre, z4R_res in *; cbn iota in *; lia.
Qed.

Lemma z4R_tl_1010 : forall RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q,
  z4R_tl_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    true false true false.
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q.
  intros AI L st LB rng_fs cells pdt SBL SBH rstk mm l1 l2 l3 q1 q2 q3 q4 e1 e2 e3 e4 o1 cq1 cr1 o2 cq2 cr2 o3 cq3 cr3
    o4 cq4 cr4 o1' b1' o2' b2' o3' b3' o4' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4 w0 l13 l14 l15 l16 u10 u17 u22 u27 u31
    K0 KE CTX LY P1 P2 P3 P4 R1 R2 R3 R4 L13 L14 L15 L16 E1 E2 E3 E4 QD1 QD2 QD3 QD4 Q1 Q2 Q3 Q4 SF K.
  destruct LY as (HL1 & HL2 & HL3 & HN & HD6 & HSG).
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ltac:(lia))
    as (FD1 & FD2 & FD3 & FT1 & FT2 & FSS & FP1 & FP2 & FRN).
  pose proof CTX as CTX0.
  destruct CTX0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2
    & DJ3 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof (AI_layout AI _ _ _ _ _ AH) as ALY.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  unfold AIMG_HI in FD1, FT1.
  clear AH NFK ABL HDT TOK ECB LCB DSTF BYS SRCB DJ1 DJ2 DJ3 LOA LOS SP16 TPA HINV RCL RLO RHI RRL RRS
    WSK WIM WIS WFS FSS.
  pose proof SF as SF0.
  destruct SF0 as ((buf & BUF & BUFL) & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S
    & FRM & MI & MU & WM).
  pose proof (bv_unsigned_in_range _ l13) as L13R. pose proof (bv_unsigned_in_range _ l14) as L14R.
  pose proof (bv_unsigned_in_range _ l15) as L15R. pose proof (bv_unsigned_in_range _ l16) as L16R.
  rewrite <- (Z_to_bv_bv_unsigned l13) in SPL.
  unfold AZ4_SB in *. cbn [z4R_fl] in *.
  kx_runFLd [583740; 587592; AZ4_C0] 100%nat (@nil bool)
    [KZRange (bv_unsigned sp) 8192 (2^47); KZRange DST 4096 (2^47); KZRange dcap 6 (2^32);
     KZRange e1 0 (2^32); KZRange e2 0 (2^32); KZRange e3 0 (2^32); KZRange e4 0 (2^32);
     KZRange (bv_unsigned l13) 1 2; KZRange (bv_unsigned l14) 1 2; KZRange (bv_unsigned l15) 1 2;
     KZRange (bv_unsigned l16) 1 2;
     KZWord (bv_unsigned sp + -344) 8 (bv_unsigned l13); KZWord (bv_unsigned sp + -352) 8 0;
     KZWord (bv_unsigned sp + -328) 8 3;
     KZWord (bv_unsigned sp + -312) 8 (DST + (dcap + 3) / 4)]
    (@nil (Z * Z)) [(bv_unsigned sp + -400, 400)] (@nil (Z * Z)).
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => z4br end).
  kx_post_regs_keep.
  z4post_ez.
  cbn [mem_denot] in *.
  try replace (bv_unsigned l15 + (DST + e3)) with (DST + (e3 + bv_unsigned l15)) by lia.
  try replace (SS + o1' + 6) with (SS + 6 + o1') by lia.
  try replace (SS + (l1 + o2') + 6) with (SS + 6 + l1 + o2') by lia.
  try replace (SS + (l1 + (l2 + o3')) + 6) with (SS + 6 + l1 + l2 + o3') by lia.
  try replace (SS + (l1 + (l2 + (l3 + o4'))) + 6) with (SS + 6 + l1 + l2 + l3 + o4') by lia.
  replace (SS + (6 + l1 + l2 + l3)) with (SS + 6 + l1 + l2 + l3) in SF by lia.
  replace (SS + (6 + l1 + l2)) with (SS + 6 + l1 + l2) in SF by lia.
  replace (SS + (6 + l1)) with (SS + 6 + l1) in SF by lia.
  eapply (K0 l1 l2 l3 (e1 + bv_unsigned l13) (e2 + bv_unsigned l14) (e3 + bv_unsigned l15) (e4 + bv_unsigned l16)
            o1' o2' o3' o4' b1' b2' b3' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4); [exact SF | .. | exact KE].
  all: unfold z4strm, z4R_pre, z4R_res in *; cbn iota in *; lia.
Qed.

Lemma z4R_tl_1011 : forall RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q,
  z4R_tl_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    true false true true.
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q.
  intros AI L st LB rng_fs cells pdt SBL SBH rstk mm l1 l2 l3 q1 q2 q3 q4 e1 e2 e3 e4 o1 cq1 cr1 o2 cq2 cr2 o3 cq3 cr3
    o4 cq4 cr4 o1' b1' o2' b2' o3' b3' o4' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4 w0 l13 l14 l15 l16 u10 u17 u22 u27 u31
    K0 KE CTX LY P1 P2 P3 P4 R1 R2 R3 R4 L13 L14 L15 L16 E1 E2 E3 E4 QD1 QD2 QD3 QD4 Q1 Q2 Q3 Q4 SF K.
  destruct LY as (HL1 & HL2 & HL3 & HN & HD6 & HSG).
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ltac:(lia))
    as (FD1 & FD2 & FD3 & FT1 & FT2 & FSS & FP1 & FP2 & FRN).
  pose proof CTX as CTX0.
  destruct CTX0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2
    & DJ3 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof (AI_layout AI _ _ _ _ _ AH) as ALY.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  unfold AIMG_HI in FD1, FT1.
  clear AH NFK ABL HDT TOK ECB LCB DSTF BYS SRCB DJ1 DJ2 DJ3 LOA LOS SP16 TPA HINV RCL RLO RHI RRL RRS
    WSK WIM WIS WFS FSS.
  pose proof SF as SF0.
  destruct SF0 as ((buf & BUF & BUFL) & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S
    & FRM & MI & MU & WM).
  pose proof (bv_unsigned_in_range _ l13) as L13R. pose proof (bv_unsigned_in_range _ l14) as L14R.
  pose proof (bv_unsigned_in_range _ l15) as L15R. pose proof (bv_unsigned_in_range _ l16) as L16R.
  rewrite <- (Z_to_bv_bv_unsigned l13) in SPL.
  unfold AZ4_SB in *. cbn [z4R_fl] in *.
  kx_runFLd [583740; 587592; AZ4_C0] 100%nat (@nil bool)
    [KZRange (bv_unsigned sp) 8192 (2^47); KZRange DST 4096 (2^47); KZRange dcap 6 (2^32);
     KZRange e1 0 (2^32); KZRange e2 0 (2^32); KZRange e3 0 (2^32); KZRange e4 0 (2^32);
     KZRange (bv_unsigned l13) 1 2; KZRange (bv_unsigned l14) 1 2; KZRange (bv_unsigned l15) 1 2;
     KZRange (bv_unsigned l16) 1 2;
     KZWord (bv_unsigned sp + -344) 8 (bv_unsigned l13); KZWord (bv_unsigned sp + -352) 8 0;
     KZWord (bv_unsigned sp + -328) 8 3;
     KZWord (bv_unsigned sp + -312) 8 (DST + (dcap + 3) / 4)]
    (@nil (Z * Z)) [(bv_unsigned sp + -400, 400)] (@nil (Z * Z)).
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => z4br end).
  kx_post_regs_keep.
  z4post_ez.
  cbn [mem_denot] in *.
  try replace (bv_unsigned l15 + (DST + e3)) with (DST + (e3 + bv_unsigned l15)) by lia.
  try replace (SS + o1' + 6) with (SS + 6 + o1') by lia.
  try replace (SS + (l1 + o2') + 6) with (SS + 6 + l1 + o2') by lia.
  try replace (SS + (l1 + (l2 + o3')) + 6) with (SS + 6 + l1 + l2 + o3') by lia.
  try replace (SS + (l1 + (l2 + (l3 + o4'))) + 6) with (SS + 6 + l1 + l2 + l3 + o4') by lia.
  replace (SS + (6 + l1 + l2 + l3)) with (SS + 6 + l1 + l2 + l3) in SF by lia.
  replace (SS + (6 + l1 + l2)) with (SS + 6 + l1 + l2) in SF by lia.
  replace (SS + (6 + l1)) with (SS + 6 + l1) in SF by lia.
  eapply (K0 l1 l2 l3 (e1 + bv_unsigned l13) (e2 + bv_unsigned l14) (e3 + bv_unsigned l15) (e4 + bv_unsigned l16)
            o1' o2' o3' o4' b1' b2' b3' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4); [exact SF | .. | exact KE].
  all: unfold z4strm, z4R_pre, z4R_res in *; cbn iota in *; lia.
Qed.

Lemma z4R_tl_1100 : forall RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q,
  z4R_tl_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    true true false false.
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q.
  intros AI L st LB rng_fs cells pdt SBL SBH rstk mm l1 l2 l3 q1 q2 q3 q4 e1 e2 e3 e4 o1 cq1 cr1 o2 cq2 cr2 o3 cq3 cr3
    o4 cq4 cr4 o1' b1' o2' b2' o3' b3' o4' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4 w0 l13 l14 l15 l16 u10 u17 u22 u27 u31
    K0 KE CTX LY P1 P2 P3 P4 R1 R2 R3 R4 L13 L14 L15 L16 E1 E2 E3 E4 QD1 QD2 QD3 QD4 Q1 Q2 Q3 Q4 SF K.
  destruct LY as (HL1 & HL2 & HL3 & HN & HD6 & HSG).
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ltac:(lia))
    as (FD1 & FD2 & FD3 & FT1 & FT2 & FSS & FP1 & FP2 & FRN).
  pose proof CTX as CTX0.
  destruct CTX0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2
    & DJ3 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof (AI_layout AI _ _ _ _ _ AH) as ALY.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  unfold AIMG_HI in FD1, FT1.
  clear AH NFK ABL HDT TOK ECB LCB DSTF BYS SRCB DJ1 DJ2 DJ3 LOA LOS SP16 TPA HINV RCL RLO RHI RRL RRS
    WSK WIM WIS WFS FSS.
  pose proof SF as SF0.
  destruct SF0 as ((buf & BUF & BUFL) & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S
    & FRM & MI & MU & WM).
  pose proof (bv_unsigned_in_range _ l13) as L13R. pose proof (bv_unsigned_in_range _ l14) as L14R.
  pose proof (bv_unsigned_in_range _ l15) as L15R. pose proof (bv_unsigned_in_range _ l16) as L16R.
  rewrite <- (Z_to_bv_bv_unsigned l13) in SPL.
  unfold AZ4_SB in *. cbn [z4R_fl] in *.
  kx_runFLd [583740; 587592; AZ4_C0] 100%nat (@nil bool)
    [KZRange (bv_unsigned sp) 8192 (2^47); KZRange DST 4096 (2^47); KZRange dcap 6 (2^32);
     KZRange e1 0 (2^32); KZRange e2 0 (2^32); KZRange e3 0 (2^32); KZRange e4 0 (2^32);
     KZRange (bv_unsigned l13) 1 2; KZRange (bv_unsigned l14) 1 2; KZRange (bv_unsigned l15) 1 2;
     KZRange (bv_unsigned l16) 1 2;
     KZWord (bv_unsigned sp + -344) 8 (bv_unsigned l13); KZWord (bv_unsigned sp + -352) 8 0;
     KZWord (bv_unsigned sp + -328) 8 0;
     KZWord (bv_unsigned sp + -312) 8 (DST + (dcap + 3) / 4)]
    (@nil (Z * Z)) [(bv_unsigned sp + -400, 400)] (@nil (Z * Z)).
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => z4br end).
  kx_post_regs_keep.
  z4post_ez.
  cbn [mem_denot] in *.
  try replace (bv_unsigned l15 + (DST + e3)) with (DST + (e3 + bv_unsigned l15)) by lia.
  try replace (SS + o1' + 6) with (SS + 6 + o1') by lia.
  try replace (SS + (l1 + o2') + 6) with (SS + 6 + l1 + o2') by lia.
  try replace (SS + (l1 + (l2 + o3')) + 6) with (SS + 6 + l1 + l2 + o3') by lia.
  try replace (SS + (l1 + (l2 + (l3 + o4'))) + 6) with (SS + 6 + l1 + l2 + l3 + o4') by lia.
  replace (SS + (6 + l1 + l2 + l3)) with (SS + 6 + l1 + l2 + l3) in SF by lia.
  replace (SS + (6 + l1 + l2)) with (SS + 6 + l1 + l2) in SF by lia.
  replace (SS + (6 + l1)) with (SS + 6 + l1) in SF by lia.
  eapply (K0 l1 l2 l3 (e1 + bv_unsigned l13) (e2 + bv_unsigned l14) (e3 + bv_unsigned l15) (e4 + bv_unsigned l16)
            o1' o2' o3' o4' b1' b2' b3' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4); [exact SF | .. | exact KE].
  all: unfold z4strm, z4R_pre, z4R_res in *; cbn iota in *; lia.
Qed.

Lemma z4R_tl_1101 : forall RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q,
  z4R_tl_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    true true false true.
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q.
  intros AI L st LB rng_fs cells pdt SBL SBH rstk mm l1 l2 l3 q1 q2 q3 q4 e1 e2 e3 e4 o1 cq1 cr1 o2 cq2 cr2 o3 cq3 cr3
    o4 cq4 cr4 o1' b1' o2' b2' o3' b3' o4' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4 w0 l13 l14 l15 l16 u10 u17 u22 u27 u31
    K0 KE CTX LY P1 P2 P3 P4 R1 R2 R3 R4 L13 L14 L15 L16 E1 E2 E3 E4 QD1 QD2 QD3 QD4 Q1 Q2 Q3 Q4 SF K.
  destruct LY as (HL1 & HL2 & HL3 & HN & HD6 & HSG).
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ltac:(lia))
    as (FD1 & FD2 & FD3 & FT1 & FT2 & FSS & FP1 & FP2 & FRN).
  pose proof CTX as CTX0.
  destruct CTX0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2
    & DJ3 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof (AI_layout AI _ _ _ _ _ AH) as ALY.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  unfold AIMG_HI in FD1, FT1.
  clear AH NFK ABL HDT TOK ECB LCB DSTF BYS SRCB DJ1 DJ2 DJ3 LOA LOS SP16 TPA HINV RCL RLO RHI RRL RRS
    WSK WIM WIS WFS FSS.
  pose proof SF as SF0.
  destruct SF0 as ((buf & BUF & BUFL) & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S
    & FRM & MI & MU & WM).
  pose proof (bv_unsigned_in_range _ l13) as L13R. pose proof (bv_unsigned_in_range _ l14) as L14R.
  pose proof (bv_unsigned_in_range _ l15) as L15R. pose proof (bv_unsigned_in_range _ l16) as L16R.
  rewrite <- (Z_to_bv_bv_unsigned l13) in SPL.
  unfold AZ4_SB in *. cbn [z4R_fl] in *.
  kx_runFLd [583740; 587592; AZ4_C0] 100%nat (@nil bool)
    [KZRange (bv_unsigned sp) 8192 (2^47); KZRange DST 4096 (2^47); KZRange dcap 6 (2^32);
     KZRange e1 0 (2^32); KZRange e2 0 (2^32); KZRange e3 0 (2^32); KZRange e4 0 (2^32);
     KZRange (bv_unsigned l13) 1 2; KZRange (bv_unsigned l14) 1 2; KZRange (bv_unsigned l15) 1 2;
     KZRange (bv_unsigned l16) 1 2;
     KZWord (bv_unsigned sp + -344) 8 (bv_unsigned l13); KZWord (bv_unsigned sp + -352) 8 0;
     KZWord (bv_unsigned sp + -328) 8 0;
     KZWord (bv_unsigned sp + -312) 8 (DST + (dcap + 3) / 4)]
    (@nil (Z * Z)) [(bv_unsigned sp + -400, 400)] (@nil (Z * Z)).
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => z4br end).
  kx_post_regs_keep.
  z4post_ez.
  cbn [mem_denot] in *.
  try replace (bv_unsigned l15 + (DST + e3)) with (DST + (e3 + bv_unsigned l15)) by lia.
  try replace (SS + o1' + 6) with (SS + 6 + o1') by lia.
  try replace (SS + (l1 + o2') + 6) with (SS + 6 + l1 + o2') by lia.
  try replace (SS + (l1 + (l2 + o3')) + 6) with (SS + 6 + l1 + l2 + o3') by lia.
  try replace (SS + (l1 + (l2 + (l3 + o4'))) + 6) with (SS + 6 + l1 + l2 + l3 + o4') by lia.
  replace (SS + (6 + l1 + l2 + l3)) with (SS + 6 + l1 + l2 + l3) in SF by lia.
  replace (SS + (6 + l1 + l2)) with (SS + 6 + l1 + l2) in SF by lia.
  replace (SS + (6 + l1)) with (SS + 6 + l1) in SF by lia.
  eapply (K0 l1 l2 l3 (e1 + bv_unsigned l13) (e2 + bv_unsigned l14) (e3 + bv_unsigned l15) (e4 + bv_unsigned l16)
            o1' o2' o3' o4' b1' b2' b3' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4); [exact SF | .. | exact KE].
  all: unfold z4strm, z4R_pre, z4R_res in *; cbn iota in *; lia.
Qed.

Lemma z4R_tl_1110 : forall RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q,
  z4R_tl_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    true true true false.
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q.
  intros AI L st LB rng_fs cells pdt SBL SBH rstk mm l1 l2 l3 q1 q2 q3 q4 e1 e2 e3 e4 o1 cq1 cr1 o2 cq2 cr2 o3 cq3 cr3
    o4 cq4 cr4 o1' b1' o2' b2' o3' b3' o4' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4 w0 l13 l14 l15 l16 u10 u17 u22 u27 u31
    K0 KE CTX LY P1 P2 P3 P4 R1 R2 R3 R4 L13 L14 L15 L16 E1 E2 E3 E4 QD1 QD2 QD3 QD4 Q1 Q2 Q3 Q4 SF K.
  destruct LY as (HL1 & HL2 & HL3 & HN & HD6 & HSG).
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ltac:(lia))
    as (FD1 & FD2 & FD3 & FT1 & FT2 & FSS & FP1 & FP2 & FRN).
  pose proof CTX as CTX0.
  destruct CTX0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2
    & DJ3 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof (AI_layout AI _ _ _ _ _ AH) as ALY.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  unfold AIMG_HI in FD1, FT1.
  clear AH NFK ABL HDT TOK ECB LCB DSTF BYS SRCB DJ1 DJ2 DJ3 LOA LOS SP16 TPA HINV RCL RLO RHI RRL RRS
    WSK WIM WIS WFS FSS.
  pose proof SF as SF0.
  destruct SF0 as ((buf & BUF & BUFL) & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S
    & FRM & MI & MU & WM).
  pose proof (bv_unsigned_in_range _ l13) as L13R. pose proof (bv_unsigned_in_range _ l14) as L14R.
  pose proof (bv_unsigned_in_range _ l15) as L15R. pose proof (bv_unsigned_in_range _ l16) as L16R.
  rewrite <- (Z_to_bv_bv_unsigned l13) in SPL.
  unfold AZ4_SB in *. cbn [z4R_fl] in *.
  kx_runFLd [583740; 587592; AZ4_C0] 100%nat (@nil bool)
    [KZRange (bv_unsigned sp) 8192 (2^47); KZRange DST 4096 (2^47); KZRange dcap 6 (2^32);
     KZRange e1 0 (2^32); KZRange e2 0 (2^32); KZRange e3 0 (2^32); KZRange e4 0 (2^32);
     KZRange (bv_unsigned l13) 1 2; KZRange (bv_unsigned l14) 1 2; KZRange (bv_unsigned l15) 1 2;
     KZRange (bv_unsigned l16) 1 2;
     KZWord (bv_unsigned sp + -344) 8 (bv_unsigned l13); KZWord (bv_unsigned sp + -352) 8 0;
     KZWord (bv_unsigned sp + -328) 8 0;
     KZWord (bv_unsigned sp + -312) 8 (DST + (dcap + 3) / 4)]
    (@nil (Z * Z)) [(bv_unsigned sp + -400, 400)] (@nil (Z * Z)).
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => z4br end).
  kx_post_regs_keep.
  z4post_ez.
  cbn [mem_denot] in *.
  try replace (bv_unsigned l15 + (DST + e3)) with (DST + (e3 + bv_unsigned l15)) by lia.
  try replace (SS + o1' + 6) with (SS + 6 + o1') by lia.
  try replace (SS + (l1 + o2') + 6) with (SS + 6 + l1 + o2') by lia.
  try replace (SS + (l1 + (l2 + o3')) + 6) with (SS + 6 + l1 + l2 + o3') by lia.
  try replace (SS + (l1 + (l2 + (l3 + o4'))) + 6) with (SS + 6 + l1 + l2 + l3 + o4') by lia.
  replace (SS + (6 + l1 + l2 + l3)) with (SS + 6 + l1 + l2 + l3) in SF by lia.
  replace (SS + (6 + l1 + l2)) with (SS + 6 + l1 + l2) in SF by lia.
  replace (SS + (6 + l1)) with (SS + 6 + l1) in SF by lia.
  eapply (K0 l1 l2 l3 (e1 + bv_unsigned l13) (e2 + bv_unsigned l14) (e3 + bv_unsigned l15) (e4 + bv_unsigned l16)
            o1' o2' o3' o4' b1' b2' b3' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4); [exact SF | .. | exact KE].
  all: unfold z4strm, z4R_pre, z4R_res in *; cbn iota in *; lia.
Qed.

Lemma z4R_tl : forall RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    r1 r2 r3 r4,
  z4R_tl_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q r1 r2 r3 r4.
Proof. intros; destruct r1, r2, r3, r4; [ apply z4R_tl_1111 | apply z4R_tl_1110 | apply z4R_tl_1101 | apply z4R_tl_1100 | apply z4R_tl_1011 | apply z4R_tl_1010 | apply z4R_tl_1001 | apply z4R_tl_1000 | apply z4R_tl_0111 | apply z4R_tl_0110 | apply z4R_tl_0101 | apply z4R_tl_0100 | apply z4R_tl_0011 | apply z4R_tl_0010 | apply z4R_tl_0001 | apply z4R_tl_0000 ]. Qed.

Lemma z4R_comp :
  (forall RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q r1 r2, z4R_s2_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q r1 r2) ->
  (forall RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q r1 r2 r3 r4, z4R_s34_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q r1 r2 r3 r4) ->
  forall r1 r2 r3 r4, z4R_case r1 r2 r3 r4.
Proof.
  intros S2 S34 r1 r2 r3 r4 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q AI L st LB rng_fs cells pdt SBL SBH rstk CTX.
  unfold z4R_goal.
  intros K0 KE mm l1 l2 l3 q1 q2 q3 q4 e1 e2 e3 e4 o1 o2 o3 o4 cq1 cr1 cq2 cr2 cq3 cr3 cq4 cr4 k1 k2 k3 k4 jp1 jp2 jp3 jp4
    w0 w4 w7 l13 l14 l15 l16 x13 x22 x23 x27 x28 x29 SF HL1 HL2 HL3 HN HD6 HSG P1 P2 P3 P4 L13 L14 L15 L16
    E1 E2 E3 E4 QD1 QD2 QD3 QD4 Q1 Q2 Q3 Q4 K.
  assert (LAY : 1 <= l1 /\ 1 <= l2 /\ 1 <= l3 /\ 6 + l1 + l2 + l3 + 1 <= zlen src /\ 6 <= dcap /\ 3 * ((dcap + 3) / 4) <= dcap)
    by (repeat split; assumption).
  eapply (z4R_s1 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q r1 AI L st LB rng_fs cells pdt SBL SBH rstk); [exact CTX | exact LAY | exact P1 | exact SF |].
  intros mm1 o1' b1' c1 v14 v22 v27 v28 v29 v31 SF1 R1.
  eapply (S2 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q r1 r2 AI L st LB rng_fs cells pdt SBL SBH rstk); [exact CTX | exact LAY | exact P2 | exact SF1 |].
  intros mm2 o2' b2' c2 u15 u22 u27 u28 u29 u31 SF2 R2.
  eapply (S34 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q r1 r2 r3 r4 AI L st LB rng_fs cells pdt SBL SBH rstk); [exact CTX | exact LAY | exact P3 | exact P4 | exact SF2 |].
  intros mm3 o3' b3' o4' b4' c3 c4 y10 y17 y22 y27 y31 SF3 R3 R4.
  exact (z4R_tl RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q r1 r2 r3 r4 AI L st LB rng_fs cells pdt SBL SBH rstk mm3 l1 l2 l3 q1 q2 q3 q4 e1 e2 e3 e4
           o1 cq1 cr1 o2 cq2 cr2 o3 cq3 cr3 o4 cq4 cr4 o1' b1' o2' b2' o3' b3' o4' b4' c1 c2 c3 c4 jp1 jp2 jp3 jp4
           w0 l13 l14 l15 l16 y10 y17 y22 y27 y31 K0 KE CTX LAY P1 P2 P3 P4 R1 R2 R3 R4 L13 L14 L15 L16
           E1 E2 E3 E4 QD1 QD2 QD3 QD4 Q1 Q2 Q3 Q4 SF3 K).
Qed.

End CANSEC1.
