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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_w4s3b.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s1_iface AF_huf_z4s1mk.

Notation amem := (word -> option byte).
Notation Zw z := (Z_to_bv 64 z) (only parsing).

Section CANSEC1. Context {rc : runConstT}.

Section M2.
  Variables (RNG : footprint) (Q : machine_state -> Prop) (gp tp : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (SP DST dcap seg DT tl mtl dl DBL DBH : Z) (cbs : list byte).
  Notation ZL pc mm r1 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29
             r30 r31 :=
    (MS (mkR r1 (Zw (SP + -384)) gp tp r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23
             r24 r25 r26 r27 r28 r29 r30 r31) FR (Zw pc) fc None mm (seg_rom bsegs)) (only parsing).
  Notation WM := [(SP + -384, SP + -104); (DST, DST + dcap)].
  Notation zctx := (z4L_ctx RNG SP DST dcap seg DT tl mtl dl DBL DBH cbs).
  Notation zmem := (z4L_mem SP DST dcap seg DT tl dl DBL DBH cbs).
  Notation zbnd := (z4L_bnd DST dcap).

  (* [comment removed for export] *)
  Definition m2s1_goal : Prop :=
    zctx ->
    forall mm (w0 w4 w5 w7 : word) (c1 c2 c3 c4 p1 p2 p3 p4 b1 b2 b3 b4 O1 O2 O3 O4 d1 d2 d3 d4 : Z)
           (jp1 jp2 jp3 jp4 : list byte) (s1 s2 s3 s4 e1 e2 e3 e4 : word)
           (l1 l2 l3 l4 x11 x13 x20 x27 x29 : word),
    zmem mm w0 w4 w5 w7 c1 c2 c3 c4 d1 d2 d3 d4 p1 p2 p3 p4 jp1 jp2 jp3 jp4 s1 s2 s3 s4 e1 e2 e3 e4 ->
    zbnd c1 c2 c3 c4 p1 p2 p3 p4 b1 b2 b3 b4 O1 O2 O3 O4 ->
    1 <= bv_unsigned l1 <= 2 -> 1 <= bv_unsigned l2 <= 2 -> 1 <= bv_unsigned l3 <= 2 -> 1 <= bv_unsigned l4 <= 2 ->
    b1 <= d1 <= b1 + 12 -> b2 <= d2 <= b2 + 12 -> b3 <= d3 <= b3 + 12 -> b4 <= d4 <= b4 + 12 ->
    (forall mm' (v0 v4 v5 v7 : word) (U1 f1 : Z) (l5 y11 y13 y20 y29 : word),
       munch WM mm mm' -> wmono bsegs mm mm' ->
       zmem mm' v0 v4 v5 v7 c1 c2 c3 c4 f1 d2 d3 d4 p1 p2 p3 p4 jp1 jp2 jp3 jp4 s1 s2 s3 s4 e1 e2 e3 e4 ->
       1 <= bv_unsigned l5 <= 2 -> O1 + 1 <= U1 <= O1 + 2 -> b1 <= f1 <= b1 + 24 ->
       evtF bsegs RNG Q (ZL 584640 mm' (Zw d2) (Zw (2^61)) (Zw (64 - tl)) (Zw (- DT - 5)) (Zw f1) (Zw O4) (Zw c1) y11
                           (Zw U1) y13 (Zw p1) (Zw p2) (Zw p3) (Zw c2) (Zw O3) (Zw O2) y20 (Zw AZ4_SB) l4 (Zw d3)
                           (Zw d4) l5 l2 x27 l3 y29 (Zw (DT + 4)) (Zw p4))) ->
    evtF bsegs RNG Q (ZL 584460 mm (Zw d2) (Zw (2^61)) (Zw (64 - tl)) (Zw (- DT - 5)) (Zw d1) (Zw O4) (Zw c1) x11
                        (Zw O1) x13 (Zw p1) (Zw p2) (Zw p3) (Zw c2) (Zw O3) (Zw O2) x20 (Zw AZ4_SB) l4 (Zw d3)
                        (Zw d4) l1 l2 x27 l3 x29 (Zw (DT + 4)) (Zw p4)).

  (* [comment removed for export] *)
  Definition m2s2_goal : Prop :=
    zctx ->
    forall mm (w0 w4 w5 w7 : word) (c1 c2 c3 c4 p1 p2 p3 p4 b1 b2 b3 b4 O1 O2 O3 O4 f1 d2 d3 d4 U1 : Z)
           (jp1 jp2 jp3 jp4 : list byte) (s1 s2 s3 s4 e1 e2 e3 e4 : word)
           (l2 l3 l4 l5 x11 x13 x20 x27 x29 : word),
    zmem mm w0 w4 w5 w7 c1 c2 c3 c4 f1 d2 d3 d4 p1 p2 p3 p4 jp1 jp2 jp3 jp4 s1 s2 s3 s4 e1 e2 e3 e4 ->
    zbnd c1 c2 c3 c4 p1 p2 p3 p4 b1 b2 b3 b4 O1 O2 O3 O4 ->
    1 <= bv_unsigned l2 <= 2 -> 1 <= bv_unsigned l3 <= 2 -> 1 <= bv_unsigned l4 <= 2 -> 1 <= bv_unsigned l5 <= 2 ->
    O1 + 1 <= U1 <= O1 + 2 -> b1 <= f1 <= b1 + 24 ->
    b2 <= d2 <= b2 + 12 -> b3 <= d3 <= b3 + 12 -> b4 <= d4 <= b4 + 12 ->
    (forall mm' (v0 v4 v5 v7 : word) (U2 f2 : Z) (l6 y13 y29 : word),
       munch WM mm mm' -> wmono bsegs mm mm' ->
       zmem mm' v0 v4 v5 v7 c1 c2 c3 c4 f1 f2 d3 d4 p1 p2 p3 p4 jp1 jp2 jp3 jp4 s1 s2 s3 s4 e1 e2 e3 e4 ->
       1 <= bv_unsigned l6 <= 2 -> O2 + 1 <= U2 <= O2 + 2 -> b2 <= f2 <= b2 + 24 ->
       evtF bsegs RNG Q (ZL 584824 mm' (Zw d2) (Zw (2^61)) (Zw (64 - tl)) (Zw (- DT - 5)) (Zw f1) (Zw O4) (Zw c1) (Zw c3)
                           (Zw U1) y13 (Zw p1) (Zw p2) (Zw p3) (Zw c2) (Zw O3) (Zw U2) (Zw f2) (Zw AZ4_SB) l4 (Zw d3)
                           (Zw d4) l5 l6 x27 l3 y29 (Zw (DT + 4)) (Zw p4))) ->
    evtF bsegs RNG Q (ZL 584640 mm (Zw d2) (Zw (2^61)) (Zw (64 - tl)) (Zw (- DT - 5)) (Zw f1) (Zw O4) (Zw c1) x11
                        (Zw U1) x13 (Zw p1) (Zw p2) (Zw p3) (Zw c2) (Zw O3) (Zw O2) x20 (Zw AZ4_SB) l4 (Zw d3)
                        (Zw d4) l5 l2 x27 l3 x29 (Zw (DT + 4)) (Zw p4)).

  (* [comment removed for export] *)
  Definition m2s3_goal : Prop :=
    zctx ->
    forall mm (w0 w4 w5 w7 : word) (c1 c2 c3 c4 p1 p2 p3 p4 b1 b2 b3 b4 O1 O2 O3 O4 f1 f2 d2 d3 d4 U1 U2 : Z)
           (jp1 jp2 jp3 jp4 : list byte) (s1 s2 s3 s4 e1 e2 e3 e4 : word)
           (l3 l4 l5 l6 x13 x27 x29 : word),
    zmem mm w0 w4 w5 w7 c1 c2 c3 c4 f1 f2 d3 d4 p1 p2 p3 p4 jp1 jp2 jp3 jp4 s1 s2 s3 s4 e1 e2 e3 e4 ->
    zbnd c1 c2 c3 c4 p1 p2 p3 p4 b1 b2 b3 b4 O1 O2 O3 O4 ->
    1 <= bv_unsigned l3 <= 2 -> 1 <= bv_unsigned l4 <= 2 -> 1 <= bv_unsigned l5 <= 2 -> 1 <= bv_unsigned l6 <= 2 ->
    O1 + 1 <= U1 <= O1 + 2 -> O2 + 1 <= U2 <= O2 + 2 -> b1 <= f1 <= b1 + 24 -> b2 <= f2 <= b2 + 24 ->
    b3 <= d3 <= b3 + 12 -> b4 <= d4 <= b4 + 12 ->
    (forall mm' (v0 v4 v5 v7 : word) (U3 f3 : Z) (l7 y13 y28 y29 : word),
       munch WM mm mm' -> wmono bsegs mm mm' ->
       zmem mm' v0 v4 v5 v7 c1 c2 c3 c4 f1 f2 f3 d4 p1 p2 p3 p4 jp1 jp2 jp3 jp4 s1 s2 s3 s4 e1 e2 e3 e4 ->
       1 <= bv_unsigned l7 <= 2 -> O3 + 1 <= U3 <= O3 + 2 -> b3 <= f3 <= b3 + 24 ->
       evtF bsegs RNG Q (ZL 585008 mm' (Zw d2) (Zw (2^61)) (Zw (64 - tl)) (Zw (- DT - 5)) (Zw f1) (Zw O4) (Zw c1) (Zw c4)
                           (Zw U1) y13 (Zw p1) (Zw p2) (Zw p3) (Zw c2) (Zw U3) (Zw U2) (Zw f2) (Zw AZ4_SB) l4 (Zw f3)
                           (Zw d4) l5 l6 l7 y28 y29 (Zw (DT + 4)) (Zw p4))) ->
    evtF bsegs RNG Q (ZL 584824 mm (Zw d2) (Zw (2^61)) (Zw (64 - tl)) (Zw (- DT - 5)) (Zw f1) (Zw O4) (Zw c1) (Zw c3)
                        (Zw U1) x13 (Zw p1) (Zw p2) (Zw p3) (Zw c2) (Zw O3) (Zw U2) (Zw f2) (Zw AZ4_SB) l4 (Zw d3)
                        (Zw d4) l5 l6 x27 l3 x29 (Zw (DT + 4)) (Zw p4)).

  (* [comment removed for export] *)
  Definition m2s4_goal : Prop :=
    zctx ->
    forall mm (w0 w4 w5 w7 : word) (c1 c2 c3 c4 p1 p2 p3 p4 b1 b2 b3 b4 O1 O2 O3 O4 f1 f2 f3 d2 d4 U1 U2 U3 : Z)
           (jp1 jp2 jp3 jp4 : list byte) (s1 s2 s3 s4 e1 e2 e3 e4 : word)
           (l4 l5 l6 l7 x13 x28 x29 : word),
    zmem mm w0 w4 w5 w7 c1 c2 c3 c4 f1 f2 f3 d4 p1 p2 p3 p4 jp1 jp2 jp3 jp4 s1 s2 s3 s4 e1 e2 e3 e4 ->
    zbnd c1 c2 c3 c4 p1 p2 p3 p4 b1 b2 b3 b4 O1 O2 O3 O4 ->
    1 <= bv_unsigned l4 <= 2 -> 1 <= bv_unsigned l5 <= 2 -> 1 <= bv_unsigned l6 <= 2 -> 1 <= bv_unsigned l7 <= 2 ->
    O1 + 1 <= U1 <= O1 + 2 -> O2 + 1 <= U2 <= O2 + 2 -> O3 + 1 <= U3 <= O3 + 2 ->
    b1 <= f1 <= b1 + 24 -> b2 <= f2 <= b2 + 24 -> b3 <= f3 <= b3 + 24 -> b4 <= d4 <= b4 + 12 ->
    (forall mm' (v0 v4 v5 v7 : word) (U4 f4 : Z) (l8 y11 y13 y28 y29 : word),
       munch WM mm mm' -> wmono bsegs mm mm' ->
       zmem mm' v0 v4 v5 v7 c1 c2 c3 c4 f1 f2 f3 f4 p1 p2 p3 p4 jp1 jp2 jp3 jp4 s1 s2 s3 s4 e1 e2 e3 e4 ->
       1 <= bv_unsigned l8 <= 2 -> O4 + 1 <= U4 <= O4 + 2 -> b4 <= f4 <= b4 + 24 ->
       evtF bsegs RNG Q (ZL 585188 mm' (Zw d2) (Zw (2^61)) (Zw (64 - tl)) (Zw (- DT - 5)) (Zw f1) (Zw U4) (Zw c1) y11
                           (Zw U1) y13 (Zw p1) (Zw p2) (Zw p3) (Zw c2) (Zw U3) (Zw U2) (Zw f2) (Zw AZ4_SB) l8 (Zw f3)
                           (Zw f4) l5 l6 l7 y28 y29 (Zw (DT + 4)) (Zw p4))) ->
    evtF bsegs RNG Q (ZL 585008 mm (Zw d2) (Zw (2^61)) (Zw (64 - tl)) (Zw (- DT - 5)) (Zw f1) (Zw O4) (Zw c1) (Zw c4)
                        (Zw U1) x13 (Zw p1) (Zw p2) (Zw p3) (Zw c2) (Zw U3) (Zw U2) (Zw f2) (Zw AZ4_SB) l4 (Zw f3)
                        (Zw d4) l5 l6 l7 x28 x29 (Zw (DT + 4)) (Zw p4)).
End M2.

Lemma m2s1 : forall RNG Q gp tp FR fc SP DST dcap seg DT tl mtl dl DBL DBH cbs,
  m2s1_goal RNG Q gp tp FR fc SP DST dcap seg DT tl mtl dl DBL DBH cbs.
Proof.
  intros RNG Q gp tp FR fc SP DST dcap seg DT tl mtl dl DBL DBH cbs CTX mm w0 w4 w5 w7 c1 c2 c3 c4 p1 p2 p3 p4
    b1 b2 b3 b4 O1 O2 O3 O4 d1 d2 d3 d4 jp1 jp2 jp3 jp4 s1 s2 s3 s4 e1 e2 e3 e4 l1 l2 l3 l4 x11 x13 x20 x27 x29
    MEM BND HL1 HL2 HL3 HL4 HD1 HD2 HD3 HD4 K.
  destruct CTX as (RS & TBL & UT1 & UT2 & UTS & UA8 & UB1 & UB2 & UDS & UDA & RT & RD & RI & A1 & A0 & A2 & A3 & A4 & A5
    & J1 & J2 & J3 & J4 & DTA & H1 & H2 & H3 & H4 & H5 & H6 & AT1 & AT2 & AS3 & AS1 & AS2 & DBA).
  destruct MEM as (C0 & C1 & C2 & C3 & CA & C8c & CB & C11 & C12 & CC & BD4 & BD3 & BD2 & BD1 & MI & TAB & TB
    & (obuf & OB & OBL) & UT & UD).
  destruct BND as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & B1 & B2 & B3 & B4 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  unfold AZ4_SB in *.
  assert (AIL : 4096 <= AIMG_LO /\ AIMG_LO <= AIMG_HI /\ AIMG_HI <= 2^47) by (unfold AIMG_LO, AIMG_HI; lia).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  assert (ZT : disjoint_from [(SP + -384, SP + -104); (DST, DST + dcap)] (DT + 4) (4 * 2^tl))
    by (cbn [disjoint_from]; unfold KXGoM.apart in *; lia).
  assert (SD1 : disjoint_from [(SP + -384, SP + -104); (DST, DST + dcap)] (shad DBL) (shad (DBH - 1) + 1 - shad DBL))
    by (eapply z4m_shd_dj; [exact AS3 | lia | lia | exact AS1 | lia | lia | lia | lia | lia]).
  assert (SD2 : disjoint_from [(SP + -384, SP + -104); (DST, DST + dcap)] (shad DST) (shad (DST + dcap - 1) + 1 - shad DST))
    by (eapply z4m_shd_dj; [exact AS3 | lia | lia | exact AS1 | lia | lia | lia | lia | lia]).
  pose proof (proj2 BD1) as WB1. pose proof (proj2 BD2) as WB2. pose proof (proj2 BD3) as WB3. pose proof (proj2 BD4) as WB4.
  cbn [cells_size csize BD4A] in WB1, WB2, WB3, WB4. pose proof (proj2 OB) as WOB.
  kx_runFLd [584640] 2000%nat (repeat true 4096)
      [KZRange SP 8192 (2^47); KZRange DST 4096 (2^47); KZRange seg 0 (2^32); KZRange dcap 6 (2^32);
       KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange (64 - tl) 52 63; KZRange mtl 1 12; KZRange dl 0 4096; KZRange (2^tl) 2 4096;
       KZRange c1 0 (2^64 - 1); KZRange c2 0 (2^64 - 1); KZRange c3 0 (2^64 - 1); KZRange c4 0 (2^64 - 1);
       KZRange p1 0 (2^64 - 1); KZRange p2 0 (2^64 - 1); KZRange p3 0 (2^64 - 1); KZRange p4 0 (2^64 - 1);
       KZRange b1 0 64; KZRange b2 0 64; KZRange b3 0 64; KZRange b4 0 64;
       KZRange d1 0 76; KZRange d2 0 76; KZRange d3 0 76; KZRange d4 0 76;
       KZRange (bv_unsigned l1) 1 2; KZRange (bv_unsigned l2) 1 2; KZRange (bv_unsigned l3) 1 2; KZRange (bv_unsigned l4) 1 2;
       KZRange (DT + 4) 4096 (2^47); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47); KZAlign (DT + 4) 4;
       KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]; KZIdx tl (2^tl);
       KZWord (SP + -376) 8 (DST + 3 * seg); KZWord (SP + -368) 8 dl; KZWord (SP + -360) 8 (DST + dcap - 7);
       KZWord (SP + -320) 8 c2; KZWord (SP + -296) 8 c4; KZWord (SP + -288) 8 c3;
       KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -312) 8 (DST + seg); KZWord (SP + -304) 8 (DST + 2 * seg);
       KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
       KZWord (SP + -144) 8 c1; KZWord (SP + -184) 8 c2; KZWord (SP + -224) 8 c3; KZWord (SP + -264) 8 c4;
       KZWord (SP + -128) 8 p1; KZWord (SP + -168) 8 p2; KZWord (SP + -208) 8 p3; KZWord (SP + -248) 8 p4;
       KZRange O1 4096 (2^47 - 8); KZWr O1 8; KZDisj O1 8 (DT + 4) (4 * 2^tl); KZDisj O1 8 (SP + -384) 384; KZDisj O1 8 AIMG_LO (AIMG_HI - AIMG_LO);
       KZRange O2 4096 (2^47 - 8); KZWr O2 8; KZDisj O2 8 (DT + 4) (4 * 2^tl); KZDisj O2 8 (SP + -384) 384; KZDisj O2 8 AIMG_LO (AIMG_HI - AIMG_LO);
       KZRange O3 4096 (2^47 - 8); KZWr O3 8; KZDisj O3 8 (DT + 4) (4 * 2^tl); KZDisj O3 8 (SP + -384) 384; KZDisj O3 8 AIMG_LO (AIMG_HI - AIMG_LO);
       KZRange O4 4096 (2^47 - 8); KZWr O4 8; KZDisj O4 8 (DT + 4) (4 * 2^tl); KZDisj O4 8 (SP + -384) 384; KZDisj O4 8 AIMG_LO (AIMG_HI - AIMG_LO)]
      [(DT + 4, 4 * 2^tl)]
      [(DT + 4, 4 * 2^tl); (SP + -384, 280); (O1, 8); (O2, 8); (O3, 8); (O4, 8)]
      [(DT + 4, 4 * 2^tl); (O1, 8); (O2, 8); (O3, 8); (O4, 8)].
  all: try (z4m_flat tl AS3 AS1 J2 J3).
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => z4m_br tl end).
  all: try (lazymatch goal with |- store_ok _ _ _ _ = _ => z4m_stok4 end).
  pose proof J1 as J1u. pose proof J2 as J2u. pose proof J3 as J3u. unfold KXGoM.apart in J1u, J2u, J3u.
  pose proof (munch_refl [(SP + -384, SP + -104); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  kx_munch_wins MUW [(SP + -384, 280); (O1, 8); (O2, 8); (O3, 8); (O4, 8)].
  lazymatch goal with HLF : log_flat ?E ?l |- context [mem_denot ?E ?m ?l] =>
    assert (MIl : mem_inv bsegs (mem_denot E m l)) by
      (apply (kx_mem_inv_log bsegs E m l MI HLF); cbn [log_wr]; repeat (first [exact I | split]);
       first [z4m_wrc tl WB4 ltac:(idtac; clear - A5 A1 A2 G1 G2 G3 G4 G5 G6 G7 G8 OBL HL1 HL2 HL3 HL4; lia) | z4m_wrc tl WB3 ltac:(idtac; clear - A5 A1 A2 G1 G2 G3 G4 G5 G6 G7 G8 OBL HL1 HL2 HL3 HL4; lia) | z4m_wrc tl WB2 ltac:(idtac; clear - A5 A1 A2 G1 G2 G3 G4 G5 G6 G7 G8 OBL HL1 HL2 HL3 HL4; lia) | z4m_wrc tl WB1 ltac:(idtac; clear - A5 A1 A2 G1 G2 G3 G4 G5 G6 G7 G8 OBL HL1 HL2 HL3 HL4; lia) | z4m_wrc tl WOB ltac:(idtac; clear - A5 A1 A2 G1 G2 G3 G4 G5 G6 G7 G8 OBL HL1 HL2 HL3 HL4; lia)]) end.

  kx_post_mem_free.
  lazymatch goal with HL : log_flat ?E ?l |- context [mem_denot ?E ?m ?l] =>
    pose proof (kx_u8arr_replay bsegs E m l DST obuf OB HL) as OB';
    pose proof (replay_length E l DST obuf) as OL' end.
  z4m_frame TB ltac:(idtac; clear - A5 A1 A2 A3 A4 J2u J3u G1 G2 G3 G4 G5 G6 G7 G8 TBL HL1 HL2 HL3 HL4; lia).
  z4m_frame C0 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame C1 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame C2 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame C3 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame CA ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame C8c ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame CB ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame C11 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame C12 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame CC ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  unfold BD4A in BD4, BD3, BD2, BD1.
  apply (kx_rwc_cons bsegs) in BD4; destruct BD4 as [BD4c BD4]; cbn [csize] in BD4; kx_rwc_norm BD4;
    apply (kx_rwc_cons bsegs) in BD4; destruct BD4 as [BD4b BD4]; cbn [csize] in BD4; kx_rwc_norm BD4.
  apply (kx_rwc_cons bsegs) in BD3; destruct BD3 as [BD3c BD3]; cbn [csize] in BD3; kx_rwc_norm BD3;
    apply (kx_rwc_cons bsegs) in BD3; destruct BD3 as [BD3b BD3]; cbn [csize] in BD3; kx_rwc_norm BD3.
  apply (kx_rwc_cons bsegs) in BD2; destruct BD2 as [BD2c BD2]; cbn [csize] in BD2; kx_rwc_norm BD2;
    apply (kx_rwc_cons bsegs) in BD2; destruct BD2 as [BD2b BD2]; cbn [csize] in BD2; kx_rwc_norm BD2.
  apply (kx_rwc_cons bsegs) in BD1; destruct BD1 as [BD1c BD1]; cbn [csize] in BD1; kx_rwc_norm BD1;
    apply (kx_rwc_cons bsegs) in BD1; destruct BD1 as [BD1b BD1]; cbn [csize] in BD1; kx_rwc_norm BD1.
  z4m_frame BD4c ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD3c ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD2c ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD1c ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD4 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD3 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD2 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD1 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD4b ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD3b ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD2b ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  kx_cell4w BD1b.
  lazymatch goal with |- context [mem_denot ?E _ _] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      repeat match goal with H : rw_cells _ _ _ [C4 (edenot E ?v)] |- _ => rewrite (ez_ok zv E (kE_atoms zv xs) v) in H end
    end
  end.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?m ?l) _) =>
    eapply evtF_eq; [| eapply (K (mem_denot E m l))] end.
  1: z4m_regs.
  all: try exact MUW.
  all: try exact WMr.
  all: try (progress unfold z4L_mem; repeat match goal with |- _ /\ _ => split end).
  all: try (lazymatch goal with |- rw_cells _ _ _ (BD4A _ _ _ _ _ _) => unfold BD4A; kx_cells_merge end).
  all: try (lazymatch goal with |- rw_cells _ _ _ _ => eassumption end).
  all: try (lazymatch goal with |- mem_inv _ _ => exact MIl end).
  all: try (lazymatch goal with |- mem_inv _ _ => eassumption end).
  all: try (lazymatch goal with |- bytes_at _ _ _ _ => eassumption end).
  all: try (lazymatch goal with |- KXTac.ztab_fact _ _ _ _ _ _ => eapply w4_ztab_munch; [exact TAB | exact MUW | exact ZT | lia | lia] end).
  all: try (lazymatch goal with |- ex _ => eexists; split; [exact OB' | rewrite OL'; exact OBL] end).
  all: try (lazymatch goal with |- unpoisoned _ _ _ =>
              first [ eapply unpoisoned_munch; [exact UT | exact MUW | exact SD1]
                    | eapply unpoisoned_munch; [exact UD | exact MUW | exact SD2] ] end).
  all: try (lazymatch goal with |- _ <= _ <= _ => z4m_rng end).
Qed.

Lemma m2s2 : forall RNG Q gp tp FR fc SP DST dcap seg DT tl mtl dl DBL DBH cbs,
  m2s2_goal RNG Q gp tp FR fc SP DST dcap seg DT tl mtl dl DBL DBH cbs.
Proof.
  intros RNG Q gp tp FR fc SP DST dcap seg DT tl mtl dl DBL DBH cbs CTX mm w0 w4 w5 w7 c1 c2 c3 c4 p1 p2 p3 p4
    b1 b2 b3 b4 O1 O2 O3 O4 f1 d2 d3 d4 U1 jp1 jp2 jp3 jp4 s1 s2 s3 s4 e1 e2 e3 e4 l2 l3 l4 l5 x11 x13 x20 x27 x29
    MEM BND HL1 HL2 HL3 HL4 HU1 HF1 HD2 HD3 HD4 K.
  destruct CTX as (RS & TBL & UT1 & UT2 & UTS & UA8 & UB1 & UB2 & UDS & UDA & RT & RD & RI & A1 & A0 & A2 & A3 & A4 & A5
    & J1 & J2 & J3 & J4 & DTA & H1 & H2 & H3 & H4 & H5 & H6 & AT1 & AT2 & AS3 & AS1 & AS2 & DBA).
  destruct MEM as (C0 & C1 & C2 & C3 & CA & C8c & CB & C11 & C12 & CC & BD4 & BD3 & BD2 & BD1 & MI & TAB & TB
    & (obuf & OB & OBL) & UT & UD).
  destruct BND as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & B1 & B2 & B3 & B4 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  unfold AZ4_SB in *.
  assert (AIL : 4096 <= AIMG_LO /\ AIMG_LO <= AIMG_HI /\ AIMG_HI <= 2^47) by (unfold AIMG_LO, AIMG_HI; lia).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  assert (ZT : disjoint_from [(SP + -384, SP + -104); (DST, DST + dcap)] (DT + 4) (4 * 2^tl))
    by (cbn [disjoint_from]; unfold KXGoM.apart in *; lia).
  assert (SD1 : disjoint_from [(SP + -384, SP + -104); (DST, DST + dcap)] (shad DBL) (shad (DBH - 1) + 1 - shad DBL))
    by (eapply z4m_shd_dj; [exact AS3 | lia | lia | exact AS1 | lia | lia | lia | lia | lia]).
  assert (SD2 : disjoint_from [(SP + -384, SP + -104); (DST, DST + dcap)] (shad DST) (shad (DST + dcap - 1) + 1 - shad DST))
    by (eapply z4m_shd_dj; [exact AS3 | lia | lia | exact AS1 | lia | lia | lia | lia | lia]).
  pose proof (proj2 BD1) as WB1. pose proof (proj2 BD2) as WB2. pose proof (proj2 BD3) as WB3. pose proof (proj2 BD4) as WB4.
  cbn [cells_size csize BD4A] in WB1, WB2, WB3, WB4. pose proof (proj2 OB) as WOB.
  kx_runFLd [584824] 2000%nat (repeat true 4096)
      [KZRange SP 8192 (2^47); KZRange DST 4096 (2^47); KZRange seg 0 (2^32); KZRange dcap 6 (2^32);
       KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange (64 - tl) 52 63; KZRange mtl 1 12; KZRange dl 0 4096; KZRange (2^tl) 2 4096;
       KZRange c1 0 (2^64 - 1); KZRange c2 0 (2^64 - 1); KZRange c3 0 (2^64 - 1); KZRange c4 0 (2^64 - 1);
       KZRange p1 0 (2^64 - 1); KZRange p2 0 (2^64 - 1); KZRange p3 0 (2^64 - 1); KZRange p4 0 (2^64 - 1);
       KZRange b1 0 64; KZRange b2 0 64; KZRange b3 0 64; KZRange b4 0 64;
       KZRange f1 0 88; KZRange d2 0 76; KZRange d3 0 76; KZRange d4 0 76; KZRange U1 4096 (2^47);
       KZRange (bv_unsigned l2) 1 2; KZRange (bv_unsigned l3) 1 2; KZRange (bv_unsigned l4) 1 2; KZRange (bv_unsigned l5) 1 2;
       KZRange (DT + 4) 4096 (2^47); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47); KZAlign (DT + 4) 4;
       KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]; KZIdx tl (2^tl);
       KZWord (SP + -376) 8 (DST + 3 * seg); KZWord (SP + -368) 8 dl; KZWord (SP + -360) 8 (DST + dcap - 7);
       KZWord (SP + -320) 8 c2; KZWord (SP + -296) 8 c4; KZWord (SP + -288) 8 c3;
       KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -312) 8 (DST + seg); KZWord (SP + -304) 8 (DST + 2 * seg);
       KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
       KZWord (SP + -144) 8 c1; KZWord (SP + -184) 8 c2; KZWord (SP + -224) 8 c3; KZWord (SP + -264) 8 c4;
       KZWord (SP + -128) 8 p1; KZWord (SP + -168) 8 p2; KZWord (SP + -208) 8 p3; KZWord (SP + -248) 8 p4;
       KZRange O1 4096 (2^47 - 8); KZWr O1 8; KZDisj O1 8 (DT + 4) (4 * 2^tl); KZDisj O1 8 (SP + -384) 384; KZDisj O1 8 AIMG_LO (AIMG_HI - AIMG_LO);
       KZRange O2 4096 (2^47 - 8); KZWr O2 8; KZDisj O2 8 (DT + 4) (4 * 2^tl); KZDisj O2 8 (SP + -384) 384; KZDisj O2 8 AIMG_LO (AIMG_HI - AIMG_LO);
       KZRange O3 4096 (2^47 - 8); KZWr O3 8; KZDisj O3 8 (DT + 4) (4 * 2^tl); KZDisj O3 8 (SP + -384) 384; KZDisj O3 8 AIMG_LO (AIMG_HI - AIMG_LO);
       KZRange O4 4096 (2^47 - 8); KZWr O4 8; KZDisj O4 8 (DT + 4) (4 * 2^tl); KZDisj O4 8 (SP + -384) 384; KZDisj O4 8 AIMG_LO (AIMG_HI - AIMG_LO)]
      [(DT + 4, 4 * 2^tl)]
      [(DT + 4, 4 * 2^tl); (SP + -384, 280); (O1, 8); (O2, 8); (O3, 8); (O4, 8)]
      [(DT + 4, 4 * 2^tl); (O1, 8); (O2, 8); (O3, 8); (O4, 8)].
  all: try (z4m_flat tl AS3 AS1 J2 J3).
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => z4m_br tl end).
  all: try (lazymatch goal with |- store_ok _ _ _ _ = _ => z4m_stok4 end).
  pose proof J1 as J1u. pose proof J2 as J2u. pose proof J3 as J3u. unfold KXGoM.apart in J1u, J2u, J3u.
  pose proof (munch_refl [(SP + -384, SP + -104); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  kx_munch_wins MUW [(SP + -384, 280); (O1, 8); (O2, 8); (O3, 8); (O4, 8)].
  lazymatch goal with HLF : log_flat ?E ?l |- context [mem_denot ?E ?m ?l] =>
    assert (MIl : mem_inv bsegs (mem_denot E m l)) by
      (apply (kx_mem_inv_log bsegs E m l MI HLF); cbn [log_wr]; repeat (first [exact I | split]);
       first [z4m_wrc tl WB4 ltac:(idtac; clear - A5 A1 A2 G1 G2 G3 G4 G5 G6 G7 G8 OBL HL1 HL2 HL3 HL4; lia) | z4m_wrc tl WB3 ltac:(idtac; clear - A5 A1 A2 G1 G2 G3 G4 G5 G6 G7 G8 OBL HL1 HL2 HL3 HL4; lia) | z4m_wrc tl WB2 ltac:(idtac; clear - A5 A1 A2 G1 G2 G3 G4 G5 G6 G7 G8 OBL HL1 HL2 HL3 HL4; lia) | z4m_wrc tl WB1 ltac:(idtac; clear - A5 A1 A2 G1 G2 G3 G4 G5 G6 G7 G8 OBL HL1 HL2 HL3 HL4; lia) | z4m_wrc tl WOB ltac:(idtac; clear - A5 A1 A2 G1 G2 G3 G4 G5 G6 G7 G8 OBL HL1 HL2 HL3 HL4; lia)]) end.

  kx_post_mem_free.
  lazymatch goal with HL : log_flat ?E ?l |- context [mem_denot ?E ?m ?l] =>
    pose proof (kx_u8arr_replay bsegs E m l DST obuf OB HL) as OB';
    pose proof (replay_length E l DST obuf) as OL' end.
  z4m_frame TB ltac:(idtac; clear - A5 A1 A2 A3 A4 J2u J3u G1 G2 G3 G4 G5 G6 G7 G8 TBL HL1 HL2 HL3 HL4; lia).
  z4m_frame C0 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame C1 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame C2 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame C3 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame CA ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame C8c ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame CB ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame C11 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame C12 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame CC ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  unfold BD4A in BD4, BD3, BD2, BD1.
  apply (kx_rwc_cons bsegs) in BD4; destruct BD4 as [BD4c BD4]; cbn [csize] in BD4; kx_rwc_norm BD4;
    apply (kx_rwc_cons bsegs) in BD4; destruct BD4 as [BD4b BD4]; cbn [csize] in BD4; kx_rwc_norm BD4.
  apply (kx_rwc_cons bsegs) in BD3; destruct BD3 as [BD3c BD3]; cbn [csize] in BD3; kx_rwc_norm BD3;
    apply (kx_rwc_cons bsegs) in BD3; destruct BD3 as [BD3b BD3]; cbn [csize] in BD3; kx_rwc_norm BD3.
  apply (kx_rwc_cons bsegs) in BD2; destruct BD2 as [BD2c BD2]; cbn [csize] in BD2; kx_rwc_norm BD2;
    apply (kx_rwc_cons bsegs) in BD2; destruct BD2 as [BD2b BD2]; cbn [csize] in BD2; kx_rwc_norm BD2.
  apply (kx_rwc_cons bsegs) in BD1; destruct BD1 as [BD1c BD1]; cbn [csize] in BD1; kx_rwc_norm BD1;
    apply (kx_rwc_cons bsegs) in BD1; destruct BD1 as [BD1b BD1]; cbn [csize] in BD1; kx_rwc_norm BD1.
  z4m_frame BD4c ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD3c ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD2c ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD1c ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD4 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD3 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD2 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD1 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD4b ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD3b ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  kx_cell4w BD2b.
  z4m_frame BD1b ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  lazymatch goal with |- context [mem_denot ?E _ _] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      repeat match goal with H : rw_cells _ _ _ [C4 (edenot E ?v)] |- _ => rewrite (ez_ok zv E (kE_atoms zv xs) v) in H end
    end
  end.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?m ?l) _) =>
    eapply evtF_eq; [| eapply (K (mem_denot E m l))] end.
  1: z4m_regs.
  all: try exact MUW.
  all: try exact WMr.
  all: try (progress unfold z4L_mem; repeat match goal with |- _ /\ _ => split end).
  all: try (lazymatch goal with |- rw_cells _ _ _ (BD4A _ _ _ _ _ _) => unfold BD4A; kx_cells_merge end).
  all: try (lazymatch goal with |- rw_cells _ _ _ _ => eassumption end).
  all: try (lazymatch goal with |- mem_inv _ _ => exact MIl end).
  all: try (lazymatch goal with |- mem_inv _ _ => eassumption end).
  all: try (lazymatch goal with |- bytes_at _ _ _ _ => eassumption end).
  all: try (lazymatch goal with |- KXTac.ztab_fact _ _ _ _ _ _ => eapply w4_ztab_munch; [exact TAB | exact MUW | exact ZT | lia | lia] end).
  all: try (lazymatch goal with |- ex _ => eexists; split; [exact OB' | rewrite OL'; exact OBL] end).
  all: try (lazymatch goal with |- unpoisoned _ _ _ =>
              first [ eapply unpoisoned_munch; [exact UT | exact MUW | exact SD1]
                    | eapply unpoisoned_munch; [exact UD | exact MUW | exact SD2] ] end).
  all: try (lazymatch goal with |- _ <= _ <= _ => z4m_rng end).
Qed.

Lemma m2s3 : forall RNG Q gp tp FR fc SP DST dcap seg DT tl mtl dl DBL DBH cbs,
  m2s3_goal RNG Q gp tp FR fc SP DST dcap seg DT tl mtl dl DBL DBH cbs.
Proof.
  intros RNG Q gp tp FR fc SP DST dcap seg DT tl mtl dl DBL DBH cbs CTX mm w0 w4 w5 w7 c1 c2 c3 c4 p1 p2 p3 p4
    b1 b2 b3 b4 O1 O2 O3 O4 f1 f2 d2 d3 d4 U1 U2 jp1 jp2 jp3 jp4 s1 s2 s3 s4 e1 e2 e3 e4 l3 l4 l5 l6 x13 x27 x29
    MEM BND HL1 HL2 HL3 HL4 HU1 HU2 HF1 HF2 HD3 HD4 K.
  destruct CTX as (RS & TBL & UT1 & UT2 & UTS & UA8 & UB1 & UB2 & UDS & UDA & RT & RD & RI & A1 & A0 & A2 & A3 & A4 & A5
    & J1 & J2 & J3 & J4 & DTA & H1 & H2 & H3 & H4 & H5 & H6 & AT1 & AT2 & AS3 & AS1 & AS2 & DBA).
  destruct MEM as (C0 & C1 & C2 & C3 & CA & C8c & CB & C11 & C12 & CC & BD4 & BD3 & BD2 & BD1 & MI & TAB & TB
    & (obuf & OB & OBL) & UT & UD).
  destruct BND as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & B1 & B2 & B3 & B4 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  unfold AZ4_SB in *.
  assert (AIL : 4096 <= AIMG_LO /\ AIMG_LO <= AIMG_HI /\ AIMG_HI <= 2^47) by (unfold AIMG_LO, AIMG_HI; lia).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  assert (ZT : disjoint_from [(SP + -384, SP + -104); (DST, DST + dcap)] (DT + 4) (4 * 2^tl))
    by (cbn [disjoint_from]; unfold KXGoM.apart in *; lia).
  assert (SD1 : disjoint_from [(SP + -384, SP + -104); (DST, DST + dcap)] (shad DBL) (shad (DBH - 1) + 1 - shad DBL))
    by (eapply z4m_shd_dj; [exact AS3 | lia | lia | exact AS1 | lia | lia | lia | lia | lia]).
  assert (SD2 : disjoint_from [(SP + -384, SP + -104); (DST, DST + dcap)] (shad DST) (shad (DST + dcap - 1) + 1 - shad DST))
    by (eapply z4m_shd_dj; [exact AS3 | lia | lia | exact AS1 | lia | lia | lia | lia | lia]).
  pose proof (proj2 BD1) as WB1. pose proof (proj2 BD2) as WB2. pose proof (proj2 BD3) as WB3. pose proof (proj2 BD4) as WB4.
  cbn [cells_size csize BD4A] in WB1, WB2, WB3, WB4. pose proof (proj2 OB) as WOB.
  kx_runFLd [585008] 2000%nat (repeat true 4096)
      [KZRange SP 8192 (2^47); KZRange DST 4096 (2^47); KZRange seg 0 (2^32); KZRange dcap 6 (2^32);
       KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange (64 - tl) 52 63; KZRange mtl 1 12; KZRange dl 0 4096; KZRange (2^tl) 2 4096;
       KZRange c1 0 (2^64 - 1); KZRange c2 0 (2^64 - 1); KZRange c3 0 (2^64 - 1); KZRange c4 0 (2^64 - 1);
       KZRange p1 0 (2^64 - 1); KZRange p2 0 (2^64 - 1); KZRange p3 0 (2^64 - 1); KZRange p4 0 (2^64 - 1);
       KZRange b1 0 64; KZRange b2 0 64; KZRange b3 0 64; KZRange b4 0 64;
       KZRange f1 0 88; KZRange f2 0 88; KZRange d3 0 76; KZRange d4 0 76; KZRange U1 4096 (2^47); KZRange U2 4096 (2^47);
       KZRange (bv_unsigned l3) 1 2; KZRange (bv_unsigned l4) 1 2; KZRange (bv_unsigned l5) 1 2; KZRange (bv_unsigned l6) 1 2;
       KZRange (DT + 4) 4096 (2^47); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47); KZAlign (DT + 4) 4;
       KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]; KZIdx tl (2^tl);
       KZWord (SP + -376) 8 (DST + 3 * seg); KZWord (SP + -368) 8 dl; KZWord (SP + -360) 8 (DST + dcap - 7);
       KZWord (SP + -320) 8 c2; KZWord (SP + -296) 8 c4; KZWord (SP + -288) 8 c3;
       KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -312) 8 (DST + seg); KZWord (SP + -304) 8 (DST + 2 * seg);
       KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
       KZWord (SP + -144) 8 c1; KZWord (SP + -184) 8 c2; KZWord (SP + -224) 8 c3; KZWord (SP + -264) 8 c4;
       KZWord (SP + -128) 8 p1; KZWord (SP + -168) 8 p2; KZWord (SP + -208) 8 p3; KZWord (SP + -248) 8 p4;
       KZRange O1 4096 (2^47 - 8); KZWr O1 8; KZDisj O1 8 (DT + 4) (4 * 2^tl); KZDisj O1 8 (SP + -384) 384; KZDisj O1 8 AIMG_LO (AIMG_HI - AIMG_LO);
       KZRange O2 4096 (2^47 - 8); KZWr O2 8; KZDisj O2 8 (DT + 4) (4 * 2^tl); KZDisj O2 8 (SP + -384) 384; KZDisj O2 8 AIMG_LO (AIMG_HI - AIMG_LO);
       KZRange O3 4096 (2^47 - 8); KZWr O3 8; KZDisj O3 8 (DT + 4) (4 * 2^tl); KZDisj O3 8 (SP + -384) 384; KZDisj O3 8 AIMG_LO (AIMG_HI - AIMG_LO);
       KZRange O4 4096 (2^47 - 8); KZWr O4 8; KZDisj O4 8 (DT + 4) (4 * 2^tl); KZDisj O4 8 (SP + -384) 384; KZDisj O4 8 AIMG_LO (AIMG_HI - AIMG_LO)]
      [(DT + 4, 4 * 2^tl)]
      [(DT + 4, 4 * 2^tl); (SP + -384, 280); (O1, 8); (O2, 8); (O3, 8); (O4, 8)]
      [(DT + 4, 4 * 2^tl); (O1, 8); (O2, 8); (O3, 8); (O4, 8)].
  all: try (z4m_flat tl AS3 AS1 J2 J3).
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => z4m_br tl end).
  all: try (lazymatch goal with |- store_ok _ _ _ _ = _ => z4m_stok4 end).
  pose proof J1 as J1u. pose proof J2 as J2u. pose proof J3 as J3u. unfold KXGoM.apart in J1u, J2u, J3u.
  pose proof (munch_refl [(SP + -384, SP + -104); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  kx_munch_wins MUW [(SP + -384, 280); (O1, 8); (O2, 8); (O3, 8); (O4, 8)].
  lazymatch goal with HLF : log_flat ?E ?l |- context [mem_denot ?E ?m ?l] =>
    assert (MIl : mem_inv bsegs (mem_denot E m l)) by
      (apply (kx_mem_inv_log bsegs E m l MI HLF); cbn [log_wr]; repeat (first [exact I | split]);
       first [z4m_wrc tl WB4 ltac:(idtac; clear - A5 A1 A2 G1 G2 G3 G4 G5 G6 G7 G8 OBL HL1 HL2 HL3 HL4; lia) | z4m_wrc tl WB3 ltac:(idtac; clear - A5 A1 A2 G1 G2 G3 G4 G5 G6 G7 G8 OBL HL1 HL2 HL3 HL4; lia) | z4m_wrc tl WB2 ltac:(idtac; clear - A5 A1 A2 G1 G2 G3 G4 G5 G6 G7 G8 OBL HL1 HL2 HL3 HL4; lia) | z4m_wrc tl WB1 ltac:(idtac; clear - A5 A1 A2 G1 G2 G3 G4 G5 G6 G7 G8 OBL HL1 HL2 HL3 HL4; lia) | z4m_wrc tl WOB ltac:(idtac; clear - A5 A1 A2 G1 G2 G3 G4 G5 G6 G7 G8 OBL HL1 HL2 HL3 HL4; lia)]) end.

  kx_post_mem_free.
  lazymatch goal with HL : log_flat ?E ?l |- context [mem_denot ?E ?m ?l] =>
    pose proof (kx_u8arr_replay bsegs E m l DST obuf OB HL) as OB';
    pose proof (replay_length E l DST obuf) as OL' end.
  z4m_frame TB ltac:(idtac; clear - A5 A1 A2 A3 A4 J2u J3u G1 G2 G3 G4 G5 G6 G7 G8 TBL HL1 HL2 HL3 HL4; lia).
  z4m_frame C0 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame C1 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame C2 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame C3 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame CA ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame C8c ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame CB ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame C11 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame C12 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame CC ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  unfold BD4A in BD4, BD3, BD2, BD1.
  apply (kx_rwc_cons bsegs) in BD4; destruct BD4 as [BD4c BD4]; cbn [csize] in BD4; kx_rwc_norm BD4;
    apply (kx_rwc_cons bsegs) in BD4; destruct BD4 as [BD4b BD4]; cbn [csize] in BD4; kx_rwc_norm BD4.
  apply (kx_rwc_cons bsegs) in BD3; destruct BD3 as [BD3c BD3]; cbn [csize] in BD3; kx_rwc_norm BD3;
    apply (kx_rwc_cons bsegs) in BD3; destruct BD3 as [BD3b BD3]; cbn [csize] in BD3; kx_rwc_norm BD3.
  apply (kx_rwc_cons bsegs) in BD2; destruct BD2 as [BD2c BD2]; cbn [csize] in BD2; kx_rwc_norm BD2;
    apply (kx_rwc_cons bsegs) in BD2; destruct BD2 as [BD2b BD2]; cbn [csize] in BD2; kx_rwc_norm BD2.
  apply (kx_rwc_cons bsegs) in BD1; destruct BD1 as [BD1c BD1]; cbn [csize] in BD1; kx_rwc_norm BD1;
    apply (kx_rwc_cons bsegs) in BD1; destruct BD1 as [BD1b BD1]; cbn [csize] in BD1; kx_rwc_norm BD1.
  z4m_frame BD4c ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD3c ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD2c ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD1c ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD4 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD3 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD2 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD1 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD4b ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  kx_cell4w BD3b.
  z4m_frame BD2b ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD1b ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  lazymatch goal with |- context [mem_denot ?E _ _] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      repeat match goal with H : rw_cells _ _ _ [C4 (edenot E ?v)] |- _ => rewrite (ez_ok zv E (kE_atoms zv xs) v) in H end
    end
  end.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?m ?l) _) =>
    eapply evtF_eq; [| eapply (K (mem_denot E m l))] end.
  1: z4m_regs.
  all: try exact MUW.
  all: try exact WMr.
  all: try (progress unfold z4L_mem; repeat match goal with |- _ /\ _ => split end).
  all: try (lazymatch goal with |- rw_cells _ _ _ (BD4A _ _ _ _ _ _) => unfold BD4A; kx_cells_merge end).
  all: try (lazymatch goal with |- rw_cells _ _ _ _ => eassumption end).
  all: try (lazymatch goal with |- mem_inv _ _ => exact MIl end).
  all: try (lazymatch goal with |- mem_inv _ _ => eassumption end).
  all: try (lazymatch goal with |- bytes_at _ _ _ _ => eassumption end).
  all: try (lazymatch goal with |- KXTac.ztab_fact _ _ _ _ _ _ => eapply w4_ztab_munch; [exact TAB | exact MUW | exact ZT | lia | lia] end).
  all: try (lazymatch goal with |- ex _ => eexists; split; [exact OB' | rewrite OL'; exact OBL] end).
  all: try (lazymatch goal with |- unpoisoned _ _ _ =>
              first [ eapply unpoisoned_munch; [exact UT | exact MUW | exact SD1]
                    | eapply unpoisoned_munch; [exact UD | exact MUW | exact SD2] ] end).
  all: try (lazymatch goal with |- _ <= _ <= _ => z4m_rng end).
Qed.

Lemma m2s4 : forall RNG Q gp tp FR fc SP DST dcap seg DT tl mtl dl DBL DBH cbs,
  m2s4_goal RNG Q gp tp FR fc SP DST dcap seg DT tl mtl dl DBL DBH cbs.
Proof.
  intros RNG Q gp tp FR fc SP DST dcap seg DT tl mtl dl DBL DBH cbs CTX mm w0 w4 w5 w7 c1 c2 c3 c4 p1 p2 p3 p4
    b1 b2 b3 b4 O1 O2 O3 O4 f1 f2 f3 d2 d4 U1 U2 U3 jp1 jp2 jp3 jp4 s1 s2 s3 s4 e1 e2 e3 e4 l4 l5 l6 l7 x13 x28 x29
    MEM BND HL1 HL2 HL3 HL4 HU1 HU2 HU3 HF1 HF2 HF3 HD4 K.
  destruct CTX as (RS & TBL & UT1 & UT2 & UTS & UA8 & UB1 & UB2 & UDS & UDA & RT & RD & RI & A1 & A0 & A2 & A3 & A4 & A5
    & J1 & J2 & J3 & J4 & DTA & H1 & H2 & H3 & H4 & H5 & H6 & AT1 & AT2 & AS3 & AS1 & AS2 & DBA).
  destruct MEM as (C0 & C1 & C2 & C3 & CA & C8c & CB & C11 & C12 & CC & BD4 & BD3 & BD2 & BD1 & MI & TAB & TB
    & (obuf & OB & OBL) & UT & UD).
  destruct BND as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & B1 & B2 & B3 & B4 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  unfold AZ4_SB in *.
  assert (AIL : 4096 <= AIMG_LO /\ AIMG_LO <= AIMG_HI /\ AIMG_HI <= 2^47) by (unfold AIMG_LO, AIMG_HI; lia).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  assert (ZT : disjoint_from [(SP + -384, SP + -104); (DST, DST + dcap)] (DT + 4) (4 * 2^tl))
    by (cbn [disjoint_from]; unfold KXGoM.apart in *; lia).
  assert (SD1 : disjoint_from [(SP + -384, SP + -104); (DST, DST + dcap)] (shad DBL) (shad (DBH - 1) + 1 - shad DBL))
    by (eapply z4m_shd_dj; [exact AS3 | lia | lia | exact AS1 | lia | lia | lia | lia | lia]).
  assert (SD2 : disjoint_from [(SP + -384, SP + -104); (DST, DST + dcap)] (shad DST) (shad (DST + dcap - 1) + 1 - shad DST))
    by (eapply z4m_shd_dj; [exact AS3 | lia | lia | exact AS1 | lia | lia | lia | lia | lia]).
  pose proof (proj2 BD1) as WB1. pose proof (proj2 BD2) as WB2. pose proof (proj2 BD3) as WB3. pose proof (proj2 BD4) as WB4.
  cbn [cells_size csize BD4A] in WB1, WB2, WB3, WB4. pose proof (proj2 OB) as WOB.
  kx_runFLd [585188] 2000%nat (repeat true 4096)
      [KZRange SP 8192 (2^47); KZRange DST 4096 (2^47); KZRange seg 0 (2^32); KZRange dcap 6 (2^32);
       KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange (64 - tl) 52 63; KZRange mtl 1 12; KZRange dl 0 4096; KZRange (2^tl) 2 4096;
       KZRange c1 0 (2^64 - 1); KZRange c2 0 (2^64 - 1); KZRange c3 0 (2^64 - 1); KZRange c4 0 (2^64 - 1);
       KZRange p1 0 (2^64 - 1); KZRange p2 0 (2^64 - 1); KZRange p3 0 (2^64 - 1); KZRange p4 0 (2^64 - 1);
       KZRange b1 0 64; KZRange b2 0 64; KZRange b3 0 64; KZRange b4 0 64;
       KZRange f1 0 88; KZRange f2 0 88; KZRange f3 0 88; KZRange d4 0 76; KZRange U1 4096 (2^47); KZRange U2 4096 (2^47); KZRange U3 4096 (2^47);
       KZRange (bv_unsigned l4) 1 2; KZRange (bv_unsigned l5) 1 2; KZRange (bv_unsigned l6) 1 2; KZRange (bv_unsigned l7) 1 2;
       KZRange (DT + 4) 4096 (2^47); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47); KZAlign (DT + 4) 4;
       KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]; KZIdx tl (2^tl);
       KZWord (SP + -376) 8 (DST + 3 * seg); KZWord (SP + -368) 8 dl; KZWord (SP + -360) 8 (DST + dcap - 7);
       KZWord (SP + -320) 8 c2; KZWord (SP + -296) 8 c4; KZWord (SP + -288) 8 c3;
       KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -312) 8 (DST + seg); KZWord (SP + -304) 8 (DST + 2 * seg);
       KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
       KZWord (SP + -144) 8 c1; KZWord (SP + -184) 8 c2; KZWord (SP + -224) 8 c3; KZWord (SP + -264) 8 c4;
       KZWord (SP + -128) 8 p1; KZWord (SP + -168) 8 p2; KZWord (SP + -208) 8 p3; KZWord (SP + -248) 8 p4;
       KZRange O1 4096 (2^47 - 8); KZWr O1 8; KZDisj O1 8 (DT + 4) (4 * 2^tl); KZDisj O1 8 (SP + -384) 384; KZDisj O1 8 AIMG_LO (AIMG_HI - AIMG_LO);
       KZRange O2 4096 (2^47 - 8); KZWr O2 8; KZDisj O2 8 (DT + 4) (4 * 2^tl); KZDisj O2 8 (SP + -384) 384; KZDisj O2 8 AIMG_LO (AIMG_HI - AIMG_LO);
       KZRange O3 4096 (2^47 - 8); KZWr O3 8; KZDisj O3 8 (DT + 4) (4 * 2^tl); KZDisj O3 8 (SP + -384) 384; KZDisj O3 8 AIMG_LO (AIMG_HI - AIMG_LO);
       KZRange O4 4096 (2^47 - 8); KZWr O4 8; KZDisj O4 8 (DT + 4) (4 * 2^tl); KZDisj O4 8 (SP + -384) 384; KZDisj O4 8 AIMG_LO (AIMG_HI - AIMG_LO)]
      [(DT + 4, 4 * 2^tl)]
      [(DT + 4, 4 * 2^tl); (SP + -384, 280); (O1, 8); (O2, 8); (O3, 8); (O4, 8)]
      [(DT + 4, 4 * 2^tl); (O1, 8); (O2, 8); (O3, 8); (O4, 8)].
  all: try (z4m_flat tl AS3 AS1 J2 J3).
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => z4m_br tl end).
  all: try (lazymatch goal with |- store_ok _ _ _ _ = _ => z4m_stok4 end).
  pose proof J1 as J1u. pose proof J2 as J2u. pose proof J3 as J3u. unfold KXGoM.apart in J1u, J2u, J3u.
  pose proof (munch_refl [(SP + -384, SP + -104); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  kx_munch_wins MUW [(SP + -384, 280); (O1, 8); (O2, 8); (O3, 8); (O4, 8)].
  lazymatch goal with HLF : log_flat ?E ?l |- context [mem_denot ?E ?m ?l] =>
    assert (MIl : mem_inv bsegs (mem_denot E m l)) by
      (apply (kx_mem_inv_log bsegs E m l MI HLF); cbn [log_wr]; repeat (first [exact I | split]);
       first [z4m_wrc tl WB4 ltac:(idtac; clear - A5 A1 A2 G1 G2 G3 G4 G5 G6 G7 G8 OBL HL1 HL2 HL3 HL4; lia) | z4m_wrc tl WB3 ltac:(idtac; clear - A5 A1 A2 G1 G2 G3 G4 G5 G6 G7 G8 OBL HL1 HL2 HL3 HL4; lia) | z4m_wrc tl WB2 ltac:(idtac; clear - A5 A1 A2 G1 G2 G3 G4 G5 G6 G7 G8 OBL HL1 HL2 HL3 HL4; lia) | z4m_wrc tl WB1 ltac:(idtac; clear - A5 A1 A2 G1 G2 G3 G4 G5 G6 G7 G8 OBL HL1 HL2 HL3 HL4; lia) | z4m_wrc tl WOB ltac:(idtac; clear - A5 A1 A2 G1 G2 G3 G4 G5 G6 G7 G8 OBL HL1 HL2 HL3 HL4; lia)]) end.

  kx_post_mem_free.
  lazymatch goal with HL : log_flat ?E ?l |- context [mem_denot ?E ?m ?l] =>
    pose proof (kx_u8arr_replay bsegs E m l DST obuf OB HL) as OB';
    pose proof (replay_length E l DST obuf) as OL' end.
  z4m_frame TB ltac:(idtac; clear - A5 A1 A2 A3 A4 J2u J3u G1 G2 G3 G4 G5 G6 G7 G8 TBL HL1 HL2 HL3 HL4; lia).
  z4m_frame C0 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame C1 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame C2 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame C3 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame CA ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame C8c ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame CB ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame C11 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame C12 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame CC ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  unfold BD4A in BD4, BD3, BD2, BD1.
  apply (kx_rwc_cons bsegs) in BD4; destruct BD4 as [BD4c BD4]; cbn [csize] in BD4; kx_rwc_norm BD4;
    apply (kx_rwc_cons bsegs) in BD4; destruct BD4 as [BD4b BD4]; cbn [csize] in BD4; kx_rwc_norm BD4.
  apply (kx_rwc_cons bsegs) in BD3; destruct BD3 as [BD3c BD3]; cbn [csize] in BD3; kx_rwc_norm BD3;
    apply (kx_rwc_cons bsegs) in BD3; destruct BD3 as [BD3b BD3]; cbn [csize] in BD3; kx_rwc_norm BD3.
  apply (kx_rwc_cons bsegs) in BD2; destruct BD2 as [BD2c BD2]; cbn [csize] in BD2; kx_rwc_norm BD2;
    apply (kx_rwc_cons bsegs) in BD2; destruct BD2 as [BD2b BD2]; cbn [csize] in BD2; kx_rwc_norm BD2.
  apply (kx_rwc_cons bsegs) in BD1; destruct BD1 as [BD1c BD1]; cbn [csize] in BD1; kx_rwc_norm BD1;
    apply (kx_rwc_cons bsegs) in BD1; destruct BD1 as [BD1b BD1]; cbn [csize] in BD1; kx_rwc_norm BD1.
  z4m_frame BD4c ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD3c ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD2c ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD1c ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD4 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD3 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD2 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD1 ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  kx_cell4w BD4b.
  z4m_frame BD3b ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD2b ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  z4m_frame BD1b ltac:(idtac; clear - A5 A1 A2 J1u G1 G2 G3 G4 G5 G6 G7 G8 HL1 HL2 HL3 HL4; lia).
  lazymatch goal with |- context [mem_denot ?E _ _] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      repeat match goal with H : rw_cells _ _ _ [C4 (edenot E ?v)] |- _ => rewrite (ez_ok zv E (kE_atoms zv xs) v) in H end
    end
  end.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?m ?l) _) =>
    eapply evtF_eq; [| eapply (K (mem_denot E m l))] end.
  1: z4m_regs.
  all: try exact MUW.
  all: try exact WMr.
  all: try (progress unfold z4L_mem; repeat match goal with |- _ /\ _ => split end).
  all: try (lazymatch goal with |- rw_cells _ _ _ (BD4A _ _ _ _ _ _) => unfold BD4A; kx_cells_merge end).
  all: try (lazymatch goal with |- rw_cells _ _ _ _ => eassumption end).
  all: try (lazymatch goal with |- mem_inv _ _ => exact MIl end).
  all: try (lazymatch goal with |- mem_inv _ _ => eassumption end).
  all: try (lazymatch goal with |- bytes_at _ _ _ _ => eassumption end).
  all: try (lazymatch goal with |- KXTac.ztab_fact _ _ _ _ _ _ => eapply w4_ztab_munch; [exact TAB | exact MUW | exact ZT | lia | lia] end).
  all: try (lazymatch goal with |- ex _ => eexists; split; [exact OB' | rewrite OL'; exact OBL] end).
  all: try (lazymatch goal with |- unpoisoned _ _ _ =>
              first [ eapply unpoisoned_munch; [exact UT | exact MUW | exact SD1]
                    | eapply unpoisoned_munch; [exact UD | exact MUW | exact SD2] ] end).
  all: try (lazymatch goal with |- _ <= _ <= _ => z4m_rng end).
Qed.

Lemma z4s1_md2 : forall RNG Q gp tp FR fc SP DST dcap seg DT tl mtl dl DBL DBH cbs,
  z4L_md2_goal RNG Q gp tp FR fc SP DST dcap seg DT tl mtl dl DBL DBH cbs.
Proof.
  intros RNG Q gp tp FR fc SP DST dcap seg DT tl mtl dl DBL DBH cbs CTX mm w0 w4 w5 w7 c1 c2 c3 c4 p1 p2 p3 p4
    b1 b2 b3 b4 O1 O2 O3 O4 d1 d2 d3 d4 jp1 jp2 jp3 jp4 s1 s2 s3 s4 e1 e2 e3 e4 l1 l2 l3 l4 x11 x13 x20 x27 x29
    MEM BND HL1 HL2 HL3 HL4 HD1 HD2 HD3 HD4 K.
  eapply (m2s1 RNG Q gp tp FR fc SP DST dcap seg DT tl mtl dl DBL DBH cbs CTX); try eassumption.
  intros m1 v0 v4 v5 v7 U1 f1 l5 y11 y13 y20 y29 MU1 WM1 MEM1 HL5 HU1 HF1.
  eapply (m2s2 RNG Q gp tp FR fc SP DST dcap seg DT tl mtl dl DBL DBH cbs CTX); try eassumption.
  intros m2 v0' v4' v5' v7' U2 f2 l6 y13' y29' MU2 WM2 MEM2 HL6 HU2 HF2.
  eapply (m2s3 RNG Q gp tp FR fc SP DST dcap seg DT tl mtl dl DBL DBH cbs CTX); try eassumption.
  intros m3 v0'' v4'' v5'' v7'' U3 f3 l7 y13'' y28 y29'' MU3 WM3 MEM3 HL7 HU3 HF3.
  eapply (m2s4 RNG Q gp tp FR fc SP DST dcap seg DT tl mtl dl DBL DBH cbs CTX); try eassumption.
  intros m4 v0''' v4''' v5''' v7''' U4 f4 l8 y11' y13''' y28' y29''' MU4 WM4 MEM4 HL8 HU4 HF4.
  eapply K; try eassumption.
  - eapply munch_trans; [eapply munch_trans; [eapply munch_trans; [exact MU1 | exact MU2] | exact MU3] | exact MU4].
  - eapply wmono_trans; [eapply wmono_trans; [eapply wmono_trans; [exact WM1 | exact WM2] | exact WM3] | exact WM4].
Qed.

End CANSEC1.
