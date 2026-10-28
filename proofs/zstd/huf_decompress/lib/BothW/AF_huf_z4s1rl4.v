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

Section Z4R4.
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

  Definition z4R_s4_goal (r1 r2 r3 r4 : bool) : Prop :=
    forall (AI : AMallocIface) (L : alayout) (st : astate) (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
           (cells : list deltX2) (pdt : aptr) (SBL SBH : Z) (rstk : region)
           mm (l1 l2 l3 e1 e2 e3 e4 o1 b1 o2 b2 o3 b3 o4 cq4 cr4 : Z) (c1 c2 c3 k4 : word)
           (jp1 jp2 jp3 jp4 : list byte) (w0 l13 l14 l15 l16 v16 v17 v22 v27 v31 : word),
    CTX AI L st LB rng_fs cells pdt SBL SBH rstk -> LAY l1 l2 l3 -> z4R_pre (n - (6 + l1 + l2 + l3)) o4 cq4 cr4 r4 ->
    Z4SF' mm (SPL w0 (Zw (z4R_fl r1)) l13 (Zw (z4R_fl r2)) c2 k4 c3)
      (BDS k4 (8 * cq4 + cr4) jp4 (6 + l1 + l2 + l3) o4) (BDS c3 b3 jp3 (6 + l1 + l2) o3)
      (BDS c2 b2 jp2 (6 + l1) o2) (BDS c1 b1 jp1 6 o1) ->
    (forall mm' (o4' b4' : Z) (c4 : word) (u10 u17 u22 u27 u31 : word),
       Z4SF' mm' (SPL w0 (Zw (z4R_fl r1)) l13 (Zw (z4R_fl r2)) c2 c4 c3)
         (BDS c4 b4' jp4 (6 + l1 + l2 + l3) o4') (BDS c3 b3 jp3 (6 + l1 + l2) o3)
         (BDS c2 b2 jp2 (6 + l1) o2) (BDS c1 b1 jp1 6 o1) ->
       z4R_res r4 o4 cq4 cr4 o4' b4' ->
       evtF bsegs RNG Q (ZR 587500 mm' (Zw b2) (Zw (2^61)) (Zw (64 - tl)) (Zw (- DT - 5)) l15 (Zw (DST + e4)) u10 l16
                           (Zw (DST + e1)) (Zw (SS + 6 + o1)) (Zw (SS + 6 + l1 + o2)) (Zw (SS + 6 + l1 + l2 + o3))
                           (Zw (SS + 6 + l1 + l2 + l3 + o4')) u17 (Zw (DST + e3)) (Zw (DST + e2)) (Zw b3)
                           (Zw AZ4_SB) u22 c1 (Zw b4') l14 (Zw b1) u27 (Zw (z4R_fl r4)) (Zw (z4R_fl r3))
                           (Zw (DT + 4)) u31)) ->
    evtF bsegs RNG Q (ZR (if r3 then 587288 else 587628) mm (Zw b2) (Zw (2^61)) (Zw (64 - tl)) (Zw (- DT - 5)) l15
                        (Zw (DST + e4)) c1 l16 (Zw (DST + e1)) (Zw (SS + 6 + o1)) (Zw (SS + 6 + l1 + o2))
                        (Zw (SS + 6 + l1 + l2 + o3)) v16 v17 (Zw (DST + e3)) (Zw (DST + e2)) (Zw b3) (Zw AZ4_SB) v22
                        (Zw (SS + 6 + l1 + l2 + l3 + o4)) (Zw (8 * cq4 + cr4)) l14 (Zw b1) v27 (Zw 3)
                        (Zw (z4R_fl r3)) (Zw (DT + 4)) v31).
End Z4R4.


Lemma z4R_s4_false : forall RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    r1 r2 r3, z4R_s4_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    r1 r2 r3 false.
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q r1 r2 r3.
  revert r3. intros r3.
  intros AI L st LB rng_fs cells pdt SBL SBH rstk mm l1 l2 l3 e1 e2 e3 e4 o1 b1 o2 b2 o3 b3 o4 cq4 cr4 c1 c2 c3 k4
    jp1 jp2 jp3 jp4 w0 l13 l14 l15 l16 v16 v17 v22 v27 v31 CTX LY PRE SF K.
  destruct LY as (HL1 & HL2 & HL3 & HN & HD6 & HSG).
  unfold z4R_pre in PRE. cbn iota in PRE.
  destruct PRE as (O4a & O4e & C4r & C4q & C4b & O4r).
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
  pose proof (munch_refl [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -264, bv_unsigned sp + -264 + 40);
                          (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof (SysStep.rw_cells_wr_at bsegs mm _ _ 120 SPL ltac:(rewrite SPLS; lia)) as WSP.
  pose proof (SysStep.rw_cells_wr_at bsegs mm _ _ 40 B4 ltac:(rewrite B4S; lia)) as WB4.
  unfold AZ4_SB in *.
  destruct r3; cbn [z4R_fl] in *.
  - kx_runFLd [587500; AZ4_C0] 200%nat (@nil bool)
    [KZRange (bv_unsigned sp) 8192 (2^47); KZRange SS 4096 (2^47); KZRange o4 0 7; KZRange l1 1 (2^26);
    KZRange l2 1 (2^26); KZRange l3 1 (2^26);
    KZWord (bv_unsigned sp + -232) 8 (SS + (6 + l1 + l2 + l3) + 8); KZWr (bv_unsigned sp + -384) 120;
    KZWr (bv_unsigned sp + -264) 40]
    (@nil (Z * Z)) [(bv_unsigned sp + -400, 400)] (@nil (Z * Z)).
    all: try (lazymatch goal with |- _ <= _ < _ => lia | |- _ <= _ <= _ => lia end).
    all: try z4r_stok.
    kx_post_regs_keep. z4post_ez. cbn [mem_denot] in *.
    try replace (SS + (l1 + (l2 + (l3 + o4))) + 6) with (SS + 6 + l1 + l2 + l3 + o4) by lia.
    eapply (K mm o4 (8 * cq4 + cr4) k4); [exact SF | cbn [z4R_res]; split; reflexivity].

  - kx_runFLd [587500; AZ4_C0] 200%nat (@nil bool)
    [KZRange (bv_unsigned sp) 8192 (2^47); KZRange SS 4096 (2^47); KZRange o4 0 7; KZRange l1 1 (2^26);
    KZRange l2 1 (2^26); KZRange l3 1 (2^26);
    KZWord (bv_unsigned sp + -232) 8 (SS + (6 + l1 + l2 + l3) + 8); KZWr (bv_unsigned sp + -384) 120;
    KZWr (bv_unsigned sp + -264) 40]
    (@nil (Z * Z)) [(bv_unsigned sp + -400, 400)] (@nil (Z * Z)).
    all: try (lazymatch goal with |- _ <= _ < _ => lia | |- _ <= _ <= _ => lia end).
    all: try z4r_stok.
    kx_post_regs_keep. z4post_ez. cbn [mem_denot] in *.
    try replace (SS + (l1 + (l2 + (l3 + o4))) + 6) with (SS + 6 + l1 + l2 + l3 + o4) by lia.
    eapply (K mm o4 (8 * cq4 + cr4) k4); [exact SF | cbn [z4R_res]; split; reflexivity].

Qed.

Lemma z4R_s4_tt : forall RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    r1 r2, z4R_s4_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    r1 r2 true true.
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q r1 r2.
  intros AI L st LB rng_fs cells pdt SBL SBH rstk mm l1 l2 l3 e1 e2 e3 e4 o1 b1 o2 b2 o3 b3 o4 cq4 cr4 c1 c2 c3 k4
    jp1 jp2 jp3 jp4 w0 l13 l14 l15 l16 v16 v17 v22 v27 v31 CTX LY PRE SF K.
  destruct LY as (HL1 & HL2 & HL3 & HN & HD6 & HSG).
  unfold z4R_pre in PRE. cbn iota in PRE.
  destruct PRE as (O4a & [O4b|(O4c & O4d)] & C4r & C4q & C4b & O4r); [lia|].
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
  pose proof (munch_refl [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -264, bv_unsigned sp + -264 + 40);
                          (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof (SysStep.rw_cells_wr_at bsegs mm _ _ 120 SPL ltac:(rewrite SPLS; lia)) as WSP.
  pose proof (SysStep.rw_cells_wr_at bsegs mm _ _ 40 B4 ltac:(rewrite B4S; lia)) as WB4.
  destruct (z4R_srcwin AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk mm CTX MU
    ltac:(lia) ltac:(lia)) as (USS & SBA & SBL1 & SBL2 & SBR & SSR).
  pose proof (z4R_srctop AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk CTX
    ltac:(lia)) as SBT.
  pose proof (z4_bytes_sub mm SS src (6 + l1 + l2 + l3 + o4 - 8) 16 BSS ltac:(lia) ltac:(lia) ltac:(lia)) as BSL.
  replace (SS + (6 + l1 + l2 + l3 + o4 - 8)) with (SS + (6 + l1 + l2 + l3) + o4 - 8) in BSL by lia.
  pose proof (unpoisoned_sub mm SS (SS + zlen src) (SS + (6 + l1 + l2 + l3) + o4 - 8) (SS + (6 + l1 + l2 + l3) + o4 - 8 + 16) USS ltac:(lia) ltac:(lia)) as USL.
  assert (RSL : rng RNG (SS + (6 + l1 + l2 + l3) + o4 - 8) 16) by (eapply rng_sub; [exact SSR | lia | lia]).
  assert (AS3 : KXGoM.apart (bv_unsigned sp + -400) 400 ASHOFF (ATOP / 8 + 1))
    by (unfold KXGoM.apart, ASHOFF; right; Z.div_mod_to_equations; lia).
  assert (TF : KXGoM.apart (SS + (6 + l1 + l2 + l3) + o4 - 8) 16 (bv_unsigned sp + -400) 400) by (unfold KXGoM.apart; left; lia).
  remember (8 * cq4 + cr4) as b4 eqn:EB4.
  unfold AZ4_SB in *. cbn [z4R_fl] in *.
  kx_runFLd [587500; AZ4_C0] 300%nat (true :: repeat false 63)
    [KZRange (bv_unsigned sp) 8192 (2^47); KZRange SS 4096 (2^47); KZRange o4 8 (2^26); KZRange l1 1 (2^26);
     KZRange l2 1 (2^26); KZRange l3 1 (2^26); KZRange b4 0 63; KZRange (zlen src - (6 + l1 + l2 + l3) - o4) 8 (2^26);
     KZRange (SS + 6 + l1 + l2 + l3 + o4) 4096 (2^47);
     KZWord (bv_unsigned sp + -232) 8 (SS + (6 + l1 + l2 + l3) + 8); KZWord (bv_unsigned sp + -280) 8 (DT + 4);
     KZWr (bv_unsigned sp + -384) 120; KZWr (bv_unsigned sp + -264) 40]
    [(SS + (6 + l1 + l2 + l3) + o4 - 8, 16)] [(bv_unsigned sp + -400, 400)] [(SS + (6 + l1 + l2 + l3) + o4 - 8, 16)].
  all: try (lazymatch goal with |- _ <= _ < _ => lia | |- _ <= _ <= _ => lia end).
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => z4r_brx end).
  all: try (lazymatch goal with |- accP _ _ _ => clear - AS3 TF RSL SBT SBL1 SBL2 HN HL1 HL2 HL3 O4a O4c O4d C4r C4q C4b EB4 FP1 FP2 ATR FS1 FS2 NSM ALY SPT; z4r_acc RSL end).
  all: try (lazymatch goal with |- flat _ _ _ /\ _ => clear - AS3 TF RSL SBT SBL1 SBL2 HN HL1 HL2 HL3 O4a O4c O4d C4r C4q C4b EB4 FP1 FP2 ATR FS1 FS2 NSM ALY SPT; z4r_flat tl AS3 AS3 TF TF end).
  all: try z4r_stok.
  kx_post_regs_keep.
  unfold SPD in SPL. kx_cells_split SPL. unfold BD4A in B4. kx_cells_split B4. kx_cells_post.
  kx_munch MUW. kx_post_mem_free.
  kx_frame B3. kx_frame B2. kx_frame B1.
  lazymatch goal with HL : log_flat ?E ?l |- context [mem_denot ?E ?m ?l] =>
    destruct (kx_u8arr_ex bsegs E m l DST buf BUF HL) as (buf' & BUF' & BUFL') end.
  z4post_ez.
  cbn [mem_denot] in *.
  lazymatch goal with |- context [edenot KXE (EAlu ALU_AND (EVar ?i) (ELit 7))] =>
    assert (HAND : edenot KXE (EAlu ALU_AND (EVar i) (ELit 7)) = Z_to_bv 64 cr4);
    [ apply bv_eq; cbn [edenot]; rewrite u_and64;
      assert (EV : ev KXE i = Z_to_bv 64 b4) by reflexivity; rewrite EV, !Z_to_bv_unsigned;
      unfold bv_wrap, bv_modulus; rewrite !(Z.mod_small _ (2 ^ Z.of_N 64)) by (change (2 ^ Z.of_N 64) with (2^64); lia);
      change 7 with (Z.ones 3); rewrite Z.land_ones by lia; subst b4; Z.div_mod_to_equations; lia
    | rewrite HAND in * ]
  end.
  lazymatch goal with |- context [edenot KXE (EAluw ALU_SRL (EVar ?i) (ELit 3))] =>
    rewrite (z4_srlw3 KXE (EVar i) b4) in * by (first [reflexivity | lia]) end.
  assert (S8 : bv_unsigned (Z_to_bv 64 (b4 / 8)) = cq4).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
    subst b4. rewrite Z.mod_small; Z.div_mod_to_equations; lia. }
  rewrite S8 in *.
  try replace (SS + (l1 + (l2 + (l3 + (o4 + - cq4)))) + 6) with (SS + 6 + l1 + l2 + l3 + (o4 - cq4)) by lia.
  try replace (SS + (l1 + (l2 + (l3 + (o4 + -1 * cq4)))) + 6) with (SS + (6 + l1 + l2 + l3) + (o4 - cq4)) in * by lia.
  eapply (K _ (o4 - cq4) cr4); [| cbn [z4R_res]; split; reflexivity].
  eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
            cells cbs pdt SBL SBH rstk mm _ (-264)); [exact CTX | lia | lia | lia | exact SF | exact MUW | idtac .. ].
  all: try reflexivity.
  all: try assumption.
  all: try (exists buf'; split; [exact BUF' | lia]).
  all: try (unfold SPD; kx_cells_merge).
  all: try (unfold BD4A; kx_cells_merge).
Qed.

Lemma z4R_s4_ft : forall RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    r1 r2, z4R_s4_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    r1 r2 false true.
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q r1 r2.
  intros AI L st LB rng_fs cells pdt SBL SBH rstk mm l1 l2 l3 e1 e2 e3 e4 o1 b1 o2 b2 o3 b3 o4 cq4 cr4 c1 c2 c3 k4
    jp1 jp2 jp3 jp4 w0 l13 l14 l15 l16 v16 v17 v22 v27 v31 CTX LY PRE SF K.
  destruct LY as (HL1 & HL2 & HL3 & HN & HD6 & HSG).
  unfold z4R_pre in PRE. cbn iota in PRE.
  destruct PRE as (O4a & [O4b|(O4c & O4d)] & C4r & C4q & C4b & O4r); [lia|].
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
  pose proof (munch_refl [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -264, bv_unsigned sp + -264 + 40);
                          (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof (SysStep.rw_cells_wr_at bsegs mm _ _ 120 SPL ltac:(rewrite SPLS; lia)) as WSP.
  pose proof (SysStep.rw_cells_wr_at bsegs mm _ _ 40 B4 ltac:(rewrite B4S; lia)) as WB4.
  destruct (z4R_srcwin AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk mm CTX MU
    ltac:(lia) ltac:(lia)) as (USS & SBA & SBL1 & SBL2 & SBR & SSR).
  pose proof (z4R_srctop AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk CTX
    ltac:(lia)) as SBT.
  pose proof (z4_bytes_sub mm SS src (6 + l1 + l2 + l3 + o4 - 8) 16 BSS ltac:(lia) ltac:(lia) ltac:(lia)) as BSL.
  replace (SS + (6 + l1 + l2 + l3 + o4 - 8)) with (SS + (6 + l1 + l2 + l3) + o4 - 8) in BSL by lia.
  pose proof (unpoisoned_sub mm SS (SS + zlen src) (SS + (6 + l1 + l2 + l3) + o4 - 8) (SS + (6 + l1 + l2 + l3) + o4 - 8 + 16) USS ltac:(lia) ltac:(lia)) as USL.
  assert (RSL : rng RNG (SS + (6 + l1 + l2 + l3) + o4 - 8) 16) by (eapply rng_sub; [exact SSR | lia | lia]).
  assert (AS3 : KXGoM.apart (bv_unsigned sp + -400) 400 ASHOFF (ATOP / 8 + 1))
    by (unfold KXGoM.apart, ASHOFF; right; Z.div_mod_to_equations; lia).
  assert (TF : KXGoM.apart (SS + (6 + l1 + l2 + l3) + o4 - 8) 16 (bv_unsigned sp + -400) 400) by (unfold KXGoM.apart; left; lia).
  remember (8 * cq4 + cr4) as b4 eqn:EB4.
  unfold AZ4_SB in *. cbn [z4R_fl] in *.
  kx_runFLd [587500; AZ4_C0] 300%nat (true :: repeat false 63)
    [KZRange (bv_unsigned sp) 8192 (2^47); KZRange SS 4096 (2^47); KZRange o4 8 (2^26); KZRange l1 1 (2^26);
     KZRange l2 1 (2^26); KZRange l3 1 (2^26); KZRange b4 0 63; KZRange (zlen src - (6 + l1 + l2 + l3) - o4) 8 (2^26);
     KZRange (SS + 6 + l1 + l2 + l3 + o4) 4096 (2^47);
     KZWord (bv_unsigned sp + -232) 8 (SS + (6 + l1 + l2 + l3) + 8); KZWord (bv_unsigned sp + -280) 8 (DT + 4);
     KZWr (bv_unsigned sp + -384) 120; KZWr (bv_unsigned sp + -264) 40]
    [(SS + (6 + l1 + l2 + l3) + o4 - 8, 16)] [(bv_unsigned sp + -400, 400)] [(SS + (6 + l1 + l2 + l3) + o4 - 8, 16)].
  all: try (lazymatch goal with |- _ <= _ < _ => lia | |- _ <= _ <= _ => lia end).
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => z4r_brx end).
  all: try (lazymatch goal with |- accP _ _ _ => clear - AS3 TF RSL SBT SBL1 SBL2 HN HL1 HL2 HL3 O4a O4c O4d C4r C4q C4b EB4 FP1 FP2 ATR FS1 FS2 NSM ALY SPT; z4r_acc RSL end).
  all: try (lazymatch goal with |- flat _ _ _ /\ _ => clear - AS3 TF RSL SBT SBL1 SBL2 HN HL1 HL2 HL3 O4a O4c O4d C4r C4q C4b EB4 FP1 FP2 ATR FS1 FS2 NSM ALY SPT; z4r_flat tl AS3 AS3 TF TF end).
  all: try z4r_stok.
  kx_post_regs_keep.
  unfold SPD in SPL. kx_cells_split SPL. unfold BD4A in B4. kx_cells_split B4. kx_cells_post.
  kx_munch MUW. kx_post_mem_free.
  kx_frame B3. kx_frame B2. kx_frame B1.
  lazymatch goal with HL : log_flat ?E ?l |- context [mem_denot ?E ?m ?l] =>
    destruct (kx_u8arr_ex bsegs E m l DST buf BUF HL) as (buf' & BUF' & BUFL') end.
  z4post_ez.
  cbn [mem_denot] in *.
  lazymatch goal with |- context [edenot KXE (EAlu ALU_AND (EVar ?i) (ELit 7))] =>
    assert (HAND : edenot KXE (EAlu ALU_AND (EVar i) (ELit 7)) = Z_to_bv 64 cr4);
    [ apply bv_eq; cbn [edenot]; rewrite u_and64;
      assert (EV : ev KXE i = Z_to_bv 64 b4) by reflexivity; rewrite EV, !Z_to_bv_unsigned;
      unfold bv_wrap, bv_modulus; rewrite !(Z.mod_small _ (2 ^ Z.of_N 64)) by (change (2 ^ Z.of_N 64) with (2^64); lia);
      change 7 with (Z.ones 3); rewrite Z.land_ones by lia; subst b4; Z.div_mod_to_equations; lia
    | rewrite HAND in * ]
  end.
  lazymatch goal with |- context [edenot KXE (EAluw ALU_SRL (EVar ?i) (ELit 3))] =>
    rewrite (z4_srlw3 KXE (EVar i) b4) in * by (first [reflexivity | lia]) end.
  assert (S8 : bv_unsigned (Z_to_bv 64 (b4 / 8)) = cq4).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
    subst b4. rewrite Z.mod_small; Z.div_mod_to_equations; lia. }
  rewrite S8 in *.
  try replace (SS + (l1 + (l2 + (l3 + (o4 + - cq4)))) + 6) with (SS + 6 + l1 + l2 + l3 + (o4 - cq4)) by lia.
  try replace (SS + (l1 + (l2 + (l3 + (o4 + -1 * cq4)))) + 6) with (SS + (6 + l1 + l2 + l3) + (o4 - cq4)) in * by lia.
  eapply (K _ (o4 - cq4) cr4); [| cbn [z4R_res]; split; reflexivity].
  eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
            cells cbs pdt SBL SBH rstk mm _ (-264)); [exact CTX | lia | lia | lia | exact SF | exact MUW | idtac .. ].
  all: try reflexivity.
  all: try assumption.
  all: try (exists buf'; split; [exact BUF' | lia]).
  all: try (unfold SPD; kx_cells_merge).
  all: try (unfold BD4A; kx_cells_merge).
Qed.

Lemma z4R_s4 : forall RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    r1 r2 r3 r4,
  z4R_s4_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q r1 r2 r3 r4.
Proof.
  intros. destruct r4; [destruct r3; [apply z4R_s4_tt | apply z4R_s4_ft] | apply z4R_s4_false].
Qed.

End CANSEC1.
