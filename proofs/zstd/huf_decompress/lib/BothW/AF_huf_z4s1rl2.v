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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s1_iface AF_huf_z4s1mk AF_huf_z4s3b AF_huf_z4s1rl_iface.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac z4f2_fr F H := z4m_frame H ltac:(idtac; clear - F; lia).

Ltac z4f2_post MU TB DTH SRC OBb BD4 BD3 BD1 FRS SPL BD2 FB buf OBL K :=
  z4f2_fr FB TB; z4f2_fr FB DTH; z4f2_fr FB SRC; z4f2_fr FB OBb;
  z4f2_fr FB BD4; z4f2_fr FB BD3; z4f2_fr FB BD1; z4f2_fr FB FRS;
  kx_post_regs_keep;
  kx_cells_split SPL; kx_cells_split BD2; kx_cells_post;
  kx_munch MU; kx_post_mem_free;
  z4post_ez;
  eapply K;
  [ unfold Z4SF; repeat match goal with |- _ /\ _ => split end;
    [ exists buf; split; [split; eassumption | exact OBL] | .. ]
  | .. ];
  try (lazymatch goal with |- rw_cells _ _ _ (SPD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => unfold SPD; kx_cells_merge end);
  try (lazymatch goal with |- rw_cells _ _ _ (BD4A _ _ _ _ _ _) => unfold BD4A; first [eassumption | kx_cells_merge] end);
  try (lazymatch goal with |- cells_size _ = _ => reflexivity end);
  try (lazymatch goal with |- z4R_res _ _ _ _ _ _ => cbn [z4R_res]; split; lia end);
  try eassumption.

Section CANSEC1. Context {rc : runConstT}.

Lemma z4R_s2 : forall RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q r1 r2,
  z4R_s2_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q r1 r2.
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q r1 r2.
  unfold z4R_s2_goal.
  intros AI L st LB rng_fs cells pdt SBL SBH rstk mm l1 l2 l3 e1 e2 e3 e4 o1 b1 o2 cq2 cr2 o3 cq3 cr3 o4 cq4 cr4
    c1 k2 k3 k4 jp1 jp2 jp3 jp4 w0 l13 l14 l15 l16 v14 v22 v27 v28 v29 v31 CTX LAY PRE MEM K.
  destruct LAY as (LA1 & LA2 & LA3 & LA4 & LA5 & LA6).
  destruct MEM as ((buf & OB & OBL) & SRC & TB & DTH & STK & SPL & SPLs & BD4 & BD4s & BD3 & BD3s & BD2 & BD2s
                   & BD1 & BD1s & FRS & MI & MU & WM).
  destruct (z4R_srcwin AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk mm
              CTX MU ltac:(lia) ltac:(lia)) as (UN & SA8 & SLE & SHE & SRS & RSS).
  destruct (z4ctx_facts AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk
              CTX ltac:(lia)) as (FD1 & FD2 & FD3 & FD4 & FD5 & FSS & FSP & FSP2 & FRK).
  destruct (FSS ltac:(lia)) as [FS1 FS2]. clear FSS.
  destruct CTX as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2
                   & DJ3 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRSK & WSK & WIM & WIS & WFS).
  assert (SHT : SS + zlen src <= ATOP).
  { destruct (SRCB ltac:(lia)) as (pb & HB & _ & _). pose proof (ablk_lin _ _ (ABL _ HB)) as A.
    cbn [ab_addr ab_size] in A. lia. }
  assert (DTT : DT + 4 + 4 * 2^tl <= ATOP).
  { pose proof (ablk_lin _ _ (ABL _ HDT)) as A. cbn [ab_addr ab_size] in A. unfold DTABLE_BYTES, HufHarness.DT_BYTES in A.
    pose proof (Z.pow_le_mono_r 2 tl mtl ltac:(lia) TLM). lia. }
  assert (DSTT : DST + dcap <= ATOP).
  { destruct DSTF as [(_ & E)|(pb & HB1)]; [lia|]. pose proof (ablk_lin _ _ (ABL _ HB1)) as A.
    cbn [ab_addr ab_size] in A. lia. }
  assert (AIL : 4096 <= AIMG_LO /\ AIMG_LO <= AIMG_HI /\ AIMG_HI <= 2^47) by (unfold AIMG_LO, AIMG_HI; lia).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  assert (FSA : KXGoM.apart (bv_unsigned sp + -384) 384 ASHOFF (ATOP / 8 + 1)) by (unfold KXGoM.apart, ASHOFF; lia).
  assert (ML1 : Z.of_nat (length (map (Z_to_bv 8) src)) = zlen src) by (rewrite length_map; reflexivity).
  assert (ML2 : Z.of_nat (length (map (Z_to_bv 8) buf)) = dcap) by (rewrite length_map; exact OBL).
  assert (ML3 : Z.of_nat (length [Z_to_bv 8 mtl; Z_to_bv 8 1; Z_to_bv 8 tl; Z_to_bv 8 mtl]) = 4) by reflexivity.
  assert (SPR : 0 <= bv_unsigned sp < 2^64)
    by (pose proof (bv_unsigned_in_range _ sp) as X; unfold bv_modulus in X; lia).
  pose proof (conj FSP (conj DTT (conj DSTT (conj SHT (conj ML1 (conj ML2 (conj ML3 (conj LCB (conj AIL
    (conj FD1 (conj FD4 (conj FS1 (conj LA4 (conj LOS (conj SPR ATR))))))))))))))) as FB.
  remember (SS + 6 + l1) as B eqn:EB.
  assert (EB2 : SS + (6 + l1) = B) by lia. rewrite EB2 in *.
  assert (UB : unpoisoned mm B (B + l2)) by (eapply unpoisoned_sub; [exact UN | lia | lia]).
  pose proof (z4_bytes_sub mm SS src (6 + l1) l2 SRC ltac:(lia) ltac:(lia) ltac:(lia)) as SB2. rewrite EB2 in SB2.
  pose proof (z4_len_sub src (6 + l1) l2 ltac:(lia) ltac:(lia) ltac:(lia)) as SBL2.
  assert (RB : rng RNG B l2) by (eapply rng_sub; [exact RSS | lia | lia]).
  assert (HA2 : 0 <= SBL).
  { destruct (SRCB ltac:(lia)) as (pb & HB & _ & _). pose proof (ablk_lin _ _ (ABL _ HB)) as A.
    cbn [ab_addr ab_size] in A. lia. }
  assert (HA3 : SBL <= B) by lia. assert (HA4 : B + l2 <= SBL + (SBH - SBL)) by lia.
  destruct OB as [OBb OBw].
  unfold SPD in SPL. unfold BD4A in BD4, BD3, BD2, BD1.
  pose proof (proj2 SPL) as WSP. pose proof (proj2 BD2) as WB2. cbn [cells_size csize] in WSP, WB2.
  unfold AZ4_SB in *.
  pose proof (AI_layout AI L RNG st LB m0 AH) as LY.
  assert (SPB : bv_unsigned sp <= 2^47) by (clear - LY SPT; lia).
  assert (RFR : rng RNG (bv_unsigned sp + -384) 384) by (eapply rng_sub; [exact FRK | lia | lia]).
  destruct r2.
  - unfold z4R_pre in PRE. destruct PRE as (P0 & [P1 | (P2 & P3)] & P4 & P5 & P6 & P7); [lia|].
    assert (exists p, o2 = p + cq2 /\ 1 <= p) as (p & -> & PP) by (exists (o2 - cq2); lia).
    destruct r1; cbn [z4R_fl] in *; cbn iota.
    all: kx_runFLd [586880] 40%nat (repeat true 4096)
      [KZRange B 4096 (2^47); KZRange p 1 (2^26); KZRange cq2 0 7; KZRange cr2 0 7; KZRange (8 * cq2 + cr2) 0 63;
       KZRange (p + cq2 - 8) 0 (2^26); KZRange (bv_unsigned sp) 8192 (2^47); KZWord (bv_unsigned sp + -152) 8 (B + 8)]
      (@nil (Z * Z)) [(bv_unsigned sp + -384, 384)] (@nil (Z * Z)).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => lia end).
    all: kx_post_regs_keep.
    all: cbn [mem_denot] in *.
    all: lazymatch goal with |- context [edenot ?E (EAluw ALU_SRL ?e (ELit 3))] =>
           rewrite (z4_srlw3 E e (8 * cq2 + cr2)) by (first [reflexivity | lia | (z4ez; reflexivity)]) end.
    all: replace ((8 * cq2 + cr2) / 8) with cq2 by (Z.div_mod_to_equations; lia).
    all: z4post_ez.
    all: try (lazymatch goal with HL : log_flat ?E _ |- _ =>
                repeat match goal with H' : context [E] |- _ => clear H' end; try clear E end).
    all: kx_runFLd [587076] 200%nat (repeat true 4096)
      [KZRange B 4096 (2^47); KZRange l2 1 (2^26); KZRange p 1 (2^26); KZRange cq2 0 7; KZRange cr2 0 7;
       KZRange (8 * cq2 + cr2) 0 63; KZRange (l2 - p - cq2) 8 (2^26); KZRange (l2 - p) 8 (2^26);
       KZRange DT 4096 (2^47); KZRange (bv_unsigned sp) 8192 (2^47); KZWord (bv_unsigned sp + -280) 8 (DT + 4);
       KZWr (bv_unsigned sp + -384) 120; KZWr (bv_unsigned sp + -184) 40; KZDisj B l2 (bv_unsigned sp + -384) 384]
      [(B, l2)] [(bv_unsigned sp + -384, 384); (B, l2)] [(B, l2)].
    all: try (z4m_flat cq2 FSA FSA FSA FSA).
    all: try z4brx.
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => lia end).
    all: z4f2_post MU TB DTH SRC OBb BD4 BD3 BD1 FRS SPL BD2 FB buf OBL K.
  - unfold z4R_pre in PRE. destruct PRE as (P0 & P1 & P4 & P5 & P6 & P7).
    destruct r1; cbn [z4R_fl] in *; cbn iota.
    all: kx_runFLd [587608] 40%nat (repeat true 4096)
      [KZRange B 4096 (2^47); KZRange o2 0 7; KZRange (bv_unsigned sp) 8192 (2^47);
       KZWord (bv_unsigned sp + -152) 8 (B + 8); KZWr (bv_unsigned sp + -384) 120]
      (@nil (Z * Z)) [(bv_unsigned sp + -384, 384)] (@nil (Z * Z)).
    all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => lia end).
    all: z4f2_post MU TB DTH SRC OBb BD4 BD3 BD1 FRS SPL BD2 FB buf OBL K.
Qed.

End CANSEC1.
