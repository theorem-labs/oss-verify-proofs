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

From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_reloadi AF_huf_z4s3b AF_huf_z4s1rl_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s1rl4.

Section CANSEC1. Context {rc : runConstT}.

Lemma z4R_s3_tt : forall (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word)
    (fc : bv 32) (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (r1 r4 : bool),
  z4R_s4_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    r1 true true r4 ->
  z4R_s34_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    r1 true true r4.
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q r1 r4 S4.
  unfold z4R_s34_goal.
  intros AI L st LB rng_fs cells pdt SBL SBH rstk mm l1 l2 l3 e1 e2 e3 e4 o1 b1 o2 b2 o3 cq3 cr3 o4 cq4 cr4 c1 c2 k3 k4
    jp1 jp2 jp3 jp4 w0 l13 l14 l15 l16 v15 v22 v27 v28 v29 v31 CTX LY PRE3 PRE4 SF K.
  cbn iota.
  pose proof LY as LY0.
  destruct LY as (HL1 & HL2 & HL3 & HN & HD6 & HSG).
  unfold z4R_pre in PRE3. cbn iota in PRE3. destruct PRE3 as (O3a & [O3b|(O3c & O3d)] & C3r & C3q & C3b & O3r); [lia|].
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
  pose proof (munch_refl [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -224, bv_unsigned sp + -224 + 40);
                          (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  destruct (z4R_srcwin AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk mm CTX MU
    ltac:(lia) ltac:(lia)) as (USS & SBA & SBL1 & SBL2 & SBR & SSR).
  pose proof (z4R_srctop AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk CTX
    ltac:(lia)) as SBT.
  pose proof (z4_bytes_sub mm SS src (6 + l1 + l2 + o3 - 8) 16 BSS ltac:(lia) ltac:(lia) ltac:(lia)) as BSL.
  replace (SS + (6 + l1 + l2 + o3 - 8)) with (SS + 6 + l1 + l2 + o3 - 8) in BSL by lia.
  pose proof (unpoisoned_sub mm SS (SS + zlen src) (SS + 6 + l1 + l2 + o3 - 8) (SS + 6 + l1 + l2 + o3 - 8 + 16) USS
    ltac:(lia) ltac:(lia)) as USL.
  assert (RSL : rng RNG (SS + 6 + l1 + l2 + o3 - 8) 16) by (eapply rng_sub; [exact SSR | lia | lia]).
  pose proof (SysStep.rw_cells_wr_at bsegs mm _ _ 120 SPL ltac:(rewrite SPLS; lia)) as WSP.
  pose proof (SysStep.rw_cells_wr_at bsegs mm _ _ 40 B3 ltac:(rewrite B3S; lia)) as WB3.
  assert (AS3 : KXGoM.apart (bv_unsigned sp + -400) 400 ASHOFF (ATOP / 8 + 1))
    by (unfold KXGoM.apart, ASHOFF; right; Z.div_mod_to_equations; lia).
  assert (TF : KXGoM.apart (SS + 6 + l1 + l2 + o3 - 8) 16 (bv_unsigned sp + -400) 400) by (unfold KXGoM.apart; left; lia).
  remember (8 * cq3 + cr3) as b3 eqn:EB3.
  unfold AZ4_SB in *.
  kx_runFLd [587288; 587628] 300%nat (repeat true 4096)
    [KZRange (bv_unsigned sp) 8192 (2^47); KZRange SS 4096 (2^47); KZRange DT 4096 (2^47); KZRange o3 8 (2^26);
     KZRange l1 1 (2^26); KZRange l2 1 (2^26); KZRange b3 0 56; KZRange (l3 - o3) 8 (2^26);
     KZRange (SS + 6 + l1 + l2 + o3) 4096 (2^47);
     KZWord (bv_unsigned sp + -192) 8 (SS + (6 + l1 + l2) + 8); KZWord (bv_unsigned sp + -280) 8 (DT + 4);
     KZWr (bv_unsigned sp + -384) 120; KZWr (bv_unsigned sp + -224) 40]
    [(SS + 6 + l1 + l2 + o3 - 8, 16)] [(bv_unsigned sp + -400, 400)] [(SS + 6 + l1 + l2 + o3 - 8, 16)].
  all: try (lazymatch goal with |- _ <= _ < _ => lia | |- _ <= _ <= _ => lia end).
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => first [z4r_brx | z4r_srl; z4br] end).
  all: try (lazymatch goal with |- exists bs, rdn _ _ _ _ = Some bs =>
       eapply kx_rd_bytes_at; [lia | exact BSL | first [z4r_addr | unfold estart; z4r_lin tl] | first [z4r_addr | unfold estart; rewrite ?length_map; z4r_lin tl]] end).
  all: try (lazymatch goal with |- accP _ _ _ => clear - AS3 TF RSL SBT SBL1 SBL2 HN HL1 HL2 HL3 O3a O3c O3d C3r C3q C3b EB3 FP1 FP2 ATR FS1 FS2 NSM ALY SPT; z4r_acc RSL end).
  all: try (lazymatch goal with |- flat _ _ _ /\ _ => clear - AS3 TF RSL SBT SBL1 SBL2 HN HL1 HL2 HL3 O3a O3c O3d C3r C3q C3b EB3 FP1 FP2 ATR FS1 FS2 NSM ALY SPT; z4r_flat tl AS3 AS3 TF TF end).
  all: try z4r_stok.
  kx_post_regs_keep.
  unfold SPD in SPL. kx_cells_split SPL. unfold BD4A in B3. kx_cells_split B3. kx_cells_post.
  kx_munch MUW. kx_post_mem_free.
  kx_frame B4. kx_frame B2. kx_frame B1.
  lazymatch goal with HL : log_flat ?E ?l |- context [mem_denot ?E ?m ?l] =>
    destruct (kx_u8arr_ex bsegs E m l DST buf BUF HL) as (buf' & BUF' & BUFL') end.
  z4post_ez.
  cbn [mem_denot] in *.
  assert (HAND : edenot KXE (EAlu ALU_AND (EVar 23) (ELit 7)) = Z_to_bv 64 cr3).
  { apply bv_eq. cbn [edenot]. rewrite u_and64.
    assert (EV : ev KXE 23 = Z_to_bv 64 b3) by reflexivity. rewrite EV, !Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus. rewrite !(Z.mod_small _ (2 ^ Z.of_N 64)) by (change (2 ^ Z.of_N 64) with (2^64); lia).
    change 7 with (Z.ones 3). rewrite Z.land_ones by lia. subst b3. Z.div_mod_to_equations; lia. }
  rewrite (z4_srlw3 KXE (EVar 23) b3) in * by (first [reflexivity | lia]).
  rewrite HAND in *.
  assert (S8 : bv_unsigned (Z_to_bv 64 (b3 / 8)) = cq3).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
    subst b3. rewrite Z.mod_small; Z.div_mod_to_equations; lia. }
  rewrite S8 in *.
  lazymatch goal with |- context [Z_to_bv 64 (SS + (l1 + (l2 + ?x)) + 6)] =>
    replace (SS + (l1 + (l2 + x)) + 6) with (SS + 6 + l1 + l2 + (o3 - cq3)) by lia end.
  repeat match goal with H : context [?s + (l1 + (l2 + (o3 + ?y))) + 6] |- _ =>
    replace (s + (l1 + (l2 + (o3 + y))) + 6) with (s + (6 + l1 + l2) + (o3 - cq3)) in H by lia end.
  eapply (S4 AI L st LB rng_fs cells pdt SBL SBH rstk _ l1 l2 l3 e1 e2 e3 e4 o1 b1 o2 b2 (o3 - cq3) cr3 o4 cq4 cr4
            c1 c2 _ k4 jp1 jp2 jp3 jp4 w0 l13 l14 l15 l16).
  1: exact CTX. 1: exact LY0. 1: exact PRE4.
  1: eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
            cells cbs pdt SBL SBH rstk mm _ (-224)); [exact CTX | lia | lia | lia | exact SF | exact MUW | idtac .. ].
  all: try reflexivity.
  all: try assumption.
  all: try (exists buf'; split; [exact BUF' | lia]).
  all: try (unfold SPD; kx_cells_merge).
  all: try (unfold BD4A; kx_cells_merge).
  intros mm' o4' b4' c4 u10 u17 u22 u27 u31 SF' R4'.
  eapply (K mm' (o3 - cq3) cr3 o4' b4' _ c4 u10 u17 u22 u27 u31 SF'); [cbn [z4R_res]; split; reflexivity | exact R4'].
Qed.

Lemma z4R_s3_ft : forall (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word)
    (fc : bv 32) (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (r1 r4 : bool),
  z4R_s4_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    r1 false true r4 ->
  z4R_s34_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    r1 false true r4.
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q r1 r4 S4.
  unfold z4R_s34_goal.
  intros AI L st LB rng_fs cells pdt SBL SBH rstk mm l1 l2 l3 e1 e2 e3 e4 o1 b1 o2 b2 o3 cq3 cr3 o4 cq4 cr4 c1 c2 k3 k4
    jp1 jp2 jp3 jp4 w0 l13 l14 l15 l16 v15 v22 v27 v28 v29 v31 CTX LY PRE3 PRE4 SF K.
  cbn iota.
  pose proof LY as LY0.
  destruct LY as (HL1 & HL2 & HL3 & HN & HD6 & HSG).
  unfold z4R_pre in PRE3. cbn iota in PRE3. destruct PRE3 as (O3a & [O3b|(O3c & O3d)] & C3r & C3q & C3b & O3r); [lia|].
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
  pose proof (munch_refl [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -224, bv_unsigned sp + -224 + 40);
                          (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  destruct (z4R_srcwin AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk mm CTX MU
    ltac:(lia) ltac:(lia)) as (USS & SBA & SBL1 & SBL2 & SBR & SSR).
  pose proof (z4R_srctop AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk CTX
    ltac:(lia)) as SBT.
  pose proof (z4_bytes_sub mm SS src (6 + l1 + l2 + o3 - 8) 16 BSS ltac:(lia) ltac:(lia) ltac:(lia)) as BSL.
  replace (SS + (6 + l1 + l2 + o3 - 8)) with (SS + 6 + l1 + l2 + o3 - 8) in BSL by lia.
  pose proof (unpoisoned_sub mm SS (SS + zlen src) (SS + 6 + l1 + l2 + o3 - 8) (SS + 6 + l1 + l2 + o3 - 8 + 16) USS
    ltac:(lia) ltac:(lia)) as USL.
  assert (RSL : rng RNG (SS + 6 + l1 + l2 + o3 - 8) 16) by (eapply rng_sub; [exact SSR | lia | lia]).
  pose proof (SysStep.rw_cells_wr_at bsegs mm _ _ 120 SPL ltac:(rewrite SPLS; lia)) as WSP.
  pose proof (SysStep.rw_cells_wr_at bsegs mm _ _ 40 B3 ltac:(rewrite B3S; lia)) as WB3.
  assert (AS3 : KXGoM.apart (bv_unsigned sp + -400) 400 ASHOFF (ATOP / 8 + 1))
    by (unfold KXGoM.apart, ASHOFF; right; Z.div_mod_to_equations; lia).
  assert (TF : KXGoM.apart (SS + 6 + l1 + l2 + o3 - 8) 16 (bv_unsigned sp + -400) 400) by (unfold KXGoM.apart; left; lia).
  remember (8 * cq3 + cr3) as b3 eqn:EB3.
  unfold AZ4_SB in *.
  kx_runFLd [587288; 587628] 300%nat (repeat true 4096)
    [KZRange (bv_unsigned sp) 8192 (2^47); KZRange SS 4096 (2^47); KZRange DT 4096 (2^47); KZRange o3 8 (2^26);
     KZRange l1 1 (2^26); KZRange l2 1 (2^26); KZRange b3 0 56; KZRange (l3 - o3) 8 (2^26);
     KZRange (SS + 6 + l1 + l2 + o3) 4096 (2^47);
     KZWord (bv_unsigned sp + -192) 8 (SS + (6 + l1 + l2) + 8); KZWord (bv_unsigned sp + -280) 8 (DT + 4);
     KZWr (bv_unsigned sp + -384) 120; KZWr (bv_unsigned sp + -224) 40]
    [(SS + 6 + l1 + l2 + o3 - 8, 16)] [(bv_unsigned sp + -400, 400)] [(SS + 6 + l1 + l2 + o3 - 8, 16)].
  all: try (lazymatch goal with |- _ <= _ < _ => lia | |- _ <= _ <= _ => lia end).
  all: try (lazymatch goal with |- branch_taken _ _ _ = _ => first [z4r_brx | z4r_srl; z4br] end).
  all: try (lazymatch goal with |- exists bs, rdn _ _ _ _ = Some bs =>
       eapply kx_rd_bytes_at; [lia | exact BSL | first [z4r_addr | unfold estart; z4r_lin tl] | first [z4r_addr | unfold estart; rewrite ?length_map; z4r_lin tl]] end).
  all: try (lazymatch goal with |- accP _ _ _ => clear - AS3 TF RSL SBT SBL1 SBL2 HN HL1 HL2 HL3 O3a O3c O3d C3r C3q C3b EB3 FP1 FP2 ATR FS1 FS2 NSM ALY SPT; z4r_acc RSL end).
  all: try (lazymatch goal with |- flat _ _ _ /\ _ => clear - AS3 TF RSL SBT SBL1 SBL2 HN HL1 HL2 HL3 O3a O3c O3d C3r C3q C3b EB3 FP1 FP2 ATR FS1 FS2 NSM ALY SPT; z4r_flat tl AS3 AS3 TF TF end).
  all: try z4r_stok.
  kx_post_regs_keep.
  unfold SPD in SPL. kx_cells_split SPL. unfold BD4A in B3. kx_cells_split B3. kx_cells_post.
  kx_munch MUW. kx_post_mem_free.
  kx_frame B4. kx_frame B2. kx_frame B1.
  lazymatch goal with HL : log_flat ?E ?l |- context [mem_denot ?E ?m ?l] =>
    destruct (kx_u8arr_ex bsegs E m l DST buf BUF HL) as (buf' & BUF' & BUFL') end.
  z4post_ez.
  cbn [mem_denot] in *.
  assert (HAND : edenot KXE (EAlu ALU_AND (EVar 23) (ELit 7)) = Z_to_bv 64 cr3).
  { apply bv_eq. cbn [edenot]. rewrite u_and64.
    assert (EV : ev KXE 23 = Z_to_bv 64 b3) by reflexivity. rewrite EV, !Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus. rewrite !(Z.mod_small _ (2 ^ Z.of_N 64)) by (change (2 ^ Z.of_N 64) with (2^64); lia).
    change 7 with (Z.ones 3). rewrite Z.land_ones by lia. subst b3. Z.div_mod_to_equations; lia. }
  rewrite (z4_srlw3 KXE (EVar 23) b3) in * by (first [reflexivity | lia]).
  rewrite HAND in *.
  assert (S8 : bv_unsigned (Z_to_bv 64 (b3 / 8)) = cq3).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
    subst b3. rewrite Z.mod_small; Z.div_mod_to_equations; lia. }
  rewrite S8 in *.
  lazymatch goal with |- context [Z_to_bv 64 (SS + (l1 + (l2 + ?x)) + 6)] =>
    replace (SS + (l1 + (l2 + x)) + 6) with (SS + 6 + l1 + l2 + (o3 - cq3)) by lia end.
  repeat match goal with H : context [?s + (l1 + (l2 + (o3 + ?y))) + 6] |- _ =>
    replace (s + (l1 + (l2 + (o3 + y))) + 6) with (s + (6 + l1 + l2) + (o3 - cq3)) in H by lia end.
  eapply (S4 AI L st LB rng_fs cells pdt SBL SBH rstk _ l1 l2 l3 e1 e2 e3 e4 o1 b1 o2 b2 (o3 - cq3) cr3 o4 cq4 cr4
            c1 c2 _ k4 jp1 jp2 jp3 jp4 w0 l13 l14 l15 l16).
  1: exact CTX. 1: exact LY0. 1: exact PRE4.
  1: eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
            cells cbs pdt SBL SBH rstk mm _ (-224)); [exact CTX | lia | lia | lia | exact SF | exact MUW | idtac .. ].
  all: try reflexivity.
  all: try assumption.
  all: try (exists buf'; split; [exact BUF' | lia]).
  all: try (unfold SPD; kx_cells_merge).
  all: try (unfold BD4A; kx_cells_merge).
  intros mm' o4' b4' c4 u10 u17 u22 u27 u31 SF' R4'.
  eapply (K mm' (o3 - cq3) cr3 o4' b4' _ c4 u10 u17 u22 u27 u31 SF'); [cbn [z4R_res]; split; reflexivity | exact R4'].
Qed.

Lemma z4R_s3_false : forall (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word)
    (fc : bv 32) (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (r1 r2 r4 : bool),
  z4R_s4_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    r1 r2 false r4 ->
  z4R_s34_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    r1 r2 false r4.
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q r1 r2 r4 S4.
  unfold z4R_s34_goal.
  intros AI L st LB rng_fs cells pdt SBL SBH rstk mm l1 l2 l3 e1 e2 e3 e4 o1 b1 o2 b2 o3 cq3 cr3 o4 cq4 cr4 c1 c2 k3 k4
    jp1 jp2 jp3 jp4 w0 l13 l14 l15 l16 v15 v22 v27 v28 v29 v31 CTX LY PRE3 PRE4 SF K.
  pose proof LY as LY0.
  destruct LY as (HL1 & HL2 & HL3 & HN & HD6 & HSG).
  pose proof PRE3 as PRE3'.
  unfold z4R_pre in PRE3'. cbn iota in PRE3'. destruct PRE3' as (O3a & O3b & C3r & C3q & C3b & O3r).
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ltac:(lia))
    as (FD1 & FD2 & FD3 & FT1 & FT2 & FSS & FP1 & FP2 & FRN).
  destruct (FSS ltac:(lia)) as (FS1 & FS2).
  pose proof CTX as CTX0.
  destruct CTX0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2
    & DJ3 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof (AI_layout AI _ _ _ _ _ AH) as ALY.
  unfold AIMG_HI in FD1, FT1, FS1.
  clear AH NFK ABL HDT TOK ECB LCB DSTF BYS SRCB DJ1 DJ2 DJ3 LOA LOS SP16 TPA HINV RCL RLO RHI RRL RRS
    WSK WIM WIS WFS FSS.
  pose proof SF as SF0.
  destruct SF0 as ((buf & BUF & BUFL) & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S
    & FRM & MI & MU & WM).
  assert (FRN' : rng RNG (bv_unsigned sp + -400) 400) by (replace (bv_unsigned sp + -400) with (bv_unsigned sp - 400) by lia; exact FRN).
  pose proof (SysStep.rw_cells_wr_at bsegs mm _ _ 120 SPL ltac:(rewrite SPLS; lia)) as WSP.
  pose proof (SysStep.rw_cells_wr_at bsegs mm _ _ 40 B3 ltac:(rewrite B3S; lia)) as WB3.
  unfold AZ4_SB in *.
  destruct r2; cbn iota.
  - kx_runFLd [587628] 40%nat (repeat true 4096)
      [KZRange (bv_unsigned sp) 8192 (2^47); KZRange SS 4096 (2^47); KZRange l1 1 (2^26); KZRange l2 1 (2^26);
       KZRange o3 0 7; KZWord (bv_unsigned sp + -192) 8 (SS + (6 + l1 + l2) + 8)]
      (@nil (Z * Z)) [(bv_unsigned sp + -400, 400)] (@nil (Z * Z)).
    all: try (lazymatch goal with |- _ <= _ < _ => lia | |- _ <= _ <= _ => lia end).
    all: kx_post_regs_keep.
    all: z4post_ez.
    all: cbn [mem_denot] in *.
    match goal with |- context [?s + (l1 + (l2 + o3)) + 6] => replace (s + (l1 + (l2 + o3)) + 6) with (s + 6 + l1 + l2 + o3) by lia end.
    eapply (S4 AI L st LB rng_fs cells pdt SBL SBH rstk _ l1 l2 l3 e1 e2 e3 e4 o1 b1 o2 b2 o3 (8 * cq3 + cr3) o4 cq4 cr4
                  c1 c2 k3 k4 jp1 jp2 jp3 jp4 w0 l13 l14 l15 l16).
    1: exact CTX. 1: exact LY0. 1: exact PRE4. 1: exact SF.
    intros mm' o4' b4' c4 u10 u17 u22 u27 u31 SF' R4'.
    eapply (K mm' o3 (8 * cq3 + cr3) o4' b4' k3 c4 u10 u17 u22 u27 u31 SF' ltac:(cbn [z4R_res]; split; reflexivity) R4').

  - kx_runFLd [587628] 40%nat (repeat true 4096)
      [KZRange (bv_unsigned sp) 8192 (2^47); KZRange SS 4096 (2^47); KZRange l1 1 (2^26); KZRange l2 1 (2^26);
       KZRange o3 0 7; KZWord (bv_unsigned sp + -192) 8 (SS + (6 + l1 + l2) + 8)]
      (@nil (Z * Z)) [(bv_unsigned sp + -400, 400)] (@nil (Z * Z)).
    all: try (lazymatch goal with |- _ <= _ < _ => lia | |- _ <= _ <= _ => lia end).
    all: kx_post_regs_keep.
    all: z4post_ez.
    all: cbn [mem_denot] in *.
    match goal with |- context [?s + (l1 + (l2 + o3)) + 6] => replace (s + (l1 + (l2 + o3)) + 6) with (s + 6 + l1 + l2 + o3) by lia end.
    eapply (S4 AI L st LB rng_fs cells pdt SBL SBH rstk _ l1 l2 l3 e1 e2 e3 e4 o1 b1 o2 b2 o3 (8 * cq3 + cr3) o4 cq4 cr4
                  c1 c2 k3 k4 jp1 jp2 jp3 jp4 w0 l13 l14 l15 l16).
    1: exact CTX. 1: exact LY0. 1: exact PRE4. 1: exact SF.
    intros mm' o4' b4' c4 u10 u17 u22 u27 u31 SF' R4'.
    eapply (K mm' o3 (8 * cq3 + cr3) o4' b4' k3 c4 u10 u17 u22 u27 u31 SF' ltac:(cbn [z4R_res]; split; reflexivity) R4').
Qed.

Lemma z4R_s34 : forall RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q
    r1 r2 r3 r4,
  z4R_s34_goal RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q r1 r2 r3 r4.
Proof.
  intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q r1 r2 r3 r4.
  destruct r3; [destruct r2 |].
  - apply z4R_s3_tt; apply z4R_s4.
  - apply z4R_s3_ft; apply z4R_s4.
  - apply z4R_s3_false; apply z4R_s4.
Qed.

End CANSEC1.
