(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MnRefillB3Rcf.v (commit 3cae605a900a, blob f1a5fad85f07) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from cgif_file_fuzzer asan-ubsan ce511d541cda (pin 1c29845fe605), the cf layer at part 3c; module paths changed; 2 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import YFk5cf YFk8cf YFkbcf YFkkcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre YGcfRmodel YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseAG AGif0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA AGImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstRefill.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import MnRefillSeamcf.
Import ListNotations.
Open Scope Z_scope.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Local Open Scope am_scope.
Variable B : asyms.
Variable IOK : Z -> Prop.
Hypothesis TS : TfibSyms B.
Hypothesis HIOK : forall inst, IOK inst -> inst = A_ALLOCATOR.
Hypothesis HIN : refill_B3_inner_cf.

Theorem refill_B3_entry_cf_ok : @refill_B3_entry_cf fx rc ci cp AImg_A AGImg_A B IOK.
Proof.
intros Hp inst ly S W regs0 mem0 md0 c HS HRO HHULL HC [Hinited Hfew].
destruct HS as (HARX & HWT & HQL & HBR & HER & HcR & Hchunks).
destruct HC as (Hra & Hra4096 & Hal & HloW & Hhi & HpresW & Hgp & Htp & Ha0 & Ha1 & Ha2 & Ha3).
pose proof (ARX_cf_iok B IOK Hp inst ly S W mem0 md0 HARX) as HI. rewrite (HIOK inst HI) in Ha2.
pose proof (ARX_cf_ARcf B IOK Hp inst ly S W mem0 md0 HARX) as HAR.
pose proof (ARX_cf_xsm B IOK Hp inst ly S W mem0 md0 HARX) as HXSM.
pose proof (ARX_cf_exh B IOK Hp inst ly S W mem0 md0 HARX) as HEXH.
pose proof (ARX_cf_errb B IOK Hp inst ly S W mem0 md0 HARX) as HERRB.
change (YG0ncf.ARcf tfibsegs B ly S Hp W mem0 md0) in HAR.
pose proof (proj1 HAR) as HARm.
assert (LY : layout_ok ly) by exact (amc_layout _ _ _ _ _ HARm).
assert (IMG : img_cover ly).
{ pose proof (proj1 (proj2 HAR)) as L. split.
  - destruct (alc_img _ _ _ _ L Asan.Asan_segment_000 ltac:(left; reflexivity)) as [H _].
    cbn in H. unfold TFIB_IMG_LO. lia.
  - destruct (alc_img _ _ _ _ L Asan.Asan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H].
    cbn in H. unfold TFIB_IMG_END. lia. }
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (amc_tsd _ _ _ _ _ HARm); exact (ts_tsd B TS)).
change (getr regs0 4 = w64 TFIB_TP) in Htp.
unfold spZ, raZ in *.
pose proof (REP_W_le c) as [RW0 RW1].
set (sp0 := bv_unsigned (getr regs0 2)) in *.
assert (Hsp : ly_stk_lo ly + RSTACK <= sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0) by (repeat split; lia).
assert (Hpres0R : forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem0 a) by (intros a Ha; apply HpresW; lia).
set (maxc := max_cached c). set (n := maxc / 2). set (nf := fa_len (rg_free (reg S c))). set (mf := rg_mapped_fa (reg S c)).
set (au := rg_alloc_user (reg S c)). set (mu := rg_mapped_user (reg S c)). set (csz := class_size c). set (mat0 := m_vm_materialized md0).
assert (Hmax : maxc = max_cached c) by reflexivity. assert (Hn : n = maxc / 2) by reflexivity. assert (Hcsz : csz = class_size c) by reflexivity.
assert (Hnf_def : nf = fa_len (rg_free (reg S c))) by reflexivity. assert (Hmf_def : mf = rg_mapped_fa (reg S c)) by reflexivity.
assert (Hau_def : au = rg_alloc_user (reg S c)) by reflexivity. assert (Hmu_def : mu = rg_mapped_user (reg S c)) by reflexivity.
assert (Hnlt : nf < n) by exact Hfew.
assert (J0 : 0 <= 0 < 2 ^ 8) by lia.
pose proof (YFkkcf.Hnf' W ly regs0 mem0 c maxc nf mf au mu 0 HcR J0 Hsp B S Hp HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hnf.
pose proof (YFkkcf.Hmf' W ly regs0 mem0 c maxc nf mf au mu 0 HcR J0 Hsp B S Hp HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hmf.
pose proof (YFkkcf.Hmu' W ly regs0 mem0 c maxc nf mf au mu 0 HcR J0 Hsp B S Hp HARm Hnf_def Hmf_def Hau_def Hmu_def) as Hmu.
pose proof (YFkkcf.Hcarved' W ly mem0 c au mu HcR B S Hp HARm Hau_def Hmu_def) as Hcarved.
pose proof (YFkkcf.Hau_al' W ly mem0 c au csz HcR Hcsz B S Hp HARm Hau_def) as Hau_al.
set (need := n - nf). set (tot := au + need * csz). set (adr := @YFk5cf.RBv ly c + mu). set (sha := YFk5cf.SHBv + adr / 8).
set (mu2 := mu + kUserMapSize). set (nce := (mu - au) / csz). set (ncg := (mu2 - au) / csz). set (nfe := nf + nce). set (nfg := nf + ncg).
set (fadr := @YFk5cf.FAv ly c + mf). set (shf := YFk5cf.SHBv + fadr / 8). set (mf2 := mf + kFreeArrayMapSize).
set (aue := au + nce * csz). set (aug := au + ncg * csz).
assert (Hneed : need = n - nf) by reflexivity. assert (Htot : tot = au + need * csz) by reflexivity.
assert (Hadr : adr = @YFk5cf.RBv ly c + mu) by reflexivity.
assert (Hsha : sha = YFk5cf.SHBv + adr / 8) by reflexivity. assert (Hmu2 : mu2 = mu + kUserMapSize) by reflexivity.
assert (Hnce : nce = (mu - au) / csz) by reflexivity. assert (Hncg : ncg = (mu2 - au) / csz) by reflexivity.
assert (Hnfe : nfe = nf + nce) by reflexivity. assert (Hnfg : nfg = nf + ncg) by reflexivity.
assert (Hfadr : fadr = @YFk5cf.FAv ly c + mf) by reflexivity. assert (Hshf : shf = YFk5cf.SHBv + fadr / 8) by reflexivity.
assert (Hmf2 : mf2 = mf + kFreeArrayMapSize) by reflexivity. assert (Haue : aue = au + nce * csz) by reflexivity.
assert (Haug : aug = au + ncg * csz) by reflexivity.
destruct (YFkkcf.junk_valuesR W ly regs0 mem0 c maxc n nf mf au mu csz 0 IMG LY HcR Hmax Hn Hcsz J0 Hsp B S Hp HARm Hnf_def Hmf_def Hau_def Hmu_def)
as (j64 & jna & jnf & jsm & jm1 & jm2 & jex & [Hj64 Hj64v] & [Hjna Hjnav] & [Hjnf Hjnfv] & [Hjsm Hjsmv] & [Hjm1 Hjm1v] & [Hjm2 Hjm2v] & [Hjex Hjexv]).
pose proof (fun a => YFkkcf.HslotPres' W ly regs0 mem0 c maxc n nf mf au mu csz 0 IMG LY HcR Hmax Hn Hcsz J0 Hsp B S Hp HARm Hnf_def Hmf_def Hau_def Hmu_def a) as HslotPres.
pose proof (fun a => YFkkcf.HfaPres' W ly regs0 mem0 c maxc n nf mf au mu csz 0 IMG LY HcR Hmax Hn Hcsz J0 Hsp B S Hp HARm Hnf_def Hmf_def Hau_def Hmu_def a) as HfaPres.
assert (Ha1' : getr regs0 11 = w64 (@YFk5cf.Pr ly c)) by (rewrite Ha1; reflexivity).
pose proof (YFkkcf.SEEDR3_ok W ly regs0 mem0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug
  IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp Htp Ha0 Ha1' Ha2 Ha3 Hnlt Hcarved Hneed Htot Hadr Hsha Hmu2
  Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug Hpres0R B S TS HTSD Hp HARm Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def
  Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v Hjexv) as SEEDR.
replace (cfg_at im_segs ag_refill regs0 mem0 md0) with (mkCfg (mkst regs0 (w64 0x373a8) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0))
by (cbn [im_segs ag_refill AImg_A AGImg_A]; unfold cfg_at, A_Refill; subst mat0; rewrite with_vm_backing_id; reflexivity).
change (amreal tfibsegs (refill_tree_cf c S) W (mkCfg (mkst regs0 (w64 0x373a8) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0))
  (refill_leaf_core_cf B Hp ly S c W regs0 mem0 md0)).
eapply amreal_SRr_pre.
{ exact (YFkbcf.seg3J W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg
    fadr shf mf2 aue aug IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hsp Hpres0R mat0 SEEDR). }
intros W' c' _ HJ. pose proof HJ as [EW (msJ & matJ & E' & EcJ & HJrest)]. subst W'. rewrite EcJ in HJ |- *.
exact (HIN Hp W ly regs0 mem0 md0 c maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 jex need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug
  matJ msJ B S IMG LY HcR Hmax Hn Hcsz Hnf Hmf Hmu Hj64 Hjna Hjnf Hjsm Hjm1 Hjm2 Hjex Hsp ltac:(lia) Hra Hra4096 Htp Ha0 Ha1' Ha2 Ha3
  Hnlt Hcarved Hau_al Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug HJ Hpres0R HpresW HslotPres HfaPres
  TS HTSD HARm Hgp Hinited Hchunks Hnf_def Hmf_def Hau_def Hmu_def Hj64v Hjnav Hjnfv Hjsmv Hjm1v Hjm2v Hjexv HEXH HERRB
  HQL HAR HXSM HBR HER HWT HRO HHULL I).
Qed.
End e.
