(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfR1.v
   (a working branch 0ddf65fd8cc) for libreac/fuzz_disco's ASan image (G9 row R9-A-instance; the row text names
   lib/A/RT_pf_disco_inst.v, the file name is a Theorem Labs lane's ruling). New file. *)
(* fuzz_disco's snprintf route at disco's own pieces pf_disco_piece = literals, %s, %d, %02x, %llu (lib/Rt/PfFacts.v:87),
   as FMsnprintfFmI.fm_snprintf_gxaP at PK = pf_disco_piece, every piece with its four arms (the three seam arms of
   FMgxaSeamPf.v and the printf_common arm of RT_pf_sh.v). Each arm is its row's lemma, taken by path:
     literals / %s   FMgxaSeamPf seam_*_arm_lit / _ps;  RT_pf_sh pcom_pcx_arm_lit / _ps
     %d              FMpfArmPdSeam;                     RT_pf_d pcom_pcx_arm_Pd
     %02x            FMgxaSeam02x;                      RT_pf_02x pcom_pcx_arm_px02
     %llu            FMpfArmPlluSeam;                   RT_pf_llu pcom_pcx_arm_llu
   %c, %04x and %.*s are not disco pieces (pf_disco_piece is False on them).
   Then disco's family: SnFF.FF_disco disco_fmt_lo disco_fmt_hi (lib/A/Rt/SnprintfConsts.v 0x102e0 / 0x22fac) lies inside
   FMsnprintfFmI.FF_fmP pf_disco_piece (formats in [0x10000, 0xa1198)), so the top holds at FF_disco by one family
   weakening (the family occurs only as a premise of sh_asnprintf_realizesU). Rule 24: no function is proved here. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AB1v AF0m FMH_Base FMsnprintfImg.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnUpoison PfFacts SnShared SnSx SnFF.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require FMgxaSeamPf RT_pf_sh FMsnprintfFm FMsnprintfCr FMsnprintfFmI.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require
FMpfArmPdSeam FMgxaSeam02x FMpfArmPlluSeam RT_pf_d RT_pf_02x RT_pf_llu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX Require G_printf_core_common.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.I Require Import RecAsanVfA.
Import ListNotations.
Local Open Scope Z_scope.

Module GXC := OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
Module SPf := OSSVerify.Proofs.libreac.fuzz_disco.lib.A.FMgxaSeamPf.
Module RTS := OSSVerify.Proofs.libreac.fuzz_disco.lib.A.RT_pf_sh.
Module FmI := OSSVerify.Proofs.libreac.fuzz_disco.lib.A.FMsnprintfFmI.

(* ---- the four arms of every disco piece ---- *)
Lemma disco_text_arms : forall p, pf_disco_piece p -> SPf.seam_text_arm p.
Proof.
intros [b| | | | | | |] H; cbn in H; try contradiction.
- apply SPf.seam_text_arm_lit.
- exact FMpfArmPdSeam.seam_text_arm_pd.
- exact FMgxaSeam02x.seam_text_arm_px02.
- exact FMpfArmPlluSeam.seam_text_arm_pllu.
- exact SPf.seam_text_arm_ps.
Qed.
Lemma disco_pargs_arms : forall p, pf_disco_piece p -> SPf.seam_pargs_arm p.
Proof.
intros [b| | | | | | |] H; cbn in H; try contradiction.
- apply SPf.seam_pargs_arm_lit.
- exact FMpfArmPdSeam.seam_pargs_arm_pd.
- exact FMgxaSeam02x.seam_pargs_arm_px02.
- exact FMpfArmPlluSeam.seam_pargs_arm_pllu.
- exact SPf.seam_pargs_arm_ps.
Qed.
Lemma disco_bytes_arms : forall p, pf_disco_piece p -> SPf.seam_bytes_arm p.
Proof.
intros [b| | | | | | |] H; cbn in H; try contradiction.
- apply SPf.seam_bytes_arm_lit.
- exact FMpfArmPdSeam.seam_bytes_arm_pd.
- exact FMgxaSeam02x.seam_bytes_arm_px02.
- exact FMpfArmPlluSeam.seam_bytes_arm_pllu.
- exact SPf.seam_bytes_arm_ps.
Qed.
Lemma disco_pcx_arms : forall p, pf_disco_piece p -> RTS.pcom_pcx_arm p.
Proof.
intros [b| | | | | | |] H; cbn in H; try contradiction.
- apply RTS.pcom_pcx_arm_lit.
- exact RT_pf_d.pcom_pcx_arm_Pd.
- exact RT_pf_02x.pcom_pcx_arm_px02.
- exact RT_pf_llu.pcom_pcx_arm_llu.
- exact RTS.pcom_pcx_arm_ps.
Qed.

(* ---- disco's family inside FmI's family at disco's pieces ---- *)
Lemma FF_disco_fmP : forall rd rs f ws T,
  FF_disco disco_fmt_lo disco_fmt_hi rd rs f ws T -> FmI.FF_fmP pf_disco_piece rd rs f ws T.
Proof.
intros rd rs f ws T (fmt & ps & args & Hf & Hp & Hk & Ha & Ht & Hq & Hlo & Hhi & Hsl & Hne & Ham).
unfold disco_fmt_lo in Hlo. unfold disco_fmt_hi in Hhi.
exists fmt, ps, args. repeat (split; [assumption|]).
split; [lia|]. split; [lia|]. repeat (split; [assumption|]). exact Ham.
Qed.

(* the family occurs only as a premise of snprintf's contract *)
Section ff. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma sh_asnprintf_realizesU_ff : forall (segs : list Segment) (B : asyms) (FF1 FF2 : fmt_fam)
  (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (pc : Z),
  (forall rd rs f ws T, FF2 rd rs f ws T -> FF1 rd rs f ws T) ->
  sh_asnprintf_realizesU segs B FF1 K gc gv img_lo img_hi cr pc ->
  sh_asnprintf_realizesU segs B FF2 K gc gv img_lo img_hi cr pc.
Proof.
intros segs B FF1 FF2 K gc gv img_lo img_hi cr pc HS HU. unfold sh_asnprintf_realizesU in *.
intros; eapply HU; eauto.
Qed.
End ff.

(* ---- disco's snprintf on the GXA route, at disco's pieces and format range ---- *)
#[local] Existing Instance N_img_asan_vf.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem disco_snprintf_gxa_r1 : forall B, AR_laws tfibsegs B -> TfibSyms B ->
  forall img_lo img_hi K, img_lo <= 65536 -> @GXC.GLOBALS_TOP N_img_asan_vf <= img_hi ->
  FMsnprintfFm.fm_glue_img + FMsnprintfFm.GXA_VF_DEPTH <= K ->
  sh_asnprintf_realizesU tfibsegs B (FF_disco disco_fmt_lo disco_fmt_hi) K FM_GOT_canary FM_canary
    img_lo img_hi FMsnprintfCr.fm_cr PC_snprintf.
Proof.
intros B LAWS TB img_lo img_hi K Hlo Hhi HK.
apply (sh_asnprintf_realizesU_ff tfibsegs B (FmI.FF_fmP pf_disco_piece) _ K FM_GOT_canary FM_canary
  img_lo img_hi FMsnprintfCr.fm_cr PC_snprintf FF_disco_fmP).
exact (FmI.fm_snprintf_gxaP B LAWS TB pf_disco_piece disco_text_arms disco_pargs_arms disco_bytes_arms disco_pcx_arms
  img_lo img_hi K Hlo Hhi HK).
Qed.
(* the AR form (no user-poisoned range) *)
Corollary disco_snprintf_gxa_r1_AR : forall B, AR_laws tfibsegs B -> TfibSyms B ->
  forall img_lo img_hi K, img_lo <= 65536 -> @GXC.GLOBALS_TOP N_img_asan_vf <= img_hi ->
  FMsnprintfFm.fm_glue_img + FMsnprintfFm.GXA_VF_DEPTH <= K ->
  sh_asnprintf_realizes tfibsegs B (FF_disco disco_fmt_lo disco_fmt_hi) K FM_GOT_canary FM_canary
    img_lo img_hi FMsnprintfCr.fm_cr PC_snprintf.
Proof.
intros B LAWS TB img_lo img_hi K Hlo Hhi HK.
apply sh_asnprintf_of_U. exact (disco_snprintf_gxa_r1 B LAWS TB img_lo img_hi K Hlo Hhi HK).
Qed.
End f.
