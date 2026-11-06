(* reac-pw/fuzz_link image A: link_snprintf_fm, snprintf at the wrapper 0x43088 (__interceptor_trampoline_snprintf ->
   ___interceptor_snprintf 0x46f20 -> ___interceptor_vsnprintf 0x46b30 -> musl vsnprintf 0x9a50c -> wrapper 0x4307c ->
   ___interceptor_vfprintf 0x46a7c -> musl vfprintf 0x973e0 / printf_core 0x97590), for link's formats: literal bytes,
   %d and %s (LinkPfPiece.pf_link_piece), any format in [0x10000, 0xa2658) (FMsnprintfFmI.FF_fmP), with the
   destination off [img_lo, img_hi) or between the stack-guard .got word and the guard (the shared contract's
   dest_off_globals, generalized in place for the .bss site 0x82b14) and any window K >= 8160.
   It is libreac/fuzz_disco's FMsnprintfDiscoR1.v (origin/ossv/recipes 501c0d516c69) at link's pieces: the four arms
   of each piece (literal / %s: FMgxaSeamPf.v and RT_pf_sh.v; %d: FMpfArmPdSeam.v and RT_pf_d.v), then the ported
   FMsnprintfFmI.fm_snprintf_gxaP. The contract is the released shared form SnShared.sh_asnprintf_realizes
   (lib/Rt/SnShared.v), with its dest_off_globals premise given the second arm and its presence post excepting the
   destination's bytes inside the image (see SnShared.v's header).
   Beside it, at link's addresses and family, the shared contracts the chain proves on the way: printf_common at
   0x45fb4 (link_pcommon), the GXA seam at musl vfprintf 0x973e0 (link_vfprintf_seam) and the vfprintf interceptor
   0x46a7c on musl vsnprintf's FILE (link_vfprintf_icpt). Rule 24: no function is proved here. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m FMH_Base FMsnprintfImg.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import SnUpoison PfFacts SnShared SnSx SnFF.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkPfPiece.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AD2l FMgxaSeamPf RT_pf_sh RT_pf_shU FMgxaSeam FMsnprintfFm
  FMsnprintfCr FMsnprintfFmI FMsnprintfSeamI FMsnprintfSvfi FMpfArmPdSeam RT_pf_d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX Require G_printf_core_common.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA Require G_vfprintf_snf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.I Require Import RecAsanVfA.
#[local] Ltac Zify.zify_pre_hook ::= try unfold YImgTop.IMG_TOP, YImgTop.IMG_LO in *.
Import ListNotations.
Local Open Scope Z_scope.

Module GXC := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
Module GVA := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.G_vfprintf_snf.
Module SPf := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.FMgxaSeamPf.
Module RTS := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.RT_pf_sh.
Module FmI := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.FMsnprintfFmI.

(* ---- the four arms of every link piece ---- *)
Lemma link_text_arms : forall p, pf_link_piece p -> SPf.seam_text_arm p.
Proof.
intros [b| | | | | | |] H; cbn in H; try contradiction.
- apply SPf.seam_text_arm_lit.
- exact FMpfArmPdSeam.seam_text_arm_pd.
- exact SPf.seam_text_arm_ps.
Qed.
Lemma link_pargs_arms : forall p, pf_link_piece p -> SPf.seam_pargs_arm p.
Proof.
intros [b| | | | | | |] H; cbn in H; try contradiction.
- apply SPf.seam_pargs_arm_lit.
- exact FMpfArmPdSeam.seam_pargs_arm_pd.
- exact SPf.seam_pargs_arm_ps.
Qed.
Lemma link_bytes_arms : forall p, pf_link_piece p -> SPf.seam_bytes_arm p.
Proof.
intros [b| | | | | | |] H; cbn in H; try contradiction.
- apply SPf.seam_bytes_arm_lit.
- exact FMpfArmPdSeam.seam_bytes_arm_pd.
- exact SPf.seam_bytes_arm_ps.
Qed.
Lemma link_pcx_arms : forall p, pf_link_piece p -> RTS.pcom_pcx_arm p.
Proof.
intros [b| | | | | | |] H; cbn in H; try contradiction.
- apply RTS.pcom_pcx_arm_lit.
- exact RT_pf_d.pcom_pcx_arm_Pd.
- exact RTS.pcom_pcx_arm_ps.
Qed.

#[local] Existing Instance N_img_asan_vf.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- snprintf at the wrapper 0x43088 ---- *)
Theorem link_snprintf_fmU : forall B, AR_laws tfibsegs B -> PcapSyms B ->
  forall img_lo img_hi K, img_lo <= 65536 -> @GXC.GLOBALS_TOP N_img_asan_vf <= img_hi ->
  FMsnprintfFm.fm_glue_img + FMsnprintfFm.GXA_VF_DEPTH <= K ->
  sh_asnprintf_realizesU tfibsegs B (FmI.FF_fmP pf_link_piece) K FM_GOT_canary FM_canary
    img_lo img_hi FMsnprintfCr.fm_cr PC_snprintf.
Proof.
intros B LAWS TB.
exact (FmI.fm_snprintf_gxaP B LAWS TB pf_link_piece link_text_arms link_pargs_arms link_bytes_arms link_pcx_arms).
Qed.
(* the AR form (no user-poisoned range): the contract link's callers apply *)
Theorem link_snprintf_fm : forall B, AR_laws tfibsegs B -> PcapSyms B ->
  forall img_lo img_hi K, img_lo <= 65536 -> @GXC.GLOBALS_TOP N_img_asan_vf <= img_hi ->
  FMsnprintfFm.fm_glue_img + FMsnprintfFm.GXA_VF_DEPTH <= K ->
  sh_asnprintf_realizes tfibsegs B (FmI.FF_fmP pf_link_piece) K FM_GOT_canary FM_canary
    img_lo img_hi FMsnprintfCr.fm_cr PC_snprintf.
Proof.
intros B LAWS TB img_lo img_hi K Hlo Hhi HK.
apply sh_asnprintf_of_U. exact (link_snprintf_fmU B LAWS TB img_lo img_hi K Hlo Hhi HK).
Qed.

(* ---- printf_common (ctx, format, aq) at 0x45fb4, for link's pieces ---- *)
Theorem link_pcommon : forall B, AR_laws tfibsegs B -> PcapSyms B -> forall K, 2320 <= K ->
  sh_apcommon_realizesUz tfibsegs B (RTS.FF_pcomK pf_link_piece) K RT_pf_shU.PCM_CR A_PCOM.
Proof. intros B LAWS TB K HK. exact (RT_pf_shU.pcom_shzK B LAWS TB pf_link_piece link_pcx_arms K HK). Qed.

(* ---- the GXA seam: musl vfprintf 0x973e0 on musl vsnprintf's FILE (sn_write 0x9a5d8), for link's pieces ---- *)
Theorem link_vfprintf_seam : forall B, AR_laws tfibsegs B -> PcapSyms B ->
  forall K img_lo img_hi, GVA.VFA_DEPTH <= K -> img_lo <= 65536 -> @GXC.GLOBALS_TOP N_img_asan_vf <= img_hi ->
  sh_avfprintf_icpt_realizesUx tfibsegs B (pf_family_ro pf_link_piece 0x10000 0xa2658) K
    FM_GOT_canary FM_canary img_lo img_hi FMsnprintfCr.fm_cr A_SNW A_VFP.
Proof.
intros B LAWS TB K img_lo img_hi HK Hlo Hhi.
exact (FMsnprintfSeamI.fm_seam_instP B LAWS TB pf_link_piece link_text_arms link_pargs_arms link_bytes_arms
  K img_lo img_hi FMsnprintfCr.fm_cr HK Hlo Hhi FMsnprintfCr.fm_cr_ro_covered).
Qed.

(* ---- ___interceptor_vfprintf 0x46a7c on musl vsnprintf's FILE, for link's formats ---- *)
Theorem link_vfprintf_icpt : forall B, AR_laws tfibsegs B -> PcapSyms B ->
  forall img_lo img_hi, img_lo <= 65536 -> @GXC.GLOBALS_TOP N_img_asan_vf <= img_hi ->
  sh_avfprintf_icpt_realizesUx tfibsegs B (FmI.FF_fmP pf_link_piece) (0x30 + FMsnprintfFm.GXA_VF_DEPTH)
    FM_GOT_canary FM_canary img_lo img_hi FMsnprintfCr.fm_cr A_SNW A_VFPI.
Proof.
intros B LAWS TB img_lo img_hi Hlo Hhi.
assert (HV : GVA.VFA_DEPTH = FMsnprintfFm.GXA_VF_DEPTH) by (rewrite FMgxaSeam.sa_vfa_depth; reflexivity).
apply (FMsnprintfSvfi.svfi_ok B LAWS TB (FmI.FF_fmP pf_link_piece) FM_GOT_canary FM_canary img_lo img_hi
  FMsnprintfCr.fm_cr 2320 FMsnprintfFm.GXA_VF_DEPTH (0x30 + FMsnprintfFm.GXA_VF_DEPTH)
  (FmI.FF_fmP_stable64 pf_link_piece) (FmI.FF_fmP_mono pf_link_piece)).
- unfold ESTACK, FMsnprintfFm.GXA_VF_DEPTH. lia.
- lia.
- unfold FMsnprintfFm.GXA_VF_DEPTH. lia.
- apply (sh_apcommon_realizesUz_weaken tfibsegs B (RTS.FF_pcomK pf_link_piece) (FmI.FF_fmP pf_link_piece) 2320
    RT_pf_shU.PCM_CR FMsnprintfCr.fm_cr A_PCOM (FmI.FF_fmP_pcomK pf_link_piece pf_link_piece (fun p Hp => Hp))).
  + intros r1 Hr1. exists r1. split; [exact Hr1 | lia].
  + exact (link_pcommon B LAWS TB 2320 ltac:(lia)).
- apply (sh_avfprintf_icpt_realizesUx_ff tfibsegs B (pf_family_ro pf_link_piece 0x10000 0xa2658)
    (FmI.FF_fmP pf_link_piece) FMsnprintfFm.GXA_VF_DEPTH FM_GOT_canary FM_canary img_lo img_hi FMsnprintfCr.fm_cr
    A_SNW A_VFP (FmI.FF_fmP_ro pf_link_piece)).
  exact (link_vfprintf_seam B LAWS TB FMsnprintfFm.GXA_VF_DEPTH img_lo img_hi ltac:(rewrite HV; lia) Hlo Hhi).
Qed.
End f.

(* ---- at link's instance: PcapB (lib/A/AD2l.v), its laws (lib/Reusable/YG0q.v), the image [IMG_LO, IMG_TOP) ---- *)
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Corollary link_snprintf_fm_PcapB : forall K, FMsnprintfFm.fm_glue_img + FMsnprintfFm.GXA_VF_DEPTH <= K ->
  sh_asnprintf_realizes tfibsegs AD2l.PcapB (FmI.FF_fmP pf_link_piece) K FM_GOT_canary FM_canary
    YImgTop.IMG_LO YImgTop.IMG_TOP FMsnprintfCr.fm_cr PC_snprintf.
Proof.
intros K HK.
apply (link_snprintf_fm AD2l.PcapB (YG0q.AR_laws_ok tfibsegs AD2l.PcapB) AD2l.PcapB_syms).
- unfold YImgTop.IMG_LO. lia.
- rewrite FMgxaSeam.sa_globals_top. unfold YImgTop.IMG_TOP. lia.
- exact HK.
Qed.
Corollary link_pcommon_PcapB : forall K, 2320 <= K ->
  sh_apcommon_realizesUz tfibsegs AD2l.PcapB (RTS.FF_pcomK pf_link_piece) K RT_pf_shU.PCM_CR A_PCOM.
Proof. exact (link_pcommon AD2l.PcapB (YG0q.AR_laws_ok tfibsegs AD2l.PcapB) AD2l.PcapB_syms). Qed.
Corollary link_vfprintf_seam_PcapB : forall K, GVA.VFA_DEPTH <= K ->
  sh_avfprintf_icpt_realizesUx tfibsegs AD2l.PcapB (pf_family_ro pf_link_piece 0x10000 0xa2658) K
    FM_GOT_canary FM_canary YImgTop.IMG_LO YImgTop.IMG_TOP FMsnprintfCr.fm_cr A_SNW A_VFP.
Proof.
intros K HK.
apply (link_vfprintf_seam AD2l.PcapB (YG0q.AR_laws_ok tfibsegs AD2l.PcapB) AD2l.PcapB_syms K); [exact HK| |].
- unfold YImgTop.IMG_LO. lia.
- rewrite FMgxaSeam.sa_globals_top. unfold YImgTop.IMG_TOP. lia.
Qed.
Corollary link_vfprintf_icpt_PcapB :
  sh_avfprintf_icpt_realizesUx tfibsegs AD2l.PcapB (FmI.FF_fmP pf_link_piece) (0x30 + FMsnprintfFm.GXA_VF_DEPTH)
    FM_GOT_canary FM_canary YImgTop.IMG_LO YImgTop.IMG_TOP FMsnprintfCr.fm_cr A_SNW A_VFPI.
Proof.
apply (link_vfprintf_icpt AD2l.PcapB (YG0q.AR_laws_ok tfibsegs AD2l.PcapB) AD2l.PcapB_syms).
- unfold YImgTop.IMG_LO. lia.
- rewrite FMgxaSeam.sa_globals_top. unfold YImgTop.IMG_TOP. lia.
Qed.
End p.
