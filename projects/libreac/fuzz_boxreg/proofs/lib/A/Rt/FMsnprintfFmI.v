(* Modified by Theorem Labs, 2026-10: relocated from omx-clap-core/fuzz_manifest lib/A/FMsnprintfFmI.v (a working branch 3e35620c52e) to libreac/fuzz_boxreg.asan: module paths changed; 4 address numerals relocated (port_addr_check 5033540ba83b predict mode, symbol + offset); name TfibSyms -> BoxregSyms (2x; boxreg's lib/A/AF0m.v record); re-pointed Requires: FMsnprintfShared, FMsnprintfPf, FMsnprintfSx, FMupoison -> lib.A.Rt; FMH_Base -> lib.A.Rt.SnprintfFmh. At 3e35620c52e fm_snprintf_gxa_r / _r_AR are fm_snprintf_gxa / fm_snprintf_gxa_AR and take no readiness premise: FMsnprintfSeamI.fm_seam_inst closes it through FMgxaSeamFm.v. *)
(* fm.asan's snprintf over the shared contract, closed on the GXA route: FMsnprintfFm.fm_snprintf_shared instantiated at
   fm's format family FF_fm, the read-only image fm_cr (FMsnprintfCr.v), printf_common from a Theorem Labs lane
   (RT_pf_shU.pcom_shz), the FILE memset (FMsnprintfMs32.memset_icpt_realizesU) and musl vfprintf from a Theorem Labs lane's
   seam (FMsnprintfSeamI.fm_seam_inst). New file. *)
(* Modified by a Theorem Labs lane on a working branch: uses fm_vfprintf_seam_closed; READY moved to the per-call store. *)
(* Modified by a Theorem Labs lane: fm_snprintf_gxa_r / _r_AR renamed fm_snprintf_gxa / fm_snprintf_gxa_AR (no premise beyond AR_laws, BoxregSyms). *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE20 AE2y.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import FMupoison SnprintfFmh FMsnprintfImg.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import FMsnprintfPf FMsnprintfShared FMsnprintfSx.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import FMgxaSeamDef FMgxaSeamFF.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require RT_pf_sh RT_pf_shU.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require FMsnprintfMs32.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require FMgxaSeam FMsnprintfFm FMsnprintfCr FMsnprintfSeamI.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GX Require G_printf_core_common.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GXA Require G_vfprintf_snf.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import RT_IImgA.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- fm's format family ---- *)
(* a Theorem Labs lane's pf_family_ro at fm's .rodata (formats from 0x10000 up to the GOT slot sym 0x22e18 = 0x9a638) and
   a Theorem Labs lane's two further facts: a nonempty format, and every string with its NUL word in application memory *)
Definition FF_fm : fmt_fam := fun rd rs f ws T =>
  exists (fmt : list Z) (ps : list pf_piece) (args : list pf_arg),
    fmt_at rd rs f fmt /\ pf_parse fmt = Some ps /\ Forall pf_fm_piece ps /\ pf_args_asan rd rs ws args /\
    pf_text ps args = Some T /\ pf_prec_pos ps args /\
    0x10000 <= f /\ f + Z.of_nat (length fmt) + 1 <= 0x99b40 /\ pf_args_slack ws args /\
    fmt <> [] /\ RT_pf_sh.pf_args_amem ws args.

Lemma FF_fm_stable64 : ff_stable64 FF_fm.
Proof.
intros rd rd' rs f ws T (fmt & ps & args & Hf & Hp & Hk & Ha & Ht & Hq & Hlo & Hhi & Hsl & Hne & Ham) Hc.
destruct (fam_reads_stable64 rd rd' rs f fmt ws args Hc Hf Ha) as [Hf' Ha'].
exists fmt, ps, args. repeat (split; [assumption|]). exact Ham.
Qed.

Lemma FF_fm_mono : ff_mono FF_fm.
Proof.
intros rd rs rs' f ws T (fmt & ps & args & Hf & Hp & Hk & Ha & Ht & Hq & Hlo & Hhi & Hsl & Hne & Ham) Hs.
exists fmt, ps, args.
split; [exact (fmt_at_mono rd rs rs' f fmt Hf Hs)|]. split; [exact Hp|]. split; [exact Hk|].
split; [exact (pf_args_asan_mono rd rs rs' ws args Ha Hs)|]. repeat (split; [assumption|]). exact Ham.
Qed.

Lemma FF_fm_ro : forall rd rs f ws T, FF_fm rd rs f ws T -> pf_family_ro pf_fm_piece 0x10000 0x99b40 rd rs f ws T.
Proof.
intros rd rs f ws T (fmt & ps & args & Hf & Hp & Hk & Ha & Ht & Hq & Hlo & Hhi & Hsl & _ & _).
exists fmt, ps, args. repeat (split; [assumption|]). exact Hsl.
Qed.

Lemma FF_fm_pcom : forall rd rs f ws T, FF_fm rd rs f ws T -> RT_pf_sh.FF_pcom rd rs f ws T.
Proof.
intros rd rs f ws T (fmt & ps & args & Hf & Hp & Hk & Ha & Ht & Hq & Hlo & Hhi & Hsl & Hne & Ham).
exists fmt, ps, args.
split; [exact Hf|]. split; [exact Hne|].
split; [assert (E : TFIB_IMG_END = 0x5f6000) by (vm_compute; reflexivity); rewrite E; lia|].
repeat (split; [assumption|]). exact Hq.
Qed.

(* ---- the instance ---- *)
Module GXC := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
Module GVA := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GXA.G_vfprintf_snf.
#[local] Existing Instance A_img.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* fm's snprintf on the GXA route, for every window K >= fm_glue_img + VF_DEPTH = 8160 (the seam's readiness is
   discharged in FMgxaSeamFm.v, so this takes no hypothesis for it) *)
Theorem fm_snprintf_gxa : forall B, AR_laws tfibsegs B -> BoxregSyms B ->
  forall img_lo img_hi K, img_lo <= 65536 -> @GXC.GLOBALS_TOP A_img <= img_hi ->
  FMsnprintfFm.fm_glue_img + FMsnprintfFm.GXA_VF_DEPTH <= K ->
  sh_asnprintf_realizesU tfibsegs B FF_fm K FM_GOT_canary FM_canary img_lo img_hi FMsnprintfCr.fm_cr PC_snprintf.
Proof.
intros B LAWS TB img_lo img_hi K Hlo Hhi HK.
assert (HV : GVA.VFA_DEPTH = FMsnprintfFm.GXA_VF_DEPTH) by (rewrite FMgxaSeam.sa_vfa_depth; reflexivity).
apply (FMsnprintfFm.fm_snprintf_shared B LAWS TB FF_fm img_lo img_hi FMsnprintfCr.fm_cr 2320 FMsnprintfFm.GXA_VF_DEPTH K
  FF_fm_stable64 FF_fm_mono).
- unfold ESTACK, FMsnprintfFm.GXA_VF_DEPTH. lia.
- unfold FMsnprintfFm.GXA_VF_DEPTH. lia.
- exact HK.
- apply (sh_apcommon_realizesUz_weaken tfibsegs B RT_pf_sh.FF_pcom FF_fm 2320 RT_pf_shU.PCM_CR FMsnprintfCr.fm_cr A_PCOM
    FF_fm_pcom).
  + intros r1 Hr1. exists r1. split; [exact Hr1 | lia].
  + exact (RT_pf_shU.pcom_shz B LAWS TB 2320 ltac:(lia)).
- exact (FMsnprintfMs32.memset_icpt_realizesU B LAWS TB).
- apply (sh_avfprintf_icpt_realizesUx_ff tfibsegs B (pf_family_ro pf_fm_piece 0x10000 0x99b40) FF_fm
    FMsnprintfFm.GXA_VF_DEPTH FM_GOT_canary FM_canary img_lo img_hi FMsnprintfCr.fm_cr A_SNW A_VFP FF_fm_ro).
  exact (FMsnprintfSeamI.fm_seam_inst B LAWS TB FMsnprintfFm.GXA_VF_DEPTH img_lo img_hi FMsnprintfCr.fm_cr
    ltac:(rewrite HV; lia) Hlo Hhi FMsnprintfCr.fm_cr_ro_covered).
Qed.
(* the AR form (no user-poisoned range) *)
Corollary fm_snprintf_gxa_AR : forall B, AR_laws tfibsegs B -> BoxregSyms B ->
  forall img_lo img_hi K, img_lo <= 65536 -> @GXC.GLOBALS_TOP A_img <= img_hi ->
  FMsnprintfFm.fm_glue_img + FMsnprintfFm.GXA_VF_DEPTH <= K ->
  sh_asnprintf_realizes tfibsegs B FF_fm K FM_GOT_canary FM_canary img_lo img_hi FMsnprintfCr.fm_cr PC_snprintf.
Proof.
intros B LAWS TB img_lo img_hi K Hlo Hhi HK.
apply sh_asnprintf_of_U. exact (fm_snprintf_gxa B LAWS TB img_lo img_hi K Hlo Hhi HK).
Qed.
End f.
