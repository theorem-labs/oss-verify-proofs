(* libreac/fuzz_boxreg, build asan: a Theorem Labs lane's proved snprintf (lib/A/Rt/FMsnprintfFmI.v fm_snprintf_gxa_AR, the GXA
   route, relocated from a working branch 3e35620c52e) at boxreg's names: segments box_segs, the
   canary cells BOX_SNP_GC -> BOX_SNP_GV, the window 2 * ESTACK, the trampoline pa_sigma BS___interceptor_trampoline_snprintf
   and the writable-globals range (IMG_LO, BOX_GLOBALS_TOP) (lib/A/Rt/SnprintfBridge.v). Rule 24: no function is proved
   here; this file is an instance.
   How each name meets fm's:
   - box_segs and tfibsegs (lib/A/AB1v.v:11) are both images.Asan's M.loaded_segments (delta);
   - BOX_SNP_GC = FM_GOT_canary = 0x99b40 and BOX_SNP_GV = FM_canary = 0x5f3f50 (lib/A/Rt/SnprintfFmh.v:56-57; fm's own
     proof reaches 0x5f3f50 through the GXA key 0x34288: FMsnprintfSeamI.v si_guard, FMgxaSeam.v sa_sym_guard,
     lib/A/RT_IImgA.v `KV 0x34288 0x5f3f50`);
   - pa_sigma BS___interceptor_trampoline_snprintf = PC_snprintf = 0x41430 (lib/A/Prog/BoxAddr.v, SnprintfFmh.v:53);
   - the window: fm_glue_img + GXA_VF_DEPTH = 8160 <= 8192 = 2 * ESTACK, so fm's theorem is taken at K = 2 * ESTACK
     directly;
   - the globals range: fm asks img_lo <= 65536 and GLOBALS_TOP (sym 0x35000 = 0x5f6000) <= img_hi, so it is taken at
     (IMG_LO, BOX_GLOBALS_TOP) = (0x10000, 0x5f6000). SnprintfBridge.v box_asnprintf_of_shared accepts that range
     (snp_img_range holds at IMG_LO, box_snp_img_range_lo below), so no step to (BOX_GLOBALS_LO, BOX_GLOBALS_TOP) is
     needed.
   Not met here: fm's format family FF_fm and read-only list fm_cr are not the bridge's pf_family (fun p => p = Ps) and
   box_snp_cr, and fm's BoxregSyms B is not among BoxClose's Section close hypotheses. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import AF0m.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym BoxSyms BoxAddr BoxPa BoxImg.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import FMsnprintfShared SnprintfBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require SnprintfFmh FMsnprintfFm FMsnprintfCr FMsnprintfFmI.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GX Require G_printf_core_common.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import RT_IImgA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module GXC := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.

Lemma box_snp_globals_top : @GXC.GLOBALS_TOP A_img <= BOX_GLOBALS_TOP.
Proof.
assert (E : @GXC.GLOBALS_TOP A_img = 0x5f6000) by (vm_compute; reflexivity).
rewrite E. unfold BOX_GLOBALS_TOP. lia.
Qed.
Lemma box_snp_K : FMsnprintfFm.fm_glue_img + FMsnprintfFm.GXA_VF_DEPTH <= 2 * ESTACK.
Proof. rewrite FMsnprintfFm.fm_K_min_gxa. unfold ESTACK. lia. Qed.
(* The range (IMG_LO, BOX_GLOBALS_TOP) is one box_asnprintf_of_shared takes. *)
Lemma box_snp_img_range_lo : snp_img_range box_segs IMG_LO BOX_GLOBALS_TOP.
Proof.
split; [unfold BOX_GLOBALS_TOP; lia|]. split; [unfold BOX_GLOBALS_TOP; lia|]. exact box_img_cover_all.
Qed.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma box_snp_pc : pa_sigma (PAImg := PI_box) BS___interceptor_trampoline_snprintf = SnprintfFmh.PC_snprintf.
Proof. reflexivity. Qed.
(* fm_snprintf_gxa_AR at boxreg's segments, canary cells, window, trampoline and globals range. *)
Theorem box_snp_fm_inst : forall B, AR_laws box_segs B -> BoxregSyms B ->
  sh_asnprintf_realizes box_segs B FMsnprintfFmI.FF_fm (2 * ESTACK) BOX_SNP_GC BOX_SNP_GV IMG_LO BOX_GLOBALS_TOP
    FMsnprintfCr.fm_cr (pa_sigma (PAImg := PI_box) BS___interceptor_trampoline_snprintf).
Proof.
intros B LAWS TB. rewrite box_snp_pc.
exact (FMsnprintfFmI.fm_snprintf_gxa_AR B LAWS TB IMG_LO BOX_GLOBALS_TOP (2 * ESTACK) ltac:(lia)
  box_snp_globals_top box_snp_K).
Qed.
End i.
