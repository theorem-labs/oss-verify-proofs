(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintf02x.v (a working branch 0ddf65fd8cc); relocated to libreac/fuzz_disco.asan-ubsan by reloc.py (target disco-Y): module paths changed; 0 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan-ubsan, symbol + offset; table: this file's rows in provenance/evidence/g9-gxa/g9tool/g9-table-disco-Y.tsv); names: record RT_IImgA -> A_img RecAsanVfB.N_img_asan_ubsan_vf; A-core -> Y-core (lib.Reusable): AB1v->YB1v, AE20->YE20, AE2y->YE2y, AE34->YE34, AF0l->YF0l, AF0m->YF0m, AF0x->YF0x. *)
(* R1 row R-02x: %02x is IN fm's snprintf route. fm_snprintf_gxaP (FMsnprintfFmI.v, a Theorem Labs lane's W0 ccca7d8f411) at the
   covered-piece predicate RT_pf_02x.pf_pc_02x (fm's pieces PLit / %s / %.*s and %02x), with its four arms: the three
   seam arms (W0's lit / %s / %.*s arms, FMgxaSeamPf.v, and FMgxaSeam02x.v's at Px02) and the printf_common arm
   (RT_pf_02x.pf_pc_02x_arms). New file; nothing is edited. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YB1v YE34 YF0l YF0m YF0x YE20 YE2y.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnUpoison.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.B Require Import FMH_Base FMsnprintfImg.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import PfFacts SnShared SnSx.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.B Require RT_pf_sh.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require FMgxaSeamPf.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.B Require FMsnprintfFm FMsnprintfCr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.B Require RT_pf_02x.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require FMgxaSeam02x.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.B Require FMsnprintfFmI.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.I Require Import RecAsanVfB.
Import ListNotations.
Local Open Scope Z_scope.

Module GXC := OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX.G_printf_core_common.

(* ---- the three seam arms at fm's pieces and %02x ---- *)
Lemma pf_pc_02x_text_arms : forall p, RT_pf_02x.pf_pc_02x p -> FMgxaSeamPf.seam_text_arm p.
Proof.
intros p Hp. destruct p; try (exfalso; exact Hp).
- apply FMgxaSeamPf.seam_text_arm_lit.
- exact FMgxaSeam02x.seam_text_arm_px02.
- exact FMgxaSeamPf.seam_text_arm_ps.
- exact FMgxaSeamPf.seam_text_arm_pps.
Qed.
Lemma pf_pc_02x_pargs_arms : forall p, RT_pf_02x.pf_pc_02x p -> FMgxaSeamPf.seam_pargs_arm p.
Proof.
intros p Hp. destruct p; try (exfalso; exact Hp).
- apply FMgxaSeamPf.seam_pargs_arm_lit.
- exact FMgxaSeam02x.seam_pargs_arm_px02.
- exact FMgxaSeamPf.seam_pargs_arm_ps.
- exact FMgxaSeamPf.seam_pargs_arm_pps.
Qed.
Lemma pf_pc_02x_bytes_arms : forall p, RT_pf_02x.pf_pc_02x p -> FMgxaSeamPf.seam_bytes_arm p.
Proof.
intros p Hp. destruct p; try (exfalso; exact Hp).
- apply FMgxaSeamPf.seam_bytes_arm_lit.
- exact FMgxaSeam02x.seam_bytes_arm_px02.
- exact FMgxaSeamPf.seam_bytes_arm_ps.
- exact FMgxaSeamPf.seam_bytes_arm_pps.
Qed.

(* ---- fm's snprintf on the GXA route, for formats with %02x ---- *)
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem fm_snprintf_gxa_02x : forall B, AR_laws tfibsegs B -> TfibSyms B ->
  forall img_lo img_hi K, img_lo <= 65536 -> @GXC.G_printf_iface.GLOBALS_TOP N_img_asan_ubsan_vf <= img_hi ->
  FMsnprintfFm.fm_glue_img + FMsnprintfFm.GXA_VF_DEPTH <= K ->
  sh_asnprintf_realizesU tfibsegs B (FMsnprintfFmI.FF_fmP RT_pf_02x.pf_pc_02x) K FM_GOT_canary FM_canary
    img_lo img_hi FMsnprintfCr.fm_cr PC_snprintf.
Proof.
intros B LAWS TB.
exact (FMsnprintfFmI.fm_snprintf_gxaP B LAWS TB RT_pf_02x.pf_pc_02x pf_pc_02x_text_arms pf_pc_02x_pargs_arms
  pf_pc_02x_bytes_arms RT_pf_02x.pf_pc_02x_arms).
Qed.
End f.
