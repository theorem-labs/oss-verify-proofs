(* fuzz_disco.asan: disco_snprintf_R, the guarded snprintf contract SnprintfDefR.asnprintf_realizesR at PB_disco's
   segments, the snprintf trampoline, AE2k's canary cells, [IMG_LO, IMG_TOP), disco's format range and snp_cr, the
   form a Theorem Labs lane's entry walk names (a Theorem Labs lane ruling (B), 2026-10-29 18:38Z). Rule 24: no function is proved here.
   New file. It is the disco snprintf top FMsnprintfDiscoR1.disco_snprintf_gxa_r1_AR (cr = FMsnprintfCr.fm_cr, every
   read-only segment), lifted to the SNPRINTF_STK window (SnprintfDef.asnprintf_of_shared_K), with its fm_cr premises
   rebuilt from what the guarded caller holds:
   - consts_view over fm_cr: FMsnprintfRomO.fm_cr_consts_of_arodata, from AR (inside ecall_pre) and arodata_okP;
   - the bounds of fm_cr: FMsnprintfCr.fm_cr_bounds;
   - fm_cr misses snp_out: fm_cr_out_disjoint below. Every range of fm_cr lies in [0x10000, 0x9f000)
     (FMsnprintfCr.fm_cr_in_image); the callee's stack window lies above kHighMemBeg <= ly_stk_lo (layout_ok's lo_top)
     and the destination outside [img_lo, img_hi) (the contract's dest_off_globals premise).
   The caller's own consts_view over snp_cr and its two side conditions are not used. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI04 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YC8g YG0q YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AB1v AF0m FMH_Base.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnUpoison SnShared.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnprintfDef SnprintfDefR.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoSyms DiscoPa.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require DiscoList DiscoImg.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AD2l AE2k FMgxaSeam FMsnprintfFm FMsnprintfCr
  FMsnprintfRomO FMsnprintfDiscoR1.
Import ListNotations.
Local Open Scope Z_scope.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma fm_cr_out_disjoint : forall B ly S (W : world tfibsegs) regs mem md K d len img_lo img_hi,
  ecall_pre tfibsegs B ly S W regs mem md -> ly_stk_lo ly + K <= spZ regs ->
  img_lo <= 0x10000 -> 0x9f000 <= img_hi -> zdisjoint (d, len) (img_lo, img_hi - img_lo) ->
  Forall (fun r => Forall (zdisjoint r) (snp_out K (spZ regs) d len)) FMsnprintfCr.fm_cr.
Proof.
intros B ly S W regs mem md K d len img_lo img_hi HE HK Hlo Hhi Hd.
destruct HE as ((M & _) & _). apply am_layout in M. apply lo_top in M.
apply Forall_forall. intros r Hr.
pose proof (proj1 (Forall_forall _ _) FMsnprintfCr.fm_cr_in_image r Hr) as Hb. cbv beta in Hb.
unfold snp_out. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint in *; cbn [fst snd] in *.
- left. unfold YG0f.kHighMemBeg in M. lia.
- lia.
Qed.
End h.

Section w. Context {rc : YM05.RunCeil}.
#[local] Abbreviation SEGS := (@pa_segs _ DiscoList.disco_listing DiscoImg.PB_disco).
#[local] Abbreviation SIGMA := (@pa_sigma _ DiscoList.disco_listing DiscoImg.PB_disco).
#[local] Abbreviation RLO := (@pa_relro_lo _ DiscoList.disco_listing DiscoImg.PB_disco).
#[local] Abbreviation RHI := (@pa_relro_hi _ DiscoList.disco_listing DiscoImg.PB_disco).

Theorem disco_snprintf_R : forall fq : YK11.FPState,
  SnprintfDefR.asnprintf_realizesR (fx := fq) SEGS AD2l.TfibB RLO RHI AE2k.FF_got_canary AE2k.FF_canary
    YImgTop.IMG_LO YImgTop.IMG_TOP disco_fmt_lo disco_fmt_hi snp_cr (SIGMA DS___interceptor_trampoline_snprintf).
Proof.
intros fq.
assert (TOP : SnprintfDef.asnprintf_realizes (fx := fq) tfibsegs AD2l.TfibB FM_GOT_canary FM_canary
  YImgTop.IMG_LO YImgTop.IMG_TOP disco_fmt_lo disco_fmt_hi FMsnprintfCr.fm_cr PC_snprintf).
{ apply (SnprintfDef.asnprintf_of_shared_K (fx := fq) tfibsegs AD2l.TfibB
    (FMsnprintfFm.fm_glue_img + FMsnprintfFm.GXA_VF_DEPTH)).
  - apply Z.leb_le. vm_compute. reflexivity.
  - apply (FMsnprintfDiscoR1.disco_snprintf_gxa_r1_AR (fx := fq) AD2l.TfibB (YG0q.AR_laws_ok tfibsegs AD2l.TfibB)
      AD2l.TfibB_syms).
    + unfold YImgTop.IMG_LO. lia.
    + rewrite FMgxaSeam.sa_globals_top. unfold YImgTop.IMG_TOP. lia.
    + lia. }
unfold SnprintfDef.asnprintf_realizes, SnShared.sh_asnprintf_realizes in TOP.
unfold SnprintfDefR.asnprintf_realizesR, SnprintfDefR.sh_asnprintf_realizesR.
intros ly S W regs mem md d n f xs ws T cval HE HRO HK HP R10 R11 R12 _ _ _ Hgc Hgv Hgc0 Hgc8 Hgv0 Hgv8 Dgc Dgv
  HVA HXS DXS HFF Hn HT Hd0 Hd PW DOK AMR RA SHV DOG FRM.
exact (TOP ly S W regs mem md d n f xs ws T cval HE HK HP R10 R11 R12
  (FMsnprintfRomO.fm_cr_consts_of_arodata AD2l.TfibB AD2l.TfibB_syms ly S W mem md RLO RHI (proj1 HE) HRO)
  FMsnprintfCr.fm_cr_bounds
  (fm_cr_out_disjoint AD2l.TfibB ly S W regs mem md SnprintfDef.SNPRINTF_STK d (sn_len (n - 1) T)
    YImgTop.IMG_LO YImgTop.IMG_TOP HE HK ltac:(unfold YImgTop.IMG_LO; lia) ltac:(unfold YImgTop.IMG_TOP; lia) DOG)
  Hgc Hgv Hgc0 Hgc8 Hgv0 Hgv8 Dgc Dgv HVA HXS DXS HFF Hn HT Hd0 Hd PW DOK AMR RA SHV DOG FRM).
Qed.
End w.
