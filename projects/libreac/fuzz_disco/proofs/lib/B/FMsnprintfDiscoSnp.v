(* fuzz_disco.asan-ubsan: disco_snprintf_R, the guarded snprintf contract SnprintfDefR.asnprintf_realizesR at PB_tfib's
   segments, YD2l.TfibB, PB_tfib's relro range, the snprintf trampoline AS___interceptor_trampoline_snprintf, YE2k's
   canary cells, [IMG_LO, IMG_TOP), disco's format range and the Y snp_cr (lib/Y/Rt/SnprintfConsts.v): the ASNP form
   of DiscoYLibX with the arodata_okP premise (a Theorem Labs lane ruling (B), 2026-10-29 18:38Z). Rule 24: no function is proved
   here. New file. It is the Y disco snprintf top FMsnprintfDiscoR1.disco_snprintf_gxa_r1_AR (cr = FMsnprintfCr.fm_cr,
   every read-only segment), lifted to the SNPRINTF_STK window (SnprintfDef.asnprintf_of_shared_K), with its fm_cr
   premises rebuilt from what the guarded caller holds:
   - consts_view over fm_cr: FMsnprintfCrRom.fm_cr_consts_view_AR (rom_viewO from AR, inside ecall_pre), with its
     rom_viewN premise from arodata_okP (in_rom is in_roP's first disjunct);
   - the bounds of fm_cr: FMsnprintfCr.fm_cr_bounds;
   - fm_cr misses snp_out: every range of fm_cr lies in [0x10000, 0xa0000) (FMsnprintfCr.fm_cr_in_image); the callee's
     stack window lies above kHighMemBeg <= ly_stk_lo (layout_ok's lo_top) and the destination outside
     [IMG_LO, IMG_TOP) (the contract's dest_off_globals premise).
   The caller's own consts_view over snp_cr and its two side conditions are not used. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI04 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YB1v YF0m YI0w YI0z YC4a YCbj.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YC8g YG0q YImgTop YD2l YE2k.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.B Require Import FMH_Base.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnUpoison SnShared.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnprintfDef SnprintfDefR.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.B Require FMsnprintfFm FMsnprintfCr FMsnprintfCrRom FMsnprintfDiscoR1.
Import ListNotations.
Local Open Scope Z_scope.

Section w. Context {rc : YM05.RunCeil}.
#[local] Abbreviation SEGS := (@pa_segs _ lib_both3_0_listing PB_tfib).
#[local] Abbreviation SIGMA := (@pa_sigma _ lib_both3_0_listing PB_tfib).
#[local] Abbreviation RLO := (@pa_relro_lo _ lib_both3_0_listing PB_tfib).
#[local] Abbreviation RHI := (@pa_relro_hi _ lib_both3_0_listing PB_tfib).

Theorem disco_snprintf_R : forall fq : YK11.FPState,
  SnprintfDefR.asnprintf_realizesR (fx := fq) SEGS YD2l.TfibB RLO RHI YE2k.FF_got_canary YE2k.FF_canary
    YImgTop.IMG_LO YImgTop.IMG_TOP disco_fmt_lo disco_fmt_hi snp_cr (SIGMA AS___interceptor_trampoline_snprintf).
Proof.
intros fq.
assert (PC : SIGMA AS___interceptor_trampoline_snprintf = PC_snprintf) by (vm_compute; reflexivity).
rewrite PC.
assert (TOP : SnprintfDef.asnprintf_realizes (fx := fq) tfibsegs YD2l.TfibB FM_GOT_canary FM_canary
  YImgTop.IMG_LO YImgTop.IMG_TOP disco_fmt_lo disco_fmt_hi FMsnprintfCr.fm_cr PC_snprintf).
{ apply (SnprintfDef.asnprintf_of_shared_K (fx := fq) tfibsegs YD2l.TfibB
    (FMsnprintfFm.fm_glue_img + FMsnprintfFm.GXA_VF_DEPTH)).
  - apply Z.leb_le. vm_compute. reflexivity.
  - apply (FMsnprintfDiscoR1.disco_snprintf_gxa_r1_AR (fx := fq) YD2l.TfibB (YG0q.AR_laws_ok tfibsegs YD2l.TfibB)
      YD2l.TfibB_syms).
    + unfold YImgTop.IMG_LO. lia.
    + apply Z.leb_le. vm_compute. reflexivity.
    + lia. }
unfold SnprintfDef.asnprintf_realizes, SnShared.sh_asnprintf_realizes in TOP.
unfold SnprintfDefR.asnprintf_realizesR, SnprintfDefR.sh_asnprintf_realizesR.
intros ly S W regs mem md d n f xs ws T cval HE HRO HK HP R10 R11 R12 _ _ _ Hgc Hgv Hgc0 Hgc8 Hgv0 Hgv8 Dgc Dgv
  HVA HXS DXS HFF Hn HT Hd0 Hd PW DOK AMR RA SHV DOG FRM.
(* consts_view over fm_cr: rom_viewO from AR, rom_viewN from arodata_okP *)
assert (CV : SnShared.consts_view tfibsegs W mem FMsnprintfCr.fm_cr).
{ apply (FMsnprintfCrRom.fm_cr_consts_view_AR YD2l.TfibB YD2l.TfibB_syms ly S W mem md (proj1 HE)).
  intros a Hrom Ho He. exact (HRO a (or_introl Hrom) Ho He). }
(* fm_cr misses the callee's stack window (above kHighMemBeg) and the destination (outside [IMG_LO, IMG_TOP)) *)
assert (DJ : Forall (fun r => Forall (zdisjoint r)
    (snp_out SnprintfDef.SNPRINTF_STK (spZ regs) d (sn_len (n - 1) T))) FMsnprintfCr.fm_cr).
{ pose proof HE as ((M & _) & _). apply am_layout in M. apply lo_top in M.
  apply Forall_forall. intros r Hr.
  pose proof (proj1 (Forall_forall _ _) FMsnprintfCr.fm_cr_in_image r Hr) as Hb. cbv beta in Hb.
  unfold snp_out. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
    unfold zdisjoint, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; cbn [fst snd] in *.
  - left. unfold YG0f.kHighMemBeg in M. lia.
  - lia. }
exact (TOP ly S W regs mem md d n f xs ws T cval HE HK HP R10 R11 R12 CV FMsnprintfCr.fm_cr_bounds DJ
  Hgc Hgv Hgc0 Hgc8 Hgv0 Hgv8 Dgc Dgv HVA HXS DXS HFF Hn HT Hd0 Hd PW DOK AMR RA SHV DOG FRM).
Qed.
End w.
