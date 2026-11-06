(* libreac/fuzz_boxreg, build asan-ubsan: a Theorem Labs lane's proved snprintf (lib/B/Rt/FMsnprintfFmI.v fm_snprintf_gxa_AR, image
   B's relocated copy of the GXA route) gives boxreg's R2 contract lib/B/Rt/SnprintfDefB.v absnprintf_realizes, through
   the image-generic bridge lib/A/Rt/SnprintfBridgeFm.v snp_fm_of_shared (the reasons are in its header). Rule 24: no
   function is proved here; this file is an instance. The two images' format bounds P2 are different constants
   (f + 3 <= 0x99b40 on A, f + 3 <= 0x99f60 on B, each image's GOT canary slot), so B's contract does not convert from
   A's; B is proved from the generic bridge at its own bound.
   - absnprintf_of_snp_fm: absnprintf_realizes is snp_fm_realizes at hi = 0x99f60 (the same text: ABSN_FMT,
     absn_word_end, absn_rom_kept are ASN_FMT, asn_word_end, asn_rom_kept with B names), by conversion;
   - boxb_snp_fm_inst: fm_snprintf_gxa_AR at boxreg's B names, as lib/A/Rt/SnprintfInst.v box_snp_fm_inst: boxb_segs and
     B's tfibsegs (lib/B/AB1v.v:11) are both images.AsanUbsan's M.loaded_segments; BOXB_SNP_GC = FM_GOT_canary =
     0x99f60 and BOXB_SNP_GV = FM_canary = 0x5f4390 (lib/B/Rt/SnprintfFmh.v:56-57, lib/B/Rt/SnprintfBridgeB.v:53-54);
     pa_sigma BB___interceptor_trampoline_snprintf = PC_snprintf = 0x41490; K = 2 * ESTACK (fm_glue_img +
     GXA_VF_DEPTH = 8160); the range (IMG_LO, BOXB_GLOBALS_TOP): fm asks img_lo <= 65536 and GLOBALS_TOP <= img_hi;
   - boxb_ff_fm_entry: B's FF_fm (its P2 bound 0x99f60) takes boxreg's call;
   - boxb_fm_cv_kept: consts_view over B's fm_cr from B's fm_cr_consts_view (lib/B/Rt/FMsnprintfCr.v), with
     abfm_rom_viewN = absn_rom_kept and abfm_rom_viewO from lib/B/Rt/StrncmpViewB.v abfm_rom_viewO_of_AR over
     lib/B/Rt/StrncmpViewBInst.v box_ro_owned_pinned (B's AF0mCheck.v box_ro_pinned) and B's TfibB_syms;
   - boxb_snp_canary_got: the .got word 0x99f60 holds 0x5f4390 in a const cell of B's TfibB (B's AF0m.v
     Tfib_const_abs, by computation).
   Row 19 of lib/B/Prog/BoxBClose.v (H_RT_SNPRINTF_B, BB = lib/B/AD2l.v TfibB; a working branch
   6ee67028be4): boxb_absnprintf_fm. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YG0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import FMsnprintfPf FMsnprintfShared.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import SnprintfBridge SnprintfBridgeFm.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import SnprintfDefB SnprintfBridgeB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require SnprintfFmh FMsnprintfFm FMsnprintfFmI FMsnprintfCr.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require StrncmpViewB StrncmpViewBInst.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B Require AF0m AD2l RT_IImgA.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GX Require G_printf_core_common.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBAddr BoxBPa BoxBImg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module GXC := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
Module BFmh := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt.SnprintfFmh.
Module BFm := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt.FMsnprintfFm.
Module BFmI := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt.FMsnprintfFmI.
Module BCr := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt.FMsnprintfCr.
Module BView := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt.StrncmpViewB.
Module BViewI := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt.StrncmpViewBInst.
Module BAF0m := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.AF0m.
Module BAD2l := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.AD2l.
Module BImg := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.RT_IImgA.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* absnprintf_realizes is the generic text at image B's GOT canary slot. *)
Lemma absnprintf_of_snp_fm : forall segs B pc, snp_fm_realizes segs B 0x99f60 pc -> absnprintf_realizes segs B pc.
Proof. intros segs B pc H. exact H. Qed.
End b.

(* ---- fm_snprintf_gxa_AR at boxreg's B names ---- *)
Lemma boxb_snp_globals_top : @GXC.GLOBALS_TOP BImg.A_img <= BOXB_GLOBALS_TOP.
Proof. unfold BOXB_GLOBALS_TOP. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma boxb_snp_K : BFm.fm_glue_img + BFm.GXA_VF_DEPTH <= 2 * ESTACK.
Proof. rewrite BFm.fm_K_min_gxa. unfold ESTACK. lia. Qed.
Lemma boxb_snp_img_range_lo : snp_img_range boxb_segs IMG_LO BOXB_GLOBALS_TOP.
Proof.
split; [unfold BOXB_GLOBALS_TOP; lia|]. split; [unfold BOXB_GLOBALS_TOP; lia|]. exact boxb_img_cover_all.
Qed.
Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma boxb_snp_pc : pa_sigma (PAImg := PI_boxb) BB___interceptor_trampoline_snprintf = BFmh.PC_snprintf.
Proof. reflexivity. Qed.
Theorem boxb_snp_fm_inst : forall B, AR_laws boxb_segs B -> BAF0m.BoxregSyms B ->
  sh_asnprintf_realizes boxb_segs B BFmI.FF_fm (2 * ESTACK) BOXB_SNP_GC BOXB_SNP_GV IMG_LO BOXB_GLOBALS_TOP
    BCr.fm_cr (pa_sigma (PAImg := PI_boxb) BB___interceptor_trampoline_snprintf).
Proof.
intros B LAWS TB. rewrite boxb_snp_pc.
exact (BFmI.fm_snprintf_gxa_AR B LAWS TB IMG_LO BOXB_GLOBALS_TOP (2 * ESTACK) ltac:(lia)
  boxb_snp_globals_top boxb_snp_K).
Qed.
End i.

(* ---- the bridge's image premises ---- *)
(* B's fm family FF_fm takes boxreg's call. *)
Lemma boxb_ff_fm_entry : snp_ff_entry BFmI.FF_fm 0x99f60.
Proof.
intros rd rs f x ws s Hf Ha Hlo Hhi Hx8.
pose proof (Z.mod_pos_bound (x + Z.of_nat (length s)) 8 ltac:(lia)) as Hmod.
exists [37; 115], [Ps], [APtr s].
split; [exact Hf|]. split; [reflexivity|]. split; [constructor; [exact I | constructor]|].
split; [split; [exact Ha | destruct ws; exact I]|].
split; [cbn [pf_text option_map]; rewrite app_nil_r; reflexivity|].
split; [exact I|].
split; [exact Hlo|]. split; [change (Z.of_nat (length [37; 115])) with 2; lia|].
split; [split; [|destruct ws; exact I]|].
{ apply (snp_amem_le x (Z.of_nat (length s) + 8)); [unfold str_end; lia | exact Hx8]. }
split; [discriminate|].
split; [exact Hx8 | destruct ws; exact I].
Qed.
(* B's fm_cr: nonempty ranges below 2 ^ 63, every byte read-only. *)
Lemma boxb_fm_cr_rom : snp_cr_rom boxb_segs BCr.fm_cr.
Proof.
split.
- assert (Hb : forallb (fun r => (0 <? snd r) && (0 <=? fst r) && (fst r + snd r <=? 2 ^ 63)) BCr.fm_cr = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb. apply Forall_forall. intros r Hr. specialize (Hb r Hr).
  apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. lia.
- intros a Ha. exact (proj1 (BCr.fm_cr_rom a Ha)).
Qed.
(* The .got canary word is a const cell of B's TfibB (a row of B's AF0m.v Tfib_const_abs). *)
Lemma boxb_snp_canary_got : snp_canary_got BAD2l.TfibB BOXB_SNP_GC BOXB_SNP_GV.
Proof.
intros ly. cbn [as_const BAD2l.TfibB]. unfold BAF0m.Tfib_const. apply in_app_iff. right. apply in_app_iff. left.
cbv [z8 c8 BOXB_SNP_GC BOXB_SNP_GV]. apply BAD2l.zcell_in. vm_compute. reflexivity.
Qed.
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* consts_view over B's fm_cr as fm takes it. *)
Lemma boxb_fm_cv_kept : snp_cv_kept boxb_segs BAD2l.TfibB BCr.fm_cr.
Proof.
intros ly S W mem md HAR Hrk.
exact (BCr.fm_cr_consts_view BAD2l.TfibB W mem BAD2l.TfibB_syms Hrk
  (BView.abfm_rom_viewO_of_AR boxb_segs BAD2l.TfibB ly S W mem md BViewI.box_ro_owned_pinned HAR)).
Qed.
Theorem boxb_absnprintf_fm_TfibB :
  absnprintf_realizes boxb_segs BAD2l.TfibB (pa_sigma (PAImg := PI_boxb) BB___interceptor_trampoline_snprintf).
Proof.
apply absnprintf_of_snp_fm.
pose proof (YG0q.AR_laws_ok boxb_segs BAD2l.TfibB) as LAWS.
exact (snp_fm_of_shared boxb_segs BAD2l.TfibB BFmI.FF_fm 0x99f60 BOXB_SNP_GC BOXB_SNP_GV IMG_LO BOXB_GLOBALS_TOP
  BCr.fm_cr (pa_sigma (PAImg := PI_boxb) BB___interceptor_trampoline_snprintf) LAWS boxb_ff_fm_entry boxb_fm_cr_rom
  boxb_fm_cv_kept boxb_snp_img_gc boxb_snp_img_gv
  (snp_canary_ar_of boxb_segs BAD2l.TfibB BOXB_SNP_GC BOXB_SNP_GV boxb_snp_canary_got boxb_snp_img_gv)
  boxb_snp_img_range_lo (boxb_snp_fm_inst BAD2l.TfibB LAWS BAD2l.TfibB_syms)).
Qed.
End k.
(* Row 19 of lib/B/Prog/BoxBClose.v (H_RT_SNPRINTF_B) at BB = lib/B/AD2l.v TfibB. *)
Theorem boxb_absnprintf_fm : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  absnprintf_realizes boxb_segs BAD2l.TfibB (pa_sigma (PAImg := PI_boxb) BB___interceptor_trampoline_snprintf).
Proof. intros rc fx. exact boxb_absnprintf_fm_TfibB. Qed.
