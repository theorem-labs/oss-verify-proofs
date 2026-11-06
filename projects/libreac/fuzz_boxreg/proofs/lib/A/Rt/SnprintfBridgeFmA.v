(* libreac/fuzz_boxreg, build asan: a Theorem Labs lane's proved snprintf (lib/A/Rt/FMsnprintfFmI.v fm_snprintf_gxa_AR, the GXA route,
   at boxreg's names in lib/A/Rt/SnprintfInst.v box_snp_fm_inst) gives boxreg's R2 contract lib/A/Rt/SnprintfDef.v
   asnprintf_realizes at TfibB, through the image-generic bridge lib/A/Rt/SnprintfBridgeFm.v snp_fm_of_shared (the
   reasons are in its header). Rule 24: no function is proved here; this file is an instance.
   - box_ff_fm_entry: fm's family FF_fm (FMsnprintfFmI.v:32-37) takes boxreg's call: pf_parse [37; 115] = Some [Ps],
     Ps is a pf_fm_piece, |fmt| = 2 turns fm's f + |fmt| + 1 <= 0x99b40 into the contract's f + 3 <= 0x99b40,
     fmt <> [], and amem_range x (|s| + 8) gives both pf_args_slack (str_end x s - x <= |s| + 8) and RT_pf_sh.v
     pf_args_amem (the same range);
   - box_fm_cr_rom: fm_cr (the image's non-writable segments) meets snp_cr_rom (nonempty ranges below 2 ^ 63, by
     computation; read-only bytes, FMsnprintfCr.v fm_cr_rom);
   - box_fm_cv_kept: consts_view over fm_cr the way fm takes it, FMsnprintfCr.v fm_cr_consts_view: its rom_viewN is
     the contract's asn_rom_kept (the same text as StrncmpDef.v fm_rom_viewN), its rom_viewO comes from StrncmpView.v
     fm_rom_viewO_of_AR over AR and StrncmpViewInst.v box_ro_owned_pinned (TfibB pins every runtime-owned read-only
     byte: AF0mCheck.v box_ro_pinned, the 26 read-only pin rows of Tfib_const_abs), and AD2l.v TfibB_syms gives its
     errno side condition;
   - box_snp_canary_got: the .got word 0x99b40 holds 0x5f3f50 in a const cell of TfibB (the row z8 (ANum 0x99b40)
     0x5f3f50 of AF0m.v Tfib_const_abs, by computation);
   - the rest: AR_laws from YG0q.v AR_laws_ok; the range (IMG_LO, BOX_GLOBALS_TOP) from SnprintfInst.v
     box_snp_img_range_lo; the canary words from SnprintfBridge.v box_snp_img_gc / box_snp_img_gv.
   Row 19 of lib/A/Prog/BoxClose.v (H_RT_SNPRINTF_A, BA = AD2l.TfibB on a working branch):
   box_asnprintf_fm. *)
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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import SnprintfDef SnprintfBridge SnprintfBridgeFm.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require FMsnprintfFmI FMsnprintfCr StrncmpView StrncmpViewInst.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require SnprintfInst.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require AF0m AD2l.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym BoxSyms BoxAddr BoxPa BoxImg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module AFmI := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt.FMsnprintfFmI.
Module ACr := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt.FMsnprintfCr.
Module AView := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt.StrncmpView.
Module AViewI := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt.StrncmpViewInst.
Module AInst := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt.SnprintfInst.
Module AAF0m := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.AF0m.
Module AAD2l := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.AD2l.

(* fm's family FF_fm takes boxreg's call. *)
Lemma box_ff_fm_entry : snp_ff_entry AFmI.FF_fm 0x99b40.
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
(* fm_cr: nonempty ranges below 2 ^ 63, every byte read-only (fm's fm_cr_rom). *)
Lemma box_fm_cr_rom : snp_cr_rom box_segs ACr.fm_cr.
Proof.
split.
- assert (Hb : forallb (fun r => (0 <? snd r) && (0 <=? fst r) && (fst r + snd r <=? 2 ^ 63)) ACr.fm_cr = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb. apply Forall_forall. intros r Hr. specialize (Hb r Hr).
  apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. lia.
- intros a Ha. exact (proj1 (ACr.fm_cr_rom a Ha)).
Qed.
(* The .got canary word is a const cell of TfibB (a row of AF0m.v Tfib_const_abs). *)
Lemma box_snp_canary_got : snp_canary_got AAD2l.TfibB BOX_SNP_GC BOX_SNP_GV.
Proof.
intros ly. cbn [as_const AAD2l.TfibB]. unfold AAF0m.Tfib_const. apply in_app_iff. right. apply in_app_iff. left.
cbv [z8 c8 BOX_SNP_GC BOX_SNP_GV]. apply AAD2l.zcell_in. vm_compute. reflexivity.
Qed.
Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* consts_view fm_cr as fm takes it: rom_viewN is asn_rom_kept, rom_viewO comes from AR and TfibB's read-only pins. *)
Lemma box_fm_cv_kept : snp_cv_kept box_segs AAD2l.TfibB ACr.fm_cr.
Proof.
intros ly S W mem md HAR Hrk.
exact (ACr.fm_cr_consts_view AAD2l.TfibB W mem AAD2l.TfibB_syms Hrk
  (AView.fm_rom_viewO_of_AR box_segs AAD2l.TfibB ly S W mem md AViewI.box_ro_owned_pinned HAR)).
Qed.
Theorem box_asnprintf_fm_TfibB :
  asnprintf_realizes box_segs AAD2l.TfibB (pa_sigma (PAImg := PI_box) BS___interceptor_trampoline_snprintf).
Proof.
apply asnprintf_of_snp_fm.
pose proof (YG0q.AR_laws_ok box_segs AAD2l.TfibB) as LAWS.
exact (snp_fm_of_shared box_segs AAD2l.TfibB AFmI.FF_fm 0x99b40 BOX_SNP_GC BOX_SNP_GV IMG_LO BOX_GLOBALS_TOP ACr.fm_cr
  (pa_sigma (PAImg := PI_box) BS___interceptor_trampoline_snprintf) LAWS box_ff_fm_entry box_fm_cr_rom box_fm_cv_kept
  box_snp_img_gc box_snp_img_gv
  (snp_canary_ar_of box_segs AAD2l.TfibB BOX_SNP_GC BOX_SNP_GV box_snp_canary_got box_snp_img_gv)
  AInst.box_snp_img_range_lo (AInst.box_snp_fm_inst AAD2l.TfibB LAWS AAD2l.TfibB_syms)).
Qed.
End i.
(* Row 19 of lib/A/Prog/BoxClose.v (H_RT_SNPRINTF_A) at BA = AD2l.TfibB. *)
Theorem box_asnprintf_fm : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  asnprintf_realizes box_segs AAD2l.TfibB (pa_sigma (PAImg := PI_box) BS___interceptor_trampoline_snprintf).
Proof. intros rc fx. exact box_asnprintf_fm_TfibB. Qed.
