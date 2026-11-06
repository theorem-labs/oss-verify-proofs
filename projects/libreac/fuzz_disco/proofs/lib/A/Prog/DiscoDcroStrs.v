From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop YO0f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1i DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacBoxName JsonScalar.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntryInv DiscoRo DiscoEntBodyStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoImg DiscoRoClose.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoDcroParts DiscoDcroLib.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section s. Context {rc : YM05.RunCeil}. Context {SK : YI16.sink_head}.
Variable B : asyms.

Theorem dcro_strs : dcro_strs_stmt B.
Proof.
unfold dcro_strs_stmt, dcro_of. intros LAWS DRO ly S W m md HAR HOK.
destruct DRO as (DRU & GM & HV).
assert (CTX : dro_ctx B ly S W m md).
{ unfold dro_ctx. split; [exact HAR|]. split; [exact HOK|]. split; [exact DRU|]. split; [exact GM | exact HV]. }
pose proof (d_rostr_of B ly S W m md CTX) as MK.
pose proof (d_word_b B ly S W m md CTX) as MKW.
pose proof (d_rbn_stem_of B ly S W m md CTX) as MKS.
pose proof (d_rbn_lit_of B ly S W m md CTX) as MKL.
pose proof (d_rdok_b B ly S W m md CTX) as MKR.
split.
- unfold dimg_strs.
  rewrite !(d_val_obj 4%nat 0x21060 ltac:(lia) eq_refl), !(d_val_obj 5%nat 0x21080 ltac:(lia) eq_refl),
    !(d_val_obj 6%nat 0x210a0 ltac:(lia) eq_refl), !(d_val_obj 7%nat 0x210c0 ltac:(lia) eq_refl),
    !(d_val_obj 8%nat 0x210e0 ltac:(lia) eq_refl), !(d_val_obj 9%nat 0x21100 ltac:(lia) eq_refl),
    !(d_val_obj 10%nat 0x20f80 ltac:(lia) eq_refl), !(d_val_obj 11%nat 0x20fc0 ltac:(lia) eq_refl),
    !(d_val_obj 12%nat 0x21180 ltac:(lia) eq_refl), !(d_val_obj 13%nat 0x21160 ltac:(lia) eq_refl),
    !(d_val_obj 14%nat 0x20fe0 ltac:(lia) eq_refl), !(d_val_obj 15%nat 0x21000 ltac:(lia) eq_refl),
    !(d_val_obj 16%nat 0x21020 ltac:(lia) eq_refl), !(d_val_obj 18%nat 0x21040 ltac:(lia) eq_refl),
    !(d_val_obj 17%nat 0x10370 ltac:(lia) eq_refl).
  repeat (split; [apply MK; vm_compute; reflexivity|]).
  split; [apply MKW; vm_compute; reflexivity | apply d_rom_b; vm_compute; reflexivity].
- unfold dimg_tj.
  rewrite !(d_val_obj 39%nat 0x21340 ltac:(lia) eq_refl), !(d_val_obj 40%nat 0x213c0 ltac:(lia) eq_refl),
    !(d_val_obj 41%nat 0x213e0 ltac:(lia) eq_refl), !(d_val_obj 42%nat 0x21360 ltac:(lia) eq_refl),
    !(d_val_obj 43%nat 0x21320 ltac:(lia) eq_refl), !(d_val_obj 44%nat 0x21300 ltac:(lia) eq_refl),
    !(d_val_obj 45%nat 0x212e0 ltac:(lia) eq_refl), !(d_val_obj 46%nat 0x21400 ltac:(lia) eq_refl),
    !(d_val_obj 47%nat 0x21480 ltac:(lia) eq_refl), !(d_val_obj 48%nat 0x214c0 ltac:(lia) eq_refl),
    !(d_val_obj 49%nat 0x21420 ltac:(lia) eq_refl), !(d_val_obj 50%nat 0x21440 ltac:(lia) eq_refl),
    !(d_val_obj 51%nat 0x21500 ltac:(lia) eq_refl), !(d_val_obj 52%nat 0x21520 ltac:(lia) eq_refl),
    !(d_val_obj 53%nat 0x214e0 ltac:(lia) eq_refl), !(d_val_obj 54%nat 0x21540 ltac:(lia) eq_refl),
    !(d_val_obj 55%nat 0x21560 ltac:(lia) eq_refl), !(d_val_obj 17%nat 0x10370 ltac:(lia) eq_refl).
  split.
  + unfold rbn_img.
    rewrite !(d_val_obj 26%nat 0xa0300 ltac:(lia) eq_refl), !(d_val_obj 27%nat 0x21220 ltac:(lia) eq_refl),
      !(d_val_obj 28%nat 0x21240 ltac:(lia) eq_refl), !(d_val_obj 29%nat 0x21260 ltac:(lia) eq_refl),
      !(d_val_obj 30%nat 0x21280 ltac:(lia) eq_refl).
    exists 0x211c0, 0x211e0, 0x21200.
    split; [reflexivity|].
    split; [exact (d_in_img_b 0xa0300 24 ltac:(vm_compute; reflexivity))|].
    split; [exact (proj1 (MKR 0xa0300 24 ltac:(vm_compute; reflexivity)))|].
    split; [apply MKW; vm_compute; reflexivity|].
    split; [apply MKW; vm_compute; reflexivity|].
    split; [apply MKW; vm_compute; reflexivity|].
    split; [apply MKS; vm_compute; reflexivity|].
    split; [apply MKS; vm_compute; reflexivity|].
    split; [apply MKS; vm_compute; reflexivity|].
    split; [apply MKS; vm_compute; reflexivity|].
    split; [apply MKL; vm_compute; reflexivity|].
    split; [apply MKL; vm_compute; reflexivity|].
    split; [apply MKL; vm_compute; reflexivity|].
    do 7 (split; [apply d_rbn_ro; vm_compute; reflexivity|]).
    apply d_rbn_ro; vm_compute; reflexivity.
  + repeat (split; [apply MK; vm_compute; reflexivity|]).
    split; [apply MKW; vm_compute; reflexivity | apply d_rom_b; vm_compute; reflexivity].
Qed.

End s.
