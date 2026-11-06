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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1i DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacBoxName JsonScalar.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntryInv DiscoRo DiscoEntBodyStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoImg DiscoDcroParts DiscoDcroLib.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section s. Context {rc : YM05.RunCeil}. Context {SK : YI16.sink_head}.
Variable B : asyms.

Theorem dcro_tjs : dcro_tjs_stmt B.
Proof.
unfold dcro_tjs_stmt, dcro_of. intros LAWS DRO ly S W m md HAR HOK.
destruct DRO as (DRU & GM & HV).
assert (CTX : dro_ctx B ly S W m md).
{ unfold dro_ctx. split; [exact HAR|]. split; [exact HOK|]. split; [exact DRU|]. split; [exact GM | exact HV]. }
pose proof (d_tjstr_of B ly S W m md CTX) as MKT.
pose proof (d_word_b B ly S W m md CTX) as MKW.
pose proof (d_rbn_stem_of B ly S W m md CTX) as MKS.
pose proof (d_rbn_lit_of B ly S W m md CTX) as MKL.
pose proof (d_rdok_b B ly S W m md CTX) as MKR.
split.
- unfold rbn_img.
  rewrite !(d_val_obj 26%nat 0xa0300 ltac:(lia) eq_refl), !(d_val_obj 27%nat 0x21220 ltac:(lia) eq_refl),
    !(d_val_obj 28%nat 0x21240 ltac:(lia) eq_refl), !(d_val_obj 29%nat 0x21260 ltac:(lia) eq_refl),
    !(d_val_obj 30%nat 0x21280 ltac:(lia) eq_refl).
  exists 0x211c0, 0x211e0, 0x21200.
  split; [reflexivity|].
  split; [exact (d_in_img_b 0xa0300 24 ltac:(vm_compute; reflexivity))|].
  split; [exact (proj1 (MKR 0xa0300 24 ltac:(vm_compute; reflexivity)))|].
  do 3 (split; [apply MKW; vm_compute; reflexivity|]).
  do 4 (split; [apply MKS; vm_compute; reflexivity|]).
  do 3 (split; [apply MKL; vm_compute; reflexivity|]).
  do 7 (split; [apply d_rbn_ro; vm_compute; reflexivity|]).
  apply d_rbn_ro; vm_compute; reflexivity.
- unfold tjson_scalar_img.
  rewrite !(d_val_obj 20%nat 0xa02c0 ltac:(lia) eq_refl), !(d_val_obj 19%nat 0x21120 ltac:(lia) eq_refl).
  exists 0x21000, 0x21020, 0x21140.
  split; [reflexivity|].
  split; [exact (d_in_img_b 0xa02c0 24 ltac:(vm_compute; reflexivity))|].
  split; [exact (proj1 (MKR 0xa02c0 24 ltac:(vm_compute; reflexivity)))|].
  do 3 (split; [apply MKW; vm_compute; reflexivity|]).
  do 3 (split; [apply MKT; vm_compute; reflexivity|]).
  apply MKT; vm_compute; reflexivity.
Qed.

End s.
