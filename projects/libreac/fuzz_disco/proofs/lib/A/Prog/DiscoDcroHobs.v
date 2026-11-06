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

Theorem dcro_hobs : dcro_hobs_stmt B.
Proof.
unfold dcro_hobs_stmt, dcro_of. intros LAWS DRO ly S W m md HAR HOK.
destruct DRO as (DRU & GM & HV).
assert (CTX : dro_ctx B ly S W m md).
{ unfold dro_ctx. split; [exact HAR|]. split; [exact HOK|]. split; [exact DRU|]. split; [exact GM | exact HV]. }
pose proof (d_word_b B ly S W m md CTX) as MKW.
pose proof (d_garr8_b B ly S W m md CTX) as MKG.
pose proof (d_rdok_b B ly S W m md CTX) as MKR.
unfold dimg_hobs, dimg_verdict.
rewrite !(d_val_obj 63%nat 66328 ltac:(lia) eq_refl), !(d_val_obj 64%nat 66504 ltac:(lia) eq_refl),
  !(d_val_obj 59%nat 656192 ltac:(lia) eq_refl), !(d_val_obj 60%nat 136768 ltac:(lia) eq_refl),
  !(d_val_obj 1%nat 656656 ltac:(lia) eq_refl).
repeat match goal with |- _ /\ _ => split end.
1-2, 8-10: apply MKW; vm_compute; reflexivity.
1-2, 10-13: apply d_rom_b; vm_compute; reflexivity.
- reflexivity.
- cbn [zseps zseps_from fst snd]. repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- exact (proj1 (MKR 656192 24 ltac:(vm_compute; reflexivity))).
- apply MKG; vm_compute; reflexivity.
- apply MKG; vm_compute; reflexivity.
- apply MKG; vm_compute; reflexivity.
- apply MKG; vm_compute; reflexivity.
Qed.

End s.
