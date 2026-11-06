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
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
Section h.
Variable B : asyms.

Definition dcro_of (Q : world SEGS -> (word -> option byte) -> Prop) : Prop :=
  AR_laws SEGS B -> d_ro_hyps B ->
  forall ly S W m md, AR SEGS B ly S W m md ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) m) -> Q W m.

Definition dcro_strs_stmt : Prop := dcro_of (fun W m => dimg_strs W m /\ dimg_tj W m).
Definition dcro_tjs_stmt : Prop := dcro_of (fun W m => rbn_img W m /\ tjson_scalar_img W m).
Definition dcro_ro_stmt : Prop := dcro_of (fun W m => dimg_ro W m /\ dimg_rates W m).
Definition dcro_hobs_stmt : Prop := dcro_of (fun W m => dimg_hobs W m /\ dimg_verdict W m).

Lemma dcro_compose :
  dcro_strs_stmt -> dcro_tjs_stmt -> dcro_ro_stmt -> dcro_hobs_stmt ->
  dimg_consts_of_ro_stmt B.
Proof.
intros HS HT HR HH LAWS DRO ly S W m md HAR HOK.
destruct (HS LAWS DRO ly S W m md HAR HOK) as [S1 S2].
destruct (HT LAWS DRO ly S W m md HAR HOK) as [T1 T2].
destruct (HR LAWS DRO ly S W m md HAR HOK) as [R1 R2].
destruct (HH LAWS DRO ly S W m md HAR HOK) as [H1 H2].
unfold dimg_consts. tauto.
Qed.

End h.
End f.
End d.
